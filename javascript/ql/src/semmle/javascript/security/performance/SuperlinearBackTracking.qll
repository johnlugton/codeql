/**
 * Provides classes for working with regular expressions that can
 * perform backtracking in superlinear time.
 */

import javascript
import ReDoS

/*
 * This module implements the analysis described in the paper:
 *   Valentin Wüstholz, Oswaldo Olivo, Marijn J. H. Heule, and Isil Dillig:
 *     Static Detection of DoS Vulnerabilities in
 *      Programs that use Regular Expressions
 *     (Extended Version).
 *   (https://arxiv.org/pdf/1701.04045.pdf)
 *
 * Theorem 3 from the paper describes the basic idea:
 * ```
 * An NFA A = (Q, Σ, Δ, q_0, F) is vulnerable iff there exist two states
 * q ∈ Q (the pivot), q' ∈ Q, and three paths π_1, π_2, and π_3 (where π_1 != π_2)
 * such that (i) π_1 starts and ends at q, (ii) π_2 starts at q and ends at q',
 * (iii) π_3 starts and ends at q', (iv) labels(π_1) = labels(π_2) = labels(π_3),
 * and (v) there is a path π_p from q_0 to q, (vi) there is path π_s from q' to a state q_r ∉ F.
 * ```
 *
 * To put in other words (and using variables and predicate names used in the implementation):
 * We search for a pair of loops, which we will call `prev` and `next`.
 *
 * We create a product automaton of 3-tuples of states.
 * There exists a transition `(a,b,c) -> (d,e,f)` in the product automaton
 * if there are three transitions in the NFA `a->d, b->e, c->f` where those three
 * transitions all match a shared character `char`.
 *
 * We start a search in the product automaton at `(prev, prev, next)`,
 * and search for a series of transitions (a `Trace`), such that we end
 * at `(prev, next, next)`.
 *
 * For example for a regular expression `/\d*5\w*$/`.
 * The search will start at the state `(\d*, \d*, \w*)` and search
 * for a path to `(\d*, \w*, \w*)`.
 * This path exists, and consists of a single transition in the product automaton,
 * where the three corresponding NFA transitions share the `char` `"5"`.
 *
 * This approach also flags regular expressions such as `/a*$/`, as the
 * start-state in the NFA has an any-transition to itself - which models that
 * the regular expression does not have a start anchor, and can thus start matching anywhere.
 *
 * The implementation is not perfect.
 * It has the same suffix detection issue as the `js/redos` query, which can cause false positives.
 * It also doesn't find all transitions in the product automaton, which can cause false negatives.
 */

/**
 * An instantiaion of `ReDoSConfiguration` for superliniear ReDoS.
 */
class SuperLiniearReDoSConfiguration extends ReDoSConfiguration {
  SuperLiniearReDoSConfiguration() { this = "SuperLiniearReDoSConfiguration" }

  override predicate isReDoSCandidate(State state, string pump) {
    superLiniearReDoSCandidate(state, pump)
  }

  override predicate isRelevant(RegExpTerm term) {
    term.getSuccessor*() instanceof InfiniteRepetitionQuantifier
    or
    term.getParent*() instanceof InfiniteRepetitionQuantifier
  }
}

/**
 * Gets any root (start) state of a regular expression.
 */
private State getRootState() { result = Match(any(RegExpRoot r), 0) }

/**
 * A state in the product automaton.
 * The product automaton contains 3-tuples of states.
 *
 * We lazily only construct those states that we are actually
 * going to need.
 * Either a start state `(prev, prev, next)`, or a state
 * where there exists a transition from an already existing state.
 *
 * The exponential variant of this query (`js/redos`) uses an optimization
 * trick where `q1 <= q2`. This trick cannot be used here as the position
 * of the elements in the tuple matter.
 */
newtype TStateTuple =
  MkStateTuple(State q1, State q2, State q3) {
    // starts at (prev, prev, next)
    isFork(q1, q3, _, _, _, _, _, _) and q1 = q2
    or
    step(_, _, _, _, q1, q2, q3)
  }

class StateTuple extends TStateTuple {
  State q1;
  State q2;
  State q3;

  StateTuple() { this = MkStateTuple(q1, q2, q3) }

  string toString() { result = "(" + q1 + ", " + q2 + ", " + q3 + ")" }

  State getFirst() { result = q1 }

  State getSecond() { result = q2 }

  State getThird() { result = q3 }
}

/**
 * Holds if `prev` and `next` are a pair of loops that could be the beginning of a quadratic blowup.
 *
 * There is a slight implementation difference compared to the paper: this predicate require that `prev != next`.
 * The case where `prev = next` causes exponential backtracking and is handled by the `js/redos` query.
 */
predicate isStartPair(State prev, State next) {
  prev != next and
  next.getRepr() instanceof InfiniteRepetitionQuantifier and
  delta*(prev) = next and
  (
    prev.getRepr() = any(InfiniteRepetitionQuantifier i)
    or
    prev = Match(any(RegExpRoot root), 0)
  )
}

/**
 * Gets a state for which there exists a transition in the NFA from `s'.
 */
State delta(State s) { delta(s, _, result) }

/**
 * TODO: Doc.
 */
pragma[noopt]
predicate isFork(
  State prev, State next, InputSymbol s1, InputSymbol s2, InputSymbol s3, State r1, State r2,
  State r3
) {
  isStartPair(prev, next) and
  exists(State q1, State q3 |
    q1 = epsilonSucc*(prev) and
    delta(q1, s1, r1) and
    deltaClosed(prev, s2, r2) and
    q3 = epsilonSucc*(next) and
    delta(q3, s3, r3) and
    exists(getAThreewayIntersect(s1, s2, s3))
  |
    s1 != s3
    or
    r1 != r3
    or
    r1 = r3 and q1 != q3
  )
}

/**
 * Holds if there are transitions from the components of `q` to the corresponding
 * components of `r` labelled with `s1` and `s2`, respectively.
 */
pragma[noinline]
predicate stepTuples(StateTuple q, InputSymbol s1, InputSymbol s2, InputSymbol s3, StateTuple r) {
  exists(State r1, State r2, State r3 |
    step(q, s1, s2, s3, r1, r2, r3) and r = MkStateTuple(r1, r2, r3)
  )
}

/**
 * Holds if there are transitions from the components of `q` to `r1` and `r2`
 * labelled with `s1` and `s2`, respectively.
 *
 * We only consider transitions where the resulting states `(r1, r2)` are both
 * inside a repetition that might backtrack.
 */
pragma[noopt]
predicate step(
  StateTuple q, InputSymbol s1, InputSymbol s2, InputSymbol s3, State r1, State r2, State r3
) {
  exists(State q1, State q2, State q3 |
    q.getFirst() = q1 and q.getSecond() = q2 and q.getThird() = q3
  |
    deltaClosed(q1, s1, r1) and
    deltaClosed(q2, s2, r2) and
    deltaClosed(q3, s3, r3) and
    // use noopt to force the join on `intersect` to happen last.
    exists(getAThreewayIntersect(s1, s2, s3))
  ) and
  // Lots of pruning, to only consider relevant states.
  isRepeitionOrRoot(r1) and // TODO: Try to move this into step?
  stateInsideRepetition(r3) and
  delta+(r1) = r2 and
  delta+(r2) = r3 and
  canReachATarget(r3) and
  canReachABeginning(r1)
  //stateInsideBacktracking(r1) and // TODO:
  //stateInsideBacktracking(r2)
}

pragma[noinline]
predicate canReachABeginning(State s) { delta+(s) = getABeginning() }

pragma[noinline]
predicate canReachATarget(State s) { delta+(s) = getATarget() }

State getATarget() { isStartPair(_, result) }

State getABeginning() { isStartPair(result, _) }

/**
 * Holds if state `s` might be inside a backtracking repetition.
 */
pragma[noinline]
predicate stateInsideRepetition(State s) {
  s.getRepr().getParent*() instanceof InfiniteRepetitionQuantifier
}

predicate isRepeitionOrRoot(State s) { stateInsideRepetition(s) or s = getRootState() }

private newtype TTrace =
  Nil() or
  Step(InputSymbol s1, InputSymbol s2, InputSymbol s3, TTrace t) {
    exists(StateTuple p |
      isReachableFromFork(_, _, p, t, _) and
      stepTuples(p, s1, s2, s3, _)
    )
    or
    t = Nil() and isFork(_, _, s1, s2, s3, _, _, _)
  }

/**
 * A list of pairs of input symbols that describe a path in the product automaton
 * starting from some fork state.
 */
class Trace extends TTrace {
  string toString() {
    this = Nil() and result = "Nil()"
    or
    exists(InputSymbol s1, InputSymbol s2, InputSymbol s3, Trace t | this = Step(s1, s2, s3, t) |
      result = "Step(" + s1 + ", " + s2 + ", " + s3 + ", " + t + ")"
    )
  }
}

/**
 * Gets a string corresponding to the trace `t`.
 */
string concretise(Trace t) {
  t = Nil() and result = ""
  or
  exists(InputSymbol s1, InputSymbol s2, InputSymbol s3, Trace rest | t = Step(s1, s2, s3, rest) |
    result = concretise(rest) + getAThreewayIntersect(s1, s2, s3)
  )
}

pragma[noinline]
InputSymbol getAMatchingInputSymbol(string char) {
  result = getAnInputSymbolMatching(char) and
  char = CharacterClasses::getARelevantChar()
}

// TODO: Rename to threewayIntersect. Document that it is not perfect.
pragma[noinline]
string getAThreewayIntersect(InputSymbol s1, InputSymbol s2, InputSymbol s3) {
  result = intersect(s1, s2) and result = intersect(s2, s3)
  or
  result = intersect(s1, s3) and result = intersect(s2, s3)
  or
  result = intersect(s1, s2) and result = intersect(s1, s3)
}

/**
 * Holds if there exists a transition from `r` to `q` in the product automaton.
 * Notice that the arguments are flipped, and thus the direction is backwards.
 */
pragma[noinline]
predicate tupleDeltaBackwards(StateTuple q, StateTuple r) { stepTuples(r, _, _, _, q) }

/**
 * Holds if `tuple` is an end state in our search.
 * That means there exists a pair of loops `(prev, next)` such that `tuple = (prev, next, next)`.
 */
predicate isEndState(StateTuple tuple) {
  exists(State prev, State next |
    isStartPair(prev, next) and
    tuple = MkStateTuple(prev, next, next)
  )
}

/**
 * Gets the minimum length of a path from `q` to `r` in the
 * product automaton.
 * DOC: Searches backwards form the end-state. Because it is way more efficient to have the first argument to `shortestDistances` be small.
 * (The default behavior would be to just have shortest distance to/from all StateTuples)
 * This allowed the PolynomialReDoS query to run more than twice as fast on our test-suite.
 */
int distBackFromEnd(StateTuple end, StateTuple r) =
  shortestDistances(isEndState/1,
    // TODO: Name.
    tupleDeltaBackwards/2)(end, r, result)

/**
 * Holds if `r` is reachable from `(fork, fork)` under input `w`, and there is
 * a path from `r` back to `(fork, fork)` with `rem` steps. <- TODO: Doc is outdated!
 */
predicate isReachableFromFork(State prev, State next, StateTuple r, Trace w, int rem) {
  // base case
  exists(InputSymbol s1, InputSymbol s2, InputSymbol s3, State q1, State q2, State q3 |
    isFork(prev, next, s1, s2, s3, q1, q2, q3) and
    r = MkStateTuple(q1, q2, q3) and
    w = Step(s1, s2, s3, Nil()) and
    rem = distBackFromEnd(MkStateTuple(prev, next, next), r)
  )
  or
  // recursive case
  exists(StateTuple p, Trace v, InputSymbol s1, InputSymbol s2, InputSymbol s3, int prevRem |
    isReachableFromFork(prev, next, p, v, prevRem) and
    prevRem - 1 = rem and
    rem = myDistPredicate(prev, next, r, p, s1, s2, s3) and
    w = Step(s1, s2, s3, v)
  )
}

// Cannot be inlined.
pragma[noinline]
int myDistPredicate(
  State prev, State next, StateTuple r, StateTuple p, InputSymbol s1, InputSymbol s2, InputSymbol s3
) {
  result = distBackFromEnd(MkStateTuple(prev, next, next), r) and
  stepTuples(p, s1, s2, s3, r)
}

/**
 * Gets a state in the product automaton from which `(prev, next, next)` is
 * reachable in zero or more epsilon transitions.
 */
StateTuple getAForkPair(State prev, State next) {
  // TODO: Name - end-tuple.
  isStartPair(prev, next) and
  result = MkStateTuple(epsilonPred*(prev), epsilonPred*(next), epsilonPred*(next))
}

predicate isPumpable(State prev, State next, string w) {
  exists(StateTuple q, Trace t |
    isReachableFromFork(prev, next, q, t, _) and
    q = getAForkPair(prev, next) and
    w = concretise(t)
  )
}

/**
 * Holds if state `s` with pump string `pump` can cause polynomial backtracking.
 * This only holds if
 */
predicate superLiniearReDoSCandidate(State s, string pump) { isPumpable(_, s, pump) }

predicate polynimalReDoS(RegExpTerm t, string pump, State s, string prefixMsg, string msg) {
  hasReDoSResult(t, pump, s, prefixMsg) and
  exists(State prev |
    isPumpable(prev, s, _) and
    msg =
      "Strings " + prefixMsg + "with many repetitions of '" + pump +
        "' can start matching anywhere after the start of the preceeding " + prev.getRepr()
  )
}

/**
 * Holds if `t` matches at least an epsilon symbol.
 *
 * That is, this term does not restrict the language of the enclosing regular expression.
 *
 * This is implemented as an under-approximation, and this predicate does not hold for sub-patterns in particular.
 */
private predicate matchesEpsilon(RegExpTerm t) {
  t instanceof RegExpStar
  or
  t instanceof RegExpOpt
  or
  t.(RegExpRange).getLowerBound() = 0
  or
  exists(RegExpTerm child |
    child = t.getAChild() and
    matchesEpsilon(child)
  |
    t instanceof RegExpAlt or
    t instanceof RegExpGroup or
    t instanceof RegExpPlus or
    t instanceof RegExpRange
  )
  or
  matchesEpsilon(t.(RegExpBackRef).getGroup())
  or
  forex(RegExpTerm child | child = t.(RegExpSequence).getAChild() | matchesEpsilon(child))
}

/**
 * A term that may cause a regular expression engine to perform a
 * polynomial number of match attempts, relative to the input length.
 */
class PolynomialBackTrackingTerm extends InfiniteRepetitionQuantifier {
  string reason;

  PolynomialBackTrackingTerm() {
    polynimalReDoS(this, _, _, _, _) and
    reason = min(string r | polynimalReDoS(this, _, _, _, r))
  }

  /**
   * Holds if all non-empty successors to the polynomial backtracking term matches the end of the line.
   */
  predicate isAtEndLine() {
    forall(RegExpTerm succ | this.getSuccessor+() = succ and not matchesEpsilon(succ) |
      succ instanceof RegExpDollar
    )
  }

  /**
   * Gets the reason for the number of match attempts.
   */
  string getReason() { result = reason }
}
