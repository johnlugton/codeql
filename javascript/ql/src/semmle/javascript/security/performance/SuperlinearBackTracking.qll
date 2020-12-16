/**
 * Provides classes for working with regular expressions that can
 * perform backtracking in superlinear time.
 */

import javascript
import ReDoS

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

import OverlapsWithPrev // TODO:

module OverlapsWithPrev {
  // TODO: I only got 1 module, so just move to top-level.
  /**
   * TODO: Descrip is old.
   * A state in the product automaton.
   *
   * We lazily only construct those states that we are actually
   * going to need: `(q, q)` for every fork state `q`, and any
   * pair of states that can be reached from a pair that we have
   * already constructed. To cut down on the number of states,
   * we only represent states `(q1, q2)` where `q1` is lexicographically
   * no bigger than `q2`.
   *
   * States are only constructed if both states in the pair are
   * inside a repetition that might backtrack.
   */
  // The exponential variant has a q1 <= q2 <= q3 variant.
  // I can't do that here, because position is important (for optimization).
  // The states are not created equals.
  newtype TStateTuple =
    // starts at (prev, prev, next)
    MkStateTuple(State q1, State q2, State q3) {
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

  pragma[noinline]
  predicate isStateTuple(StateTuple p) {
    // TODO: Rename - reorginaize - and document the two-phase system.
    // Quick and dirty check that the goal might be reachable.
    exists(StateTuple start, State prev, State next | isFork(prev, next, _, _, _, _, _, _) |
      tupleDeltaTmp*(start) = p and
      tupleDeltaTmp*(p) = getAForkPair(prev, next)
    )
  }

  StateTuple tupleDeltaTmp(StateTuple s) { tupleDelta(s, result) }

  pragma[noinline]
  predicate tupleDelta(StateTuple q, StateTuple r) { stepTuples(q, _, _, _, r) }

  pragma[noinline]
  predicate tupleDeltaBackwards(StateTuple q, StateTuple r) {
    tupleDelta(r, q) and
    isStateTuple(q) and
    isStateTuple(r)
  }

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

  State getADeltaReachable(State s) { delta(s, _, result) }

  /**
   * Holds if `prev` and `next` are a pair of states that could be the beginning of a quadratic blowup.
   * TODO: Make bigger explanation in top of module. Paper: https://arxiv.org/pdf/1701.04045.pdf
   * Mention how the "start anywhere" is modeled by just having an any-transition from the start state to itself.
   * TODO: Consider detecting loops using the NFA. (in any case simplfy)
   */
  predicate isStartPair(State prev, State next) {
    prev != next and
    next.getRepr() instanceof InfiniteRepetitionQuantifier and
    getADeltaReachable*(prev) = next and
    (
      prev.getRepr() = any(InfiniteRepetitionQuantifier i)
      or
      epsilonSucc*(getRootState()) = prev
      or
      prev = Match(any(RegExpRoot root), 0)
    )
  }

  pragma[noopt]
  predicate isFork(
    State prev, State next, InputSymbol s1, InputSymbol s2, InputSymbol s3, State r1, State r2,
    State r3
  ) {
    isStartPair(prev, next) and
    exists(State q1, State q2, State q3 |
      q1 = epsilonSucc*(prev) and
      delta(q1, s1, r1) and
      q2 = epsilonSucc*(prev) and
      delta(q2, s2, r2) and
      q3 = epsilonSucc*(next) and
      delta(q3, s3, r3) and
      // TODO: This is duplicated. De-duplicate? Also not perfect. Consider doing some pre-compuation in another predicate?
      threeWayIntersect(s1, s2, s3)
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

  pragma[noinline]
  predicate threeWayIntersect(InputSymbol s1, InputSymbol s2, InputSymbol s3) {
    exists(getAnIntersectedChar(s1, s2, s3)) // TODO: Consider inlining this thing
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
      // TODO: Try others. Have some noinline predicate that computes 3-way intersect.
      threeWayIntersect(s1, s2, s3)
    ) and
    // Lots of pruning, to only consider relevant states.
    isRepeitionOrRoot(r1) and // TODO: Try to move this into step?
    stateInsideRepetition(r3) and
    getADeltaReachable+(r1) = r2 and
    getADeltaReachable+(r2) = r3 and
    canReachATarget(r3) and
    canReachABeginning(r1)
    //stateInsideBacktracking(r1) and // TODO:
    //stateInsideBacktracking(r2)
  }

  pragma[noinline]
  predicate canReachABeginning(State s) { getADeltaReachable+(s) = getABeginning() }

  pragma[noinline]
  predicate canReachATarget(State s) { getADeltaReachable+(s) = getATarget() }

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
      result = concretise(rest) + getAnIntersectedChar(s1, s2, s3)
    )
  }

  pragma[noinline]
  InputSymbol getAMatchingInputSymbol(string char) {
    result = getAnInputSymbolMatching(char) and
    char = CharacterClasses::getARelevantChar()
  }

  // TODO: Rename to threewayIntersect. Document that it is not perfect.
  pragma[noinline]
  string getAnIntersectedChar(InputSymbol s1, InputSymbol s2, InputSymbol s3) {
    // TODO: Try to do a first-phase, where I just check existence of intersections.
    result = intersect(s1, s2) and result = intersect(s2, s3)
    or
    result = intersect(s1, s3) and result = intersect(s2, s3)
    or
    result = intersect(s1, s2) and result = intersect(s1, s3)
  }

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
    State prev, State next, StateTuple r, StateTuple p, InputSymbol s1, InputSymbol s2,
    InputSymbol s3
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
}

/**
 * Holds if state `s` with pump string `pump` can cause polynomial backtracking.
 * This only holds if
 */
predicate superLiniearReDoSCandidate(State s, string pump) {
  OverlapsWithPrev::isPumpable(_, s, pump)
}

predicate polynimalReDoS(RegExpTerm t, string pump, State s, string prefixMsg, string msg) {
  hasReDoSResult(t, pump, s, prefixMsg) and
  exists(State prev |
    OverlapsWithPrev::isPumpable(prev, s, _) and
    msg =
      "Strings " + prefixMsg + "with many repetitions of '" + pump +
        "' can start matching anywhere after the start of the preceeding " + prev.getRepr()
  )
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
