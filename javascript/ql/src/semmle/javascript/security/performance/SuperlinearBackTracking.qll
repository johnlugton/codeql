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

  override predicate isRelevant(RegExpTerm term) { any() } // TODO:
}

/**
 * Gets any root (start) state of a regular expression.
 */
private State getRootState() { result = Match(any(RegExpRoot r), 0) }

module CanStartAnywhereNotUsedToDelete {
  /**
   * Holds if `s` is an infinite repetition that can start matching anywhere in the regular expression.
   * This causes quadratic runtime if there exists a rejecting suffix.
   */
  predicate canStartMatchingAnywhere(State s, string pump) {
    s.getRepr() instanceof InfiniteRepetitionQuantifier and
    epsilonSucc+(getRootState()) = s and
    pump = repetitionString(s.getRepr())
  }

  /**
   * Holds if `s` is the start state inside an infinite repeition.
   */
  private predicate isStartOfRepetition(State s) {
    s.getRepr() = any(InfiniteRepetitionQuantifier r).getChild(0)
  }

  /**
   * Holds if there exists a transition in the NFA from `a` to `b`.
   */
  private predicate delta(State a, State b) { delta(a, _, b) }

  /**
   * Gets the minimum length of a path from `q` to `r`,
   */
  private int distFromRepetitionStart(State q, State r) =
    shortestDistances(isStartOfRepetition/1, delta/2)(q, r, result)

  /**
   * Gets the shortest distance in the NFA from the beginning of the repetition `quantifier` to `s`.
   */
  private int distToQuantifier(InfiniteRepetitionQuantifier quantifier, State s) {
    exists(int loopLength |
      loopLength = distFromRepetitionStart(Match(quantifier.getChild(0), 0), Match(quantifier, 0)) and
      result = loopLength - distFromRepetitionStart(Match(quantifier.getChild(0), 0), s)
    ) and
    result >= 0
  }

  /**
   * Holds if the shortest distance from the beginning of `quantifier` to `s` is `dist`,
   * and `str` matches the regular expression from the beginning of `quantifier` to `s`.
   * Is used to construct a string matching the inside of a repetition one step at a time.
   */
  private predicate repetitionString(
    InfiniteRepetitionQuantifier quantifier, State s, int dist, string str
  ) {
    // base case
    s.getRepr() = quantifier.getChild(0) and
    str = "" and
    dist = distToQuantifier(quantifier, s)
    or
    // recursive case
    exists(string prevStr, State prev |
      prev =
        // Select a previous by an arbibary measure
        min(State prevCan, Location loc |
          delta(prevCan, _, s) and
          distToQuantifier(quantifier, prevCan) - 1 = dist and
          dist = distToQuantifier(quantifier, s) and
          loc = prevCan.getRepr().getLocation()
        |
          prevCan
          order by
            loc.getStartLine(), loc.getStartColumn(), loc.getEndLine(), loc.getEndColumn()
        ) and
      repetitionString(quantifier, prev, dist + 1, prevStr) and
      (
        delta(prev, Epsilon(), s) and str = prevStr
        or
        exists(string char |
          char =
            min(string c |
              c = CharacterClasses::getARelevantChar() and
              delta(prev, getAnInputSymbolMatching(c), s)
            ) and
          str = prevStr + char
        )
      )
    )
  }

  /**
   * Gets a string that matches the inner regular expression of the repeition `quantifier`.
   */
  private string repetitionString(InfiniteRepetitionQuantifier quantifier) {
    repetitionString(quantifier, Match(quantifier, 0), 0, result)
  }
}

import OverlapsWithPrev // TODO:

module OverlapsWithPrev {
  /**
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
  newtype TStatePair =
    MkStatePair(State q1, State q2) {
      isFork(q1, q2, _, _, _, _)
      or
      step(_, _, _, q1, q2)
    }

  class StatePair extends TStatePair {
    State q1;
    State q2;

    StatePair() { this = MkStatePair(q1, q2) }

    string toString() { result = "(" + q1 + ", " + q2 + ")" }

    State getLeft() { result = q1 }

    State getRight() { result = q2 }
  }

  predicate isStatePair(StatePair p) { any() }

  predicate delta2(StatePair q, StatePair r) { step(q, _, _, r) }

  /**
   * Gets the minimum length of a path from `q` to `r` in the
   * product automaton.
   */
  int statePairDist(StatePair q, StatePair r) =
    shortestDistances(isStatePair/1, delta2/2)(q, r, result)

  State getADeltaReachable(State s) { delta(s, _, result) }

  /**
   * Holds if `prev` and `next` are a pair of states that could be the beginning of a quadratic blowup.
   * TODO: Make bigger explanation in top of module. Paper: https://arxiv.org/pdf/1701.04045.pdf
   * Mention how the "start anywhere" is modeled by just having an any-transition from the start state to itself.
   * TODO: Consider detecting loops using the NFA.
   */
  predicate isStartPair(State prev, State next) {
    prev != next and
    next.getRepr() instanceof InfiniteRepetitionQuantifier and
    getADeltaReachable*(prev) = next and
    (
      prev.getRepr() = any(InfiniteRepetitionQuantifier i).getChild(0)
      or
      epsilonSucc*(getRootState()) = prev
      or
      prev = Match(any(RegExpRoot root), 0)
    )
  }

  pragma[noopt]
  predicate isFork(State prev, State next, InputSymbol s1, InputSymbol s2, State r1, State r2) {
    isStartPair(prev, next) and
    exists(State q1, State q2 |
      q1 = epsilonSucc*(prev) and
      delta(q1, s1, r1) and
      q2 = epsilonSucc*(next) and
      delta(q2, s2, r2) and
      exists(intersect(s1, s2))
    |
      s1 != s2
      or
      r1 != r2
      or
      r1 = r2 and q1 != q2
    )
  }

  /**
   * Holds if there are transitions from the components of `q` to the corresponding
   * components of `r` labelled with `s1` and `s2`, respectively.
   */
  predicate step(StatePair q, InputSymbol s1, InputSymbol s2, StatePair r) {
    exists(State r1, State r2 | step(q, s1, s2, r1, r2) and r = MkStatePair(r1, r2))
  }

  /**
   * Holds if there are transitions from the components of `q` to `r1` and `r2`
   * labelled with `s1` and `s2`, respectively.
   *
   * We only consider transitions where the resulting states `(r1, r2)` are both
   * inside a repetition that might backtrack.
   */
  pragma[noopt]
  predicate step(StatePair q, InputSymbol s1, InputSymbol s2, State r1, State r2) {
    exists(State q1, State q2 | q.getLeft() = q1 and q.getRight() = q2 |
      deltaClosed(q1, s1, r1) and
      deltaClosed(q2, s2, r2) and
      // use noopt to force the join on `intersect` to happen last.
      exists(intersect(s1, s2))
    ) //and
    //stateInsideBacktracking(r1) and
    //stateInsideBacktracking(r2)
  }

  private newtype TTrace =
    Nil() or
    Step(InputSymbol s1, InputSymbol s2, TTrace t) {
      exists(StatePair p |
        isReachableFromFork(_, _, p, t, _) and
        step(p, s1, s2, _)
      )
      or
      t = Nil() and isFork(_, _, s1, s2, _, _)
    }

  /**
   * A list of pairs of input symbols that describe a path in the product automaton
   * starting from some fork state.
   */
  class Trace extends TTrace {
    string toString() {
      this = Nil() and result = "Nil()"
      or
      exists(InputSymbol s1, InputSymbol s2, Trace t | this = Step(s1, s2, t) |
        result = "Step(" + s1 + ", " + s2 + ", " + t + ")"
      )
    }
  }

  /**
   * Gets a string corresponding to the trace `t`.
   */
  string concretise(Trace t) {
    t = Nil() and result = ""
    or
    exists(InputSymbol s1, InputSymbol s2, Trace rest | t = Step(s1, s2, rest) |
      result = concretise(rest) + intersect(s1, s2)
    )
  }

  /**
   * Holds if `r` is reachable from `(fork, fork)` under input `w`, and there is
   * a path from `r` back to `(fork, fork)` with `rem` steps.
   */
  predicate isReachableFromFork(State prev, State next, StatePair r, Trace w, int rem) {
    // base case
    exists(InputSymbol s1, InputSymbol s2, State q1, State q2 |
      isFork(prev, next, s1, s2, q1, q2) and
      r = MkStatePair(q1, q2) and
      w = Step(s1, s2, Nil()) and
      rem = statePairDist(r, MkStatePair(next, next))
    )
    or
    // recursive case
    exists(StatePair p, Trace v, InputSymbol s1, InputSymbol s2 |
      isReachableFromFork(prev, next, p, v, rem + 1) and
      step(p, s1, s2, r) and
      w = Step(s1, s2, v) and
      rem >= statePairDist(r, MkStatePair(next, next))
    )
  }

  /**
   * Gets a state in the product automaton from which `(fork, fork)` is
   * reachable in zero or more epsilon transitions.
   */
  StatePair getAForkPair(State prev, State next) {
    isStartPair(prev, next) and
    result = MkStatePair(epsilonPred*(next), epsilonPred*(next))
  }

  /**
   * Gets a state that can be reached from start `s` consuming all
   * chars in `w` any number of times followed by the first `i+1` characters of `w`.
   * TODO: Pumps the prev to get pi_1
   */
  private State processPrev(State s, string w, int i) {
    isPumpableCandidate(s, _, w) and
    exists(State prev |
      i = 0 and prev = s
      or
      prev = processPrev(s, w, i - 1)
      or
      // repeat until fixpoint
      i = 0 and
      prev = processPrev(s, w, w.length() - 1)
    |
      deltaClosed(prev, getAnInputSymbolMatching(w.charAt(i)), result)
    )
  }

  predicate isPumpableCandidate(State prev, State next, string w) {
    exists(StatePair q, Trace t |
      isReachableFromFork(prev, next, q, t, _) and
      q = getAForkPair(prev, next) and
      w = concretise(t)
    )
  }

  predicate isPumpable(State prev, State next, string w) {
    isPumpableCandidate(prev, next, w) and
    epsilonSucc*(processPrev(prev, w, w.length() - 1)) = prev
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
