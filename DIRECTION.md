# DIRECTION — Erdős 239

## CURRENT DIRECTIVE (set lap 4, 2026-09-24; altitude laps only may rewrite)

**Objective.** Prove `Wirsing.tendsto_logMean_div_log_atTop_zero` — `L(N) = o(log N)` when
`∑_{f(p)=-1} 1/p = ∞` — by the **potential / Gronwall-in-`Φ`** route set out below.  This is
the crux of Erdős 239.

**Mandated next move.** Build `FormalConjectures/ErdosProblems/Wirsing/Decay.lean` implementing
the five steps A–F of the route (see `PENDING_WORK.md`, "The potential route").  Step B (the
Fubini comparison `∑_p (log p/p) g(⌊N/p⌋) = ∑_n g(n)/n + O(log N)`) is the first and the
most load-bearing; do it first.

**Forbidden drift.**
* Do **not** resume the `logProfile` recursion, the step-function deficit bootstrap, or the
  limsup shortcut.  All three are refuted or superseded; `logProfile` is now dead scaffolding.
* Do **not** start the Wintner half (`exists_hasMeanValue_of_summable`) until the crux closes.
* No new Mertens work: the sharp chain in `FormalConjecturesForMathlib/NumberTheory/Mertens.lean`
  is sufficient for the whole route.

**Why.** The route is a *complete elementary proof*, checked end to end on paper (lap 4), whose
every analytic input is already formalised in this repo.  It replaces the marginal single-scale
Gronwall induction — which two laps proved cannot close — by a second-order argument: the
telescoping of `Φ(N)/(log N)²` makes the bad-prime deficit *summable*, and a Fubini swap turns
that summability into `∑_{f(p)=-1} 1/p < ∞`.  The multiplicative gain the previous route was
hunting for appears automatically, because the weight `1/(log N)³` converts a *constant* gain
per scale into a *convergent* series across scales.

### Directive history
* lap 4 (2026-09-24) — switch the crux attack from the `logProfile` multi-scale recursion to
  the potential route `Φ(N) = ∑_{n≤N} |L(n)|/n`.

---

## Standing charter

Prove `Erdos239.erdos_239` (`FormalConjectures/ErdosProblems/239.lean`) — Wirsing's mean value
theorem for `±1`-valued multiplicative functions — without changing its statement, docstring,
`answer(True)` or attributes.  All helper mathematics lives in
`FormalConjectures/ErdosProblems/Wirsing/` and `FormalConjecturesForMathlib/`.

The two halves:
1. **divergent case** (`∑_p (1-f p)/p = ∞ ⇒ mean 0`) — the crux, currently open;
2. **convergent case** (Wintner) — elementary, untouched.
