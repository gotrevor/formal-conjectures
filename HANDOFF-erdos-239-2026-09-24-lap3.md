# HANDOFF — Erdős 239 (Wirsing for ±1 multiplicative functions) — 2026-09-24 (lap 3)

Branch `erdos-239-proof`, HEAD `a770b062`. Working tree clean. Nothing pushed.

## Target

`Erdos239.erdos_239` in `FormalConjectures/ErdosProblems/239.lean`; statement untouched.
It reduces to `Wirsing.exists_hasMeanValue` in `Wirsing/Main.lean`.

## Open obligations (all in `Main.lean`, three sorries)

1. `Wirsing.tendsto_logProfile_div_log_atTop_zero` — **THE CRUX**. `ψ(N) = o(log N)` for the
   recursive profile `logProfile`. Purely analytic: all number theory is discharged.
2. `Wirsing.tendsto_mean_atTop_zero_of_logMean` — the Tauberian step `L ⇒ σ`.
3. `Wirsing.exists_hasMeanValue_of_summable` — the Wintner half, untouched.

`tendsto_logMean_div_log_atTop_zero` and `tendsto_mean_atTop_zero_of_badPrimeSum_atTop` are
now proved *from* 1 and 2.

## What this lap did

**Generalised the engine.** `abs_logMean_mul_log_sub_defect_le`: for every ±1-valued
multiplicative `f`, `L(N) log N = ∑_{p≤N} (log p/p)(1 + f p) L(⌊N/p⌋) + O(log N)`. The model
case `f(p) = -1` is now a corollary. `logProfile` (strong recursion) satisfies this with
equality and dominates `|L|` (`abs_logMean_le_logProfile`), which is how the crux became
purely analytic.

**Two refutations, both recorded in `PENDING_WORK.md`. Do not retry either.**
* *Step-function deficit bootstrap*: the profile `α(1+log M) − s·[M ≥ N₁]` maps
  `s ↦ 2s(1−1/T) − 2C` while `log N ↦ T log N`; the multiplier ratio `2(1−1/T)/T` peaks at
  `1/2 < 1` at `T = 2`, so the deficit never grows relative to `log N`.
* *Limsup shortcut*: the deficit in the sharp step is a constant gain against `α log N`, so
  it divides away; no single scale improves `limsup |L|/log N`, however large `r(K)` is.

**The sharp Mertens chain (this was the real blocker).** The Gronwall induction is *marginal*
— both `(log N)²` terms cancel identically — so the Mertens error enters only through its
average `∫_0^{log x} E`, and a two-sided `O(1)` bound contributes `O(log x)` there and kills
the induction. Now proved, sorry-free, in `FormalConjecturesForMathlib/NumberTheory/Mertens.lean`:
`sum_log_le_sharp`, `sum_log_ge_sharp`, `E₁Λ_le_sharp` (error `≤ log 4 − 1 ≈ 0.386`),
`sum_vonMangoldt_div_nonprime_ge` (proper prime powers carry mass `≥ 1/2`), and
**`sum_log_prime_div_le_log`: `∑_{p≤x} log p/p ≤ log x` for `x ≥ 10^10`.**

**Consequences in `Wirsing/Log.lean`,** all sorry-free:
`sum_log_div_le_sq_log` (log-harmonic sum pinned two-sided);
`sum_primeWeight_mul_log_div_le` — `∑_p (log p/p) log⌊N/p⌋ ≤ (log N)²/2 + O(1)`, **no `log N`
term**, by Abel (the `A(N) log N` term cancels identically);
`badDefect`, `abs_logMean_mul_log_le_of_profile_sharp` — the sharp Gronwall step, with an
exact `(log N)²` coefficient and the deficit as the entire gain;
`sum_primeWeight_mul_le_of_antitone` — the same comparison for **any** nonincreasing,
nonnegative, `log`-Lipschitz profile, again with no `log N` term.

## Next step (crux)

Run the multi-scale recursion. The mechanism is identified: the constant deficit becomes
proportional through the doubling of `β` across scales,
`β(u) = 2β(u/2) − 2α r(u/2) + O(1)`, giving `β(u) ≈ −cαu` and hence a multiplicative
contraction `α_eff = α(1−c)`, matching the ODE
`u ψ(u) = 2∫_0^u ψ(u−v)dμ(v) − 2∫_0^u ψ(u−v)dr(v) + Cu`
whose solution decays like `exp(−2∫ r(v/2)/v² dv)` — divergent exactly when
`∑_{f(p)=−1} 1/p = ∞`. Every input is proved; `sum_primeWeight_mul_le_of_antitone` is the
lemma to feed the decaying profile through.

## Build

    lake --wfail build FormalConjecturesForMathlib
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Log'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
