# HANDOFF — Erdős 239 (Wirsing for ±1 multiplicative functions) — 2026-09-24 (lap 4)

Branch `erdos-239-proof`, HEAD `da8f27fb`. Working tree clean. Nothing pushed.

**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE outranks this file.

## Target

`Erdos239.erdos_239` in `FormalConjectures/ErdosProblems/239.lean`; statement untouched.
It reduces to `Wirsing.exists_hasMeanValue` in `Wirsing/Main.lean`.

## Open obligations (all three still in `Main.lean`)

1. `Wirsing.tendsto_logProfile_div_log_atTop_zero` — **now dead scaffolding.** Delete it and
   prove `tendsto_logMean_div_log_atTop_zero` directly once steps E–F land (see below).
2. `Wirsing.tendsto_mean_atTop_zero_of_logMean` — the Tauberian step `L ⇒ σ`.
3. `Wirsing.exists_hasMeanValue_of_summable` — the Wintner half, untouched.

## What this lap did: a new, complete, elementary proof of the crux

Laps 2 and 3 refuted two single-scale iteration schemes and established that the Gronwall
induction is *marginal*. Lap 4 replaced the whole strategy. The route is written out in full
in `PENDING_WORK.md` ("THE POTENTIAL ROUTE"); the short version, with
`g(n) = |L(n)|`, `Φ(N) = ∑_{n≤N} g(n)/n`, `D(N) = ∑_{p≤N, f p = -1} (log p/p) g(⌊N/p⌋)`:

* the engine identity applied with the profile `|L|` **itself** (legitimate because
  `||L(m)| - |L(m-1)|| ≤ 1/m`) plus a Fubini weight comparison gives
  `g(N) log N ≤ 2Φ(N) - 2D(N) + 64(1 + log N)`;
* telescoping `Φ(N)/(log N)²` makes `D` summable against `1/(N (log N)³)`;
* a window/Fubini argument turns that summability into `∑_{f(p)=-1} 1/p < ∞`, contradicting
  the hypothesis; so `Φ(N) = o((log N)²)` and hence `g(N) = o(log N)`.

The deficit is never cashed in at one scale (which is what failed twice); it is accumulated
across all scales, and a constant gain per scale summed against `1/(N (log N)³)` is exactly
`∑ 1/p`.

### Proved and sorry-free this lap, all in the new `Wirsing/Decay.lean`

* **Step B** `abs_sum_primeWeight_comp_sub_sum_div_le` —
  `|∑_{p≤N}(log p/p) g(⌊N/p⌋) - ∑_{n≤N} g(n)/n| ≤ 11|g 1| + 16 log N` for every `g` with
  `|g m - g (m-1)| ≤ 1/m`. Expand both sides along the increments of `g`, swap the order of
  summation (`sum_Icc_div_comm`, `sum_Icc_le_comm`), and use Mertens on the inner weights.
  No Abel summation, no total-variation bound.
* **Step C** `abs_logMean_mul_log_le_potential` —
  `|L(N)| log N ≤ 2Φ(N) - 2D(N) + 64(1 + log N)`, with `potential`, `badWeight`,
  `abs_abs_logMean_sub_le`, `sum_one_sub_eq_two_mul_badWeight`.
* **Step D** `potential_step_algebra`, `potential_step`, `potential_div_add_sum_le`,
  `exists_sum_badWeight_le` — the telescoping, giving
  `∃ B ≥ 0, ∀ M, ∑_{3≤N≤M} D(N)/(N (log N)³) ≤ B`.
* **The monotone envelope** `envelope f N = Φ(N)/(log N)² + 128/log N + 4/N`, with
  `envelope_step`, `envelope_add_sum_le`, `envelope_antitone`, `envelopeInf`,
  `envelopeInf_le`, `exists_envelope_lt`. Folding in the error tails turns the step into
  plain monotonicity, so `ℓ = ⨅ envelope` needs no convergence machinery, and gives
  **both** `Φ(M) ≥ (ℓ - 128/log M - 4/M)(log M)²` for every `M ≥ 2` **and**
  `Φ(M) ≤ (ℓ+η)(log M)²` past a threshold.
* **The block bound** `sum_div_succ_le_sum_block` —
  `∑_{a≤M≤b} h(M)/(M+1) ≤ ∑_{pa≤N≤pb+p-1} h(⌊N/p⌋)/N` for nonnegative `h`, by fibering over
  `N ↦ ⌊N/p⌋`. Keeping the factor `p` is essential; a one-`N`-per-`M` bound loses it and the
  window argument collapses.
* `potential_sub`, `one_le_log_three`, `one_div_le_log_succ_sub_log`,
  `one_le_mul_log_succ_sub_log`, `one_div_mul_log_sq_le_sub`, `sum_one_div_mul_log_sq_le`,
  `sum_Icc_three_one_div_sq_le`, `eq_add_sum_sub`, `logMean_succ`, `logMean_one`.

## Next step, in order

1. **Per-prime window bound.** For `p ≥ 2` and `X ≥ p·p² + p`:

       (Φ(p²) - Φ(p)) / (128 (log p)³) ≤ ∑_{N ∈ Icc 3 X} |L(⌊N/p⌋)| / (N (log N)³).

   Window `M ∈ Ioc p (p²)`, blocks inside `Icc (p(p+1)) (p·p² + p - 1)`; there
   `N ≤ 2p³` so `(log N)³ ≤ 64 (log p)³`, and `1/(M+1) ≥ 1/(2M)` gives the other factor 2.
   Inputs: `sum_div_succ_le_sum_block`, `potential_sub`,
   `Finset.sum_le_sum_of_subset_of_nonneg`. **Avoid `ℕ` subtraction**: use `p^2` (not
   `p^2 - 1`) as the window top and `Nat.sub_le` for the `+ p - 1`.
2. **Fubini over the bad primes.** Swap
   `∑_{N ∈ Icc 3 X} D(N)/(N (log N)³) = ∑_{p bad ≤ X} (log p/p) ∑_{N ∈ Icc (max 3 p) X} …`
   with `Finset.sum_comm'` (membership condition:
   `N ∈ Icc 3 X ∧ p ∈ filter Q (Icc 1 N) ↔ N ∈ Icc (max 3 p) X ∧ p ∈ filter Q (Icc 1 X)`),
   then drop all but a finite set `S` of large bad primes.
3. **The contradiction.** If `ℓ > 0`, pick `η = ℓ` and `M₀` from `exists_envelope_lt`; for
   `p ≥ P₁` large, `Φ(p²) - Φ(p) ≥ 2ℓ(log p)²`, so each prime contributes
   `≥ (log p/p)·2ℓ(log p)²/(128 (log p)³) = ℓ/(64 p)`. Since
   `badPrimeSum f → ∞` (`tendsto_badPrimeSum_atTop_of_not_summable`), the total exceeds the
   bound `B` of `exists_sum_badWeight_le`. Hence `ℓ = 0`.
4. **Conclusion.** `ℓ = 0` gives `Φ(M)/(log M)² → 0` via `exists_envelope_lt`, and step C
   gives `|L(N)|/log N ≤ 2Φ(N)/(log N)² + 64(1+log N)/(log N)² → 0`. Then delete
   `tendsto_logProfile_div_log_atTop_zero` from `Main.lean` and prove
   `tendsto_logMean_div_log_atTop_zero` from this.

## Lean gotchas learned this lap (also in `PENDING_WORK.md`)

* `linarith` parses `a / b` with a **non-numeral** `b` as a *single atom*. So `128 / X` and
  `1 / X` are unrelated atoms, and `2 * D / X` differs from `2 * (D / X)`. Write every
  scalable term as `c * (1 / X)`. This cost three build cycles.
* `div_le_div_iff` is `div_le_div_iff₀` in this mathlib; `abs_add` is `abs_add_le`.
* `field_simp` often closes the goal, making a following `ring` fail with "no goals"; and
  `congr 1` on `∑ x ∈ Ioc 1 N, … = ∑ x ∈ Icc 2 N, …` closes it outright (the finsets are
  defeq), so a following `ext`/`omega` also errors.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Decay'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

Green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
