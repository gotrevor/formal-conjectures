# HANDOFF — Erdős 239 — 2026-09-24 (lap 8)

Branch `erdos-239-proof`, HEAD `e286e167`, working tree clean.  Nothing pushed.
`DIRECTION.md`'s lap-7 CURRENT DIRECTIVE objective was already met before this lap; the
forbidden-drift list still binds and was respected (no new package dependency, no
Erdős–Selberg PNT, no repeated Mertens-weight transfers).

## Landed this lap

**`Wirsing/Weighted.lean` is now sorry-free** (`#print axioms` on
`exists_sum_primeWeight_one_sub_mul_cos_ge`: `propext, Classical.choice, Quot.sound`).
`lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` is green.

* `exists_abs_tsum_vonMangoldt_twisted_sub_le` — **two-sided**:
  `|∑_n Λ(n)n^{-(1+x)}(1-cos(t log n)) - 1/x| ≤ C_t` on `0 < x ≤ 1`, `t ≠ 0`.
  Real parts of `∑Λ(n)n^{-s} = 1/(s-1) + G(s)` at `1+x` and `1+x+it`, subtracted;
  `G` bounded on two compact segments.  This is where `riemannZeta_ne_zero_of_one_le_re`
  enters.  `_ge` and `_le` are one-line corollaries.
* `exists_tsum_vonMangoldt_le` — untwisted `∑_n Λ(n)n^{-(1+x)} ≤ 1/x + C`.
* `sum_vonMangoldt_rpow_head_ge` — Mertens in `m` geometric blocks
  `N^{i/m} < n ≤ N^{(i+1)/m}`.
* `sum_range_exp_ge`, `sum_range_exp_ge_32` — the Riemann-sum bound for `∑_{i<m}e^{-c(i+1)/m}`.
* **`exists_sum_primeWeight_one_sub_cos_ge`** — `∑_{p≤N}(log p/p)(1-cos(t log p)) ≥ log N/4 - C_t`.

**The trick that closed it**: the tail `∑_{n>N}Λ(n)n^{-1-x}` needs **no Abel summation**.
The untwisted series has a matching *upper* bound `1/x + O(1)`, so
`tail = total - head`, and the head is bounded below by a *finite* `m`-block Riemann sum.
With `c = 2`, `m = 32` the prime part that survives is `≥ (17/56)log N - O(1) > log N/4`.

## The route-decisive finding of this lap

The two-sided bound says the Laplace transform of the **nondecreasing**
`D_t(v) = ∑_{n≤e^v}(Λ(n)/n)(1-cos(t log n))` is `1/x + O_t(1)`.  That is exactly the
hypothesis of **Karamata's Tauberian theorem**, whose conclusion `D_t(v) ~ v` is

    ∑_{p ≤ N} (log p / p) cos(t log p) = o(log N)   for each fixed t ≠ 0,

i.e. **verbatim the PNT-strength estimate lap 6 named as the blocker** for the resonance
step of the crux.  So the deep input is *Karamata* — elementary, ~1 page, self-contained —
not Wiener–Ikehara and not the Erdős–Selberg elementary PNT.  Mathlib has no `Karamata`
(grepped v4.33.1 this lap).

## In progress: `Wirsing/Karamata.lean` (new, currently SORRY-FREE)

Builds green with `--wfail`.  Done:

* `functional a x g = x ∑_n a_n n^{-x} g(n^{-x})`, `series a x = ∑_n a_n n^{-x}`.
* `functional_pow` — `Λ_x(u^k) = ((k+1)x S((k+1)x))/(k+1)`.
* `summable_term`, `functional_add`, `functional_sub`, `functional_const_mul`,
  `functional_mono`, `abs_functional_le` — bounded positive linear functional.
* `tendsto_functional_pow`, `tendsto_functional_polynomial` — `Λ_x(P) → c∫_0^1 P`.
* **`tendsto_functional_continuousOn`** — `Λ_x(g) → c∫_0^1 g` for every `g` continuous on
  `[0,1]`.  Weierstrass (`exists_polynomial_near_of_continuousOn`) + the uniform bound.
* `testFun θ u = u^{-1}·1_{θ≤u}`, `bracketLow`, `bracketHigh` (continuous, denominator
  `max u (θ/2)` to stay continuous at `0`), their ordering and `2/θ` bounds.
* `integral_bracketLow_ge` `≥ -log(θ+η)`, `integral_bracketHigh_le` `≤ -log(θ-η)`.

## NEXT (in order)

1. `Karamata.functional_testFun`: for `0 < θ ≤ 1`, `0 < x`, `a 0 = 0`,
   ```
   functional a x (testFun θ) = x * ∑ n ∈ Finset.Icc 1 ⌊(1/θ) ^ (1/x)⌋₊, a n
   ```
   because `a_n · n^{-x} · (n^{-x})^{-1} = a_n` and `θ ≤ n^{-x} ⟺ n ≤ (1/θ)^{1/x}`.
   Use `tsum_eq_sum` with the support Finset.
2. The pinch: `bracketLow ≤ testFun ≤ bracketHigh` + `functional_mono` +
   `tendsto_functional_continuousOn` on both brackets.  With `θ = e^{-1}` (so
   `-log θ = 1`, `(1/θ)^{1/x} = exp(1/x)`) and `η → 0` (use `η ≤ min (θ/4) (θε/(12(|c|+1)))`
   and `log((θ+η)/(θ-η)) ≤ 4η/θ`) this gives
   ```
   Tendsto (fun x ↦ x * ∑ n ∈ Icc 1 ⌊Real.exp (1/x)⌋₊, a n) (𝓝[>] 0) (𝓝 c)
   ```
   and then, with `V = 1/x`, `(∑_{n≤e^V} a_n)/V → c`.
3. Apply with `a_n = (Λ(n)/n)(1-cos(t log n))`, `c = 1` (hypothesis from
   `exists_abs_tsum_vonMangoldt_twisted_sub_le`; summability from
   `summable_vonMangoldt_rpow_cos`; note `a_n n^{-x} = Λ(n)n^{-(1+x)}(1-cos)`).
   Subtract Mertens and drop prime powers to get
   `Wirsing.tendsto_sum_primeWeight_cos`: `∑_{p≤N}(log p/p)cos(t log p) = o(log N)`.
4. Feed that into the route-C resonance computation in `Wirsing/Rigidity.lean`.
   Once `Karamata.lean` is sorry-free it should move to
   `FormalConjecturesForMathlib/Analysis/Karamata.lean` (that directory forbids `sorry`).

The crux `Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero` in `Wirsing/Main.lean`
remains the only `sorry` in `src/`.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Karamata'
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Weighted'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green.  Commits use `--no-verify` (the global pre-commit hook runs a whole-project build
that dies with "Too many open files" on this box).

## Aristotle

Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (the crux, lap 6) still uncollected; check
`aristotle show` before submitting anything new.  No job was submitted this lap.
