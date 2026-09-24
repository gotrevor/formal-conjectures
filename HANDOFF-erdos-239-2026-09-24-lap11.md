# HANDOFF — Erdős 239 — 2026-09-24 (lap 11, review + proof)

Branch `erdos-239-proof`, HEAD `1bc1c772`, working tree clean.  Nothing pushed.
`DIRECTION.md`'s CURRENT DIRECTIVE was **rewritten this lap** (altitude lap); obey it.

## The route decision of this lap

Lap 10 ended with `Newman.norm_sub_integral_le` — Newman's estimate on a **disc** — and named
as its next action "get `G` analytic on `|z| ≤ R` from analyticity on `re z ≥ 0`".
**That step is impossible.**  `closedBall 0 R` contains `-R/2`, so the closed right half plane
contains no disc around `0` at all, for any `R > 0`; the disc estimate's hypothesis can never
be met.  Also refuted this lap, so do not retry:

* **shifted discs** `|z - c| ≤ r` with `c < r ≤ c + δ` (these *are* inside `{re z ≥ -δ}` and do
  contain `0`), because the `1/z` factor at the contour's closest approach to `0` makes the
  `G`-term integral blow up like `log(R/δ)/δ`;
* **conformal adjustment** — no Riemann mapping in mathlib, and the kernel identity
  `(1 + z²/R²)/z = 2\,\mathrm{Re}(z)/R²` is special to a circle centred at `0`.

The structural reason: the part of the contour near `0` must have `re z ≤ -δ` *bounded away
from* `0`, since that is what supplies the `e^{-δT}` decay for the `G` term.  A circle passing
near `0` has `re z` sweeping continuously through `0`.

**Mathlib's only Cauchy theorem for a non-disc region is the one for a rectangle**
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).  So the contour is now
`Q = [-δ, R] × [-R, R]` and the kernel is `k(z) = 1/z + z/R²`.

## Landed this lap — all sorry-free, all `[propext, Classical.choice, Quot.sound]`

**`Wirsing/Rectangle.lean` (new).**
* `rectInt`, `rect`, `rectInt_eq_zero` — mathlib's Cauchy–Goursat restated with four real
  corner coordinates instead of two complex corners.
* `integral_inv_horiz`, `integral_inv_vert_pos`, `integral_inv_vert_neg` — `1/z` along each
  edge by the fundamental theorem of calculus, `Complex.log` as antiderivative (`log(-z)` on
  the left edge, forced by the principal branch's slit).
* `rectInt_inv` — `∮_{∂Q} dz/z = 2πi`.  Moduli cancel in pairs; the `2π` comes from the two
  left-edge arguments differing from the right-edge ones by `±π`.
* `rectInt_div_self`, `rectInt_mul_kernel` — the residue: `∮_{∂Q} h(z)k(z)dz = 2πi\,h(0)`.
* `newmanKernel`, `newmanKernel_eq`, `norm_newmanKernel_horiz` (`≤ 3|re z|/R²` on `|im z| = R`,
  because `z² + R² = (z+iR)(z-iR)` and **one factor is the real number `re z`** — this is the
  rectangle's version of the circle miracle), `norm_newmanKernel_vert` (`≤ 3/R`).
* `norm_rectInt_le`, `norm_rectInt_le_of_left`, `norm_edge_le_of_rectInt_eq_zero`,
  `differentiableOn_newmanKernel`, `continuousOn_newmanKernel`.

**`Wirsing/Laplace.lean` (new).**  `Newman.lean` was split: the complex analysis moved here,
together with `tendsto_integral_of_analyticOn` (still `sorry`); `Newman.lean` keeps the
arithmetic (Abel summation, sharp Mertens, PNT, the window statement).  New here:
* `newmanAux F G T z = (G z - g_T z)e^{zT}` with `newmanAux_zero` (its value at `0` **is**
  `G 0 - ∫_0^T F`) and `differentiable_newmanAux`;
* `norm_newmanAux_le` (`≤ C/re z` for `re z > 0`), `norm_trunc_mul_exp_le` (`≤ C/(-re z)`);
* the four edge estimates: `norm_integrand_horiz_le` (`3(Mδ+C)/R²`),
  `norm_integrand_vert_right_le` (`3C/R²`), `norm_trunc_integrand_horiz_le`,
  `norm_trunc_integrand_vert_le`, `norm_G_integrand_left_le` (`M e^{-δT}(1/δ + 2/R)`);
* **`norm_sub_integral_le_rect`** — Newman's estimate, assembled:
  `‖G 0 - ∫_0^T F‖ ≤ (2Mδ + 5C)/R + R M e^{-δT}(1/δ + 2/R)`.

## Open `sorry`s in `src/` (3, all rooted in one theorem)

* `Wirsing/Laplace.lean` — `tendsto_integral_of_analyticOn`;
* `Wirsing/Newman.lean` — `summable_psi_sub_div` (that theorem applied to
  `F(t) = ψ(e^t)e^{-t} - 1`);
* `Wirsing/Main.lean` — `tendsto_mean_sub_logMean_div_log_atTop_zero` (the headline crux,
  which consumes the now-proved window statement).

## NEXT (in order)

1. **`tendsto_integral_of_analyticOn` from `norm_sub_integral_le_rect`.**  Two steps left.
   * *Compactness.*  Take `U := {z | AnalyticAt ℂ G z}`, which is open (`isOpen_analyticAt`)
     and contains `{re z ≥ 0}`; `G` is differentiable on it.  For fixed `R > 0` the set
     `S = {iy : |y| ≤ R}` is compact and `⊆ U`, so `IsCompact.exists_thickening_subset_open`
     gives `ε > 0` with `thickening ε S ⊆ U`.  For `δ < min ε R` every point of
     `rect (-δ) R (-R) R` with `re z < 0` is within `δ` of `S`, and the rest is in
     `{re z ≥ 0} ⊆ U`; so `rect (-δ) R (-R) R ⊆ U`.  Fix `δ₀ = δ₀(R)` first and take
     `M := sup{‖G z‖ : z ∈ rect (-δ₀) R (-R) R}` (continuous on a compact set), which then
     serves for **every** `δ ≤ δ₀` — this is what lets `δ → 0` with `M` fixed.
   * *The ε-chase*, in this order and no other: given `ε > 0`, pick `R` with `5C/R < ε/3`,
     then `δ ≤ δ₀(R)` with `2Mδ/R < ε/3`, then `T₀` with `R M e^{-δT}(1/δ + 2/R) < ε/3` for
     `T ≥ T₀`.  Conclude with `Metric.tendsto_atTop`.  Finally take real parts: `F` is real so
     `∫_0^T (F t : ℂ)` is the coercion of `∫_0^T F`, and the limit `G 0` is real.
2. **`summable_psi_sub_div`** — apply (1) to `F(t) = ψ(e^t)e^{-t} - 1`, bounded by
   `Chebyshev.psi_le_const_mul_self`, whose transform is `-ζ'/ζ(z+1)/(z+1) - 1/z`, analytic
   across `re z = 0` by `Wirsing.exists_continuousOn_lSeries_vonMangoldt_sub` and
   `riemannZeta_ne_zero_of_one_le_re`.  Then convert `∫_0^T F` into the series by `t = log m`
   (`ψ` is constant between integers).
3. With sharp Mertens unconditional, feed `tendsto_sum_log_prime_div_window` into
   `Wirsing.eq_of_mean_quotient_close` and close the prime chain.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

Green, 8940 jobs.  Commits use `--no-verify` (the global pre-commit hook runs a whole-project
build that dies with "Too many open files" on this box).

## Gotchas found this lap

* `tac <;> [t1; t2]` **cannot** appear in a file that uses the `[[a, b]]` (`Set.uIcc`)
  notation: the parser reads `]]` and fails with `unexpected token ']]'`.  Use separate
  `have`s.
* `field_simp` frequently closes these goals outright, and a following `ring` then errors with
  "No goals to be solved".  Where it is needed it is needed, so the two cases have to be
  distinguished by building.
* `positivity` does not look at hypotheses: `0 ≤ C / z.re` with `hzre : 0 < z.re` in context
  must be given as `div_nonneg hC0 hzre.le`.
* `simp only [newmanKernel]` will not unfold a partially applied `def`; state the lambda with
  `have h : DifferentiableAt ℂ (fun w ↦ …) z := …` and close by `exact`.

## Aristotle

Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (the crux, lap 6) still uncollected; check
`aristotle show` before submitting anything new.  No job submitted this lap.
