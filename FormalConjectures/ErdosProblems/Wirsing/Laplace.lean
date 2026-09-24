/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil
public import FormalConjectures.ErdosProblems.Wirsing.Rectangle

/-!
# Newman's analytic theorem

The Tauberian input to the Prime Number Theorem: a bounded, locally integrable
`F : [0,\infty) \to \mathbb{R}` whose Laplace transform
`G(z) = \int_0^\infty F(t)e^{-zt}\,dt`, a priori analytic on `\mathrm{Re}\,z > 0`, continues
analytically to the closed half plane `\mathrm{Re}\,z \ge 0`, has a convergent improper
integral, with `\int_0^\infty F = G(0)`.

This file holds the complex analysis; `Newman.lean` holds the arithmetic that consumes it.

**The contour is a rectangle, not a circle.**  Newman and Zagier integrate
`(G(z) - g_T(z))e^{zT}(1 + z^2/R^2)/z` over the boundary of
`\{|z| \le R\} \cap \{\mathrm{Re}\,z > -\delta\}`.  A closed disc cannot be used instead:
`closedBall 0 R` contains `-R/2`, so the closed right half plane — all the hypothesis gives —
contains no disc around `0` at all.  Nor can the indentation be dispensed with: the part of
the contour that passes near `0` must have `\mathrm{Re}\,z \le -\delta` *bounded away from*
`0`, since that is what supplies the factor `e^{-\delta T} \to 0` for the `G` term, and a
circle through a neighbourhood of `0` has `\mathrm{Re}\,z` sweeping continuously through `0`.
Mathlib's only Cauchy theorem for a non-disc region is the one for a rectangle, so the
contour is the rectangle `Q = [-\delta, R] \times [-R, R]`, and the kernel is
`k(z) = 1/z + z/R^2`, the same one in a different guise.

The estimates are the same as on the circle:

* right edge `\mathrm{Re}\,z = R`: `\|k\| \le (1+\sqrt2)/R` and
  `\|G - g_T\|e^{RT} \le C/R`, so the edge contributes `O(C/R)`;
* top and bottom `\mathrm{Im}\,z = \pm R`: `R^2 + z^2 = x(x \pm 2iR)` gives
  `\|k\| \le \sqrt5|x|/R^2` — the same cancellation of `x` against `Ce^{-xT}/x` that makes
  the circle work — so these contribute `O(C/R) + O((M+C)\delta/R^2)`;
* left edge `\mathrm{Re}\,z = -\delta`: the `G` term carries `e^{-\delta T}`, and the `g_T`
  term, being entire, is deformed by a second application of Cauchy's theorem onto the three
  outer edges of `Q' = [-R, -\delta] \times [-R, R]` (which misses `0`), where it is again
  `O(C/R)`.

The limits are taken in the order `T \to \infty`, then `\delta \to 0`, then `R \to \infty`.

The circle lemmas below (`Newman.kernel_eq` through `Newman.norm_sub_integral_le`) are kept:
they are sorry-free, and the bounds that do not mention the contour
(`Newman.norm_integral_Ioi_le`, `Newman.norm_integral_Ioc_le`,
`Newman.integral_Ioi_sub_integral_Ioc`, `Newman.differentiable_truncLaplace`) are exactly
what the rectangle argument uses too.

*References:*
- [Ne80] Newman, D. J., Simple analytic proof of the prime number theorem.
  Amer. Math. Monthly 87 (1980), 693-696.
- [Za97] Zagier, D., Newman's short proof of the prime number theorem.
  Amer. Math. Monthly 104 (1997), 705-708.
-/

@[expose] public section

open Filter

open scoped Topology Interval

namespace Newman

/-! ### The Newman kernel -/

/--
**The Newman kernel identity.**  On the circle `|z| = R` the kernel
`(1 + z^2/R^2)/z` is *real*, and equals `2\,\mathrm{Re}(z)/R^2`.

This one line is the whole miracle of Newman's proof.  On the right-hand arc the tail
`G(z) - g_T(z)` is `O(Ce^{-xT}/x)` with `x = \mathrm{Re}(z) > 0`, while the kernel times
`e^{zT}` has modulus `2xe^{xT}/R^2`; the `x` and the exponentials cancel exactly and the
product is `2C/R^2`, uniformly in `T`.  Without the factor `1 + z^2/R^2` the kernel would be
`1/R` and the estimate would fail.
-/
@[category API, AMS 30]
theorem kernel_eq {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    (1 + z ^ 2 / (R : ℂ) ^ 2) / z = 2 * (z.re : ℂ) / (R : ℂ) ^ 2 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hRne : ((R : ℂ)) ≠ 0 := by simpa using ne_of_gt hR
  have hR2 : ((R : ℂ)) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj]
    norm_cast
    rw [← hz, Complex.normSq_eq_norm_sq]
  have hadd : z + (starRingEnd ℂ) z = 2 * (z.re : ℂ) := by
    have h := Complex.add_conj z
    push_cast at h
    linear_combination h
  have hkey : ((R : ℂ)) ^ 2 + z ^ 2 = 2 * (z.re : ℂ) * z := by
    rw [hR2]; linear_combination z * hadd
  field_simp
  linear_combination hkey

/-- The modulus of the Newman kernel on `|z| = R` is `2|\mathrm{Re}\,z|/R^2`. -/
@[category API, AMS 30]
theorem norm_kernel {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    ‖(1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ = 2 * |z.re| / R ^ 2 := by
  rw [kernel_eq hR hz]
  rw [norm_div, norm_mul]
  simp [abs_of_pos hR]

/-! ### The Laplace tail on the right-hand arc -/

/-- `\int_T^\infty e^{-bt}\,dt = e^{-bT}/b` for `b > 0`. -/
@[category API, AMS 26]
theorem integral_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in Set.Ioi T, Real.exp (-b * t) = Real.exp (-b * T) / b := by
  have hderiv : ∀ x ∈ Set.Ioi T,
      HasDerivAt (fun t : ℝ ↦ -Real.exp (-b * t) / b) (Real.exp (-b * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul (-b)).exp).neg.div_const b
    simpa [mul_comm, mul_div_assoc, hb.ne'] using h
  have hcont : ContinuousWithinAt (fun t : ℝ ↦ -Real.exp (-b * t) / b) (Set.Ici T) T := by
    fun_prop
  have hlim : Filter.Tendsto (fun t : ℝ ↦ -Real.exp (-b * t) / b) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ ↦ Real.exp (-b * t)) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using (h1.neg.div_const b)
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (exp_neg_integrableOn_Ioi T hb) hlim
  rw [this]
  ring

/--
**The Laplace tail bound.**  If `|F| \le C` then for `\mathrm{Re}\,z = x > 0`
$$\Bigl\|\int_T^\infty F(t)e^{-zt}\,dt\Bigr\| \le \frac{Ce^{-xT}}{x}.$$

Paired with `Newman.norm_kernel` this is what makes the right-hand arc contribute `O(C/R)`.
-/
@[category API, AMS 30]
theorem norm_integral_Ioi_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ}
    (hz : 0 < z.re) (T : ℝ) :
    ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * T) / z.re := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hbound : ∀ t : ℝ, ‖(F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * Real.exp (-z.re * t))
      (Set.Ioi T) := (exp_neg_integrableOn_Ioi T hz).const_mul C
  calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Set.Ioi T, C * Real.exp (-z.re * t) :=
        MeasureTheory.norm_integral_le_of_norm_le hgint
          (Filter.Eventually.of_forall fun t ↦ hbound t)
    _ = C * Real.exp (-z.re * T) / z.re := by
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hz T]
        ring

/--
The Laplace integrand is integrable on `(0,\infty)` when `\mathrm{Re}\,z > 0`: it is
dominated by `Ce^{-xt}`.
-/
@[category API, AMS 30]
theorem integrableOn_laplace {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {z : ℂ} (hz : 0 < z.re) {a : ℝ} :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-z * (t : ℂ))) (Set.Ioi a) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi a)) := by
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hFi.aestronglyMeasurable.restrict))
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' ((exp_neg_integrableOn_Ioi a hz).const_mul C) hmeas ?_
  filter_upwards with t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    show (-z * (t : ℂ)).re = -z.re * t by simp]
  exact mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le

/--
**The tail identity.**  For `\mathrm{Re}\,z > 0` the Laplace transform minus its truncation
at `T` is exactly the tail:
$$\int_0^\infty F(t)e^{-zt}\,dt - \int_0^T F(t)e^{-zt}\,dt = \int_T^\infty F(t)e^{-zt}\,dt .$$

This is what turns `Newman.norm_integral_Ioi_le` into a bound on `G - g_T` on the right-hand
arc, and so feeds `Newman.norm_tail_mul_kernel_le`.
-/
@[category API, AMS 30]
theorem integral_Ioi_sub_integral_Ioc {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
        - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))
      = ∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
  set h : ℝ → ℂ := fun t ↦ (F t : ℂ) * Complex.exp (-z * (t : ℂ)) with hh
  have hIoi : MeasureTheory.IntegrableOn h (Set.Ioi T) := integrableOn_laplace hFb hFi hz
  have hIoc : MeasureTheory.IntegrableOn h (Set.Ioc (0 : ℝ) T) :=
    (integrableOn_laplace hFb hFi hz (a := 0)).mono_set Set.Ioc_subset_Ioi_self
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) :=
    Set.Ioc_disjoint_Ioi le_rfl
  have hunion : Set.Ioc (0 : ℝ) T ∪ Set.Ioi T = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hT
  have := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  rw [hunion] at this
  rw [this]
  ring

/--
**The Newman balance.**  On the right-hand arc the tail and the kernel multiply to `2C/R^2`,
uniformly in `T`.  Integrating over the semicircle of length `\pi R` and dividing by `2\pi`
gives the `C/R` bound that drives the whole proof.
-/
@[category API, AMS 30]
theorem norm_tail_mul_kernel_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ} {R T : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hzre : 0 < z.re) :
    ‖(∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have htail := norm_integral_Ioi_le hFb hzre T
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_mul, norm_mul, hexp, norm_kernel hR hz, abs_of_pos hzre]
  have hprod : (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) = C / z.re := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  have hstep : ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
      Real.exp (z.re * T) ≤ C / z.re := by
    calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ * Real.exp (z.re * T)
        ≤ (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) :=
          mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
      _ = C / z.re := hprod
  have hfin : (C / z.re) * (2 * z.re / R ^ 2) = 2 * C / R ^ 2 := by
    field_simp
  calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ * Real.exp (z.re * T) *
        (2 * z.re / R ^ 2)
      ≤ (C / z.re) * (2 * z.re / R ^ 2) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = 2 * C / R ^ 2 := hfin

/-! ### The truncated transform on the left-hand arc -/

/-- `\int_0^T e^{bt}\,dt = (e^{bT}-1)/b` for `b > 0`. -/
@[category API, AMS 26]
theorem integral_exp_mul_uIoc {b : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.exp (b * t) = (Real.exp (b * T) - 1) / b := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun t : ℝ ↦ Real.exp (b * t) / b) (Real.exp (b * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul b).exp).div_const b
    simpa [mul_comm, hb.ne'] using h
  have hint : IntervalIntegrable (fun x : ℝ ↦ Real.exp (b * x)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  ring

/--
**The truncated transform on the left.**  The entire function
`g_T(z) = \int_0^T F(t)e^{-zt}\,dt` satisfies, for `\mathrm{Re}\,z = x < 0`,
$$\|g_T(z)\| \le \frac{Ce^{-xT}}{-x}.$$

This is the mirror of `Newman.norm_integral_Ioi_le`, and it is why the left half of Newman's
contour contributes the same `O(C/R)`: `g_T` is entire, so its contour there may be deformed
to the left semicircle, where the very same balance applies.
-/
@[category API, AMS 30]
theorem norm_integral_Ioc_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ}
    (hz : z.re < 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * T) / (-z.re) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  set b := -z.re with hb
  have hbpos : 0 < b := by simpa [hb] using hz
  have hbound : ∀ t : ℝ, ‖(F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ ≤ C * Real.exp (b * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = b * t := by simp [hb]
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * Real.exp (b * t))
      (Set.Ioc (0 : ℝ) T) := by
    apply Continuous.integrableOn_Ioc
    fun_prop
  have hval : ∫ t in Set.Ioc (0 : ℝ) T, C * Real.exp (b * t)
      = C * ((Real.exp (b * T) - 1) / b) := by
    rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_const_mul,
      integral_exp_mul_uIoc hbpos T]
  calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, C * Real.exp (b * t) :=
        MeasureTheory.norm_integral_le_of_norm_le hgint
          (Filter.Eventually.of_forall fun t ↦ hbound t)
    _ = C * ((Real.exp (b * T) - 1) / b) := hval
    _ ≤ C * Real.exp (b * T) / b := by
        have h1 : C * ((Real.exp (b * T) - 1) / b) = (C * (Real.exp (b * T) - 1)) / b := by
          ring
        rw [h1, div_le_div_iff_of_pos_right hbpos]
        nlinarith [hC0]

/--
**The Newman balance on the left.**  Exactly the same `2C/R^2`, uniformly in `T`.

Together with `Newman.norm_tail_mul_kernel_le` this bounds both semicircles of the contour by
`C/R` after integration, which is the whole quantitative content of
`Newman.tendsto_integral_of_analyticOn`; what is left is the Cauchy bookkeeping and the
dominated-convergence step for the analytic continuation on `\mathrm{Re}\,z \le 0`.
-/
@[category API, AMS 30]
theorem norm_trunc_mul_kernel_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ} {R T : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hzre : z.re < 0) (hT : 0 ≤ T) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hbpos : 0 < -z.re := by linarith
  have htr := norm_integral_Ioc_le hFb hzre hT
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_mul, norm_mul, hexp, norm_kernel hR hz, abs_of_neg hzre]
  have hprod : (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) = C / (-z.re) := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  have hstep : ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
      Real.exp (z.re * T) ≤ C / (-z.re) := by
    calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
          Real.exp (z.re * T)
        ≤ (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) :=
          mul_le_mul_of_nonneg_right htr (Real.exp_pos _).le
      _ = C / (-z.re) := hprod
  have hzne : z.re ≠ 0 := ne_of_lt hzre
  have hfin : (C / (-z.re)) * (2 * -z.re / R ^ 2) = 2 * C / R ^ 2 := by
    field_simp
  calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
        Real.exp (z.re * T) * (2 * -z.re / R ^ 2)
      ≤ (C / (-z.re)) * (2 * -z.re / R ^ 2) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = 2 * C / R ^ 2 := hfin

/-! ### The two closed arcs -/

/-- On the imaginary axis the Newman kernel vanishes. -/
@[category API, AMS 30]
theorem kernel_eq_zero_of_re_eq_zero {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R)
    (hzre : z.re = 0) : (1 + z ^ 2 / (R : ℂ) ^ 2) / z = 0 := by
  rw [kernel_eq hR hz, hzre]
  simp

/--
**The right closed arc.**  On `|z| = R`, `\mathrm{Re}\,z \ge 0`,
$$\bigl\|(G(z) - g_T(z))e^{zT}\tfrac{1 + z^2/R^2}{z}\bigr\| \le \frac{2C}{R^2}.$$

For `\mathrm{Re}\,z > 0` this is `Newman.integral_Ioi_sub_integral_Ioc` followed by
`Newman.norm_tail_mul_kernel_le`; on the imaginary axis the kernel vanishes
(`Newman.kernel_eq_zero_of_re_eq_zero`), so the bound holds there for free.  Closing the arc
at `\mathrm{Re}\,z = 0` is what makes the contour split into two *closed* arcs, with no
measure-zero bookkeeping.
-/
@[category API, AMS 30]
theorem norm_sub_trunc_mul_kernel_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {z : ℂ} {R T : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) (hzre : 0 ≤ z.re) (hT : 0 ≤ T) :
    ‖(G z - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  rcases eq_or_lt_of_le hzre with hzero | hpos
  · rw [kernel_eq_zero_of_re_eq_zero hR hz hzero.symm, mul_zero, norm_zero]
    positivity
  · rw [hGeq z hpos, integral_Ioi_sub_integral_Ioc hFb hFi hpos hT]
    exact norm_tail_mul_kernel_le hFb hR hz hpos

/--
**The left closed arc.**  On `|z| = R`, `\mathrm{Re}\,z \le 0`,
`\|g_T(z)e^{zT}(1 + z^2/R^2)/z\| \le 2C/R^2`.

`Newman.norm_trunc_mul_kernel_le` with the imaginary axis added, again because the kernel
vanishes there.  Note that `g_T` is entire, so unlike Zagier's presentation no deformation of
the left contour is needed.
-/
@[category API, AMS 30]
theorem norm_trunc_mul_kernel_le' {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ} {R T : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hzre : z.re ≤ 0) (hT : 0 ≤ T) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  rcases eq_or_lt_of_le hzre with hzero | hneg
  · rw [kernel_eq_zero_of_re_eq_zero hR hz hzero, mul_zero, norm_zero]
    positivity
  · exact norm_trunc_mul_kernel_le hFb hR hz hneg hT

/-- For `x \le 0` and `T > 0`, `(-x)e^{xT} \le 1/T`: the decay beats the linear factor. -/
@[category API, AMS 26]
theorem neg_mul_exp_mul_le {x T : ℝ} (hx : x ≤ 0) (hT : 0 < T) :
    (-x) * Real.exp (x * T) ≤ 1 / T := by
  set y : ℝ := -x with hy
  have hy0 : 0 ≤ y := by simp [hy]; linarith
  have hpos : 0 < Real.exp (y * T) := Real.exp_pos _
  have key : y * T ≤ Real.exp (y * T) := by
    linarith [Real.add_one_le_exp (y * T)]
  rw [show x * T = -(y * T) by rw [hy]; ring, Real.exp_neg, le_div_iff₀ hT,
    inv_eq_one_div, mul_one_div, div_mul_eq_mul_div, div_le_one hpos]
  exact key

/--
**The uniform bound on the whole circle.**  If `\|G\| \le M` on `|z| = R` then for every
`T > 0` and every `z` with `|z| = R`,
$$\bigl\|(G(z) - g_T(z))e^{zT}\tfrac{1 + z^2/R^2}{z}\bigr\|
   \le \frac{2C}{R^2} + \frac{2M}{R^2 T} .$$

This is the estimate that makes Newman's proof go through with **no contour split and no
dominated convergence**.  On the right arc it is `Newman.norm_sub_trunc_mul_kernel_le`.  On
the left arc one splits `G - g_T`; the `g_T` part is `Newman.norm_trunc_mul_kernel_le'`, and
the `G` part is `M e^{xT}\cdot 2|x|/R^2` with `x = \mathrm{Re}\,z < 0`, where the kernel's
own factor `|x|` is exactly what the exponential decay can absorb:
`(-x)e^{xT} \le 1/T` uniformly in `x` (`Newman.neg_mul_exp_mul_le`).  Without the factor
`1 + z^2/R^2` the kernel would be `1/R` with no `|x|`, and the left arc would not tend to
`0`.

Integrating over the circle and dividing by `2\pi` gives
`|G(0) - g_T(0)| \le 2C/R + 2M/(RT)`, whence the theorem on letting `T \to \infty` and then
`R \to \infty`.
-/
@[category API, AMS 30]
theorem norm_sub_trunc_mul_kernel_le_circle {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {M : ℝ} {z : ℂ} {R T : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) (hT : 0 < T)
    (hM : ‖G z‖ ≤ M) :
    ‖(G z - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 + 2 * M / (R ^ 2 * T) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hextra : 0 ≤ 2 * M / (R ^ 2 * T) := by positivity
  rcases le_or_gt 0 z.re with hzre | hzre
  · have := norm_sub_trunc_mul_kernel_le hFb hFi hGeq hR hz hzre hT.le
    linarith
  · -- the left arc: split `G - g_T`
    set g : ℂ := ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)) with hgdef
    set K : ℂ := (1 + z ^ 2 / (R : ℂ) ^ 2) / z with hK
    have hsplit : (G z - g) * Complex.exp (z * (T : ℂ)) * K
        = G z * Complex.exp (z * (T : ℂ)) * K - g * Complex.exp (z * (T : ℂ)) * K := by
      ring
    have hgpart : ‖g * Complex.exp (z * (T : ℂ)) * K‖ ≤ 2 * C / R ^ 2 :=
      norm_trunc_mul_kernel_le' hFb hR hz hzre.le hT.le
    have hGpart : ‖G z * Complex.exp (z * (T : ℂ)) * K‖ ≤ 2 * M / (R ^ 2 * T) := by
      have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
        rw [Complex.norm_exp]; congr 1; simp
      rw [norm_mul, norm_mul, hexp, hK, norm_kernel hR hz, abs_of_neg hzre]
      have hdecay : (-z.re) * Real.exp (z.re * T) ≤ 1 / T := neg_mul_exp_mul_le hzre.le hT
      have hnegre : (0 : ℝ) < -z.re := by linarith
      have hnn : (0 : ℝ) ≤ 2 * -z.re / R ^ 2 := by positivity
      have hstep : ‖G z‖ * Real.exp (z.re * T) * (2 * -z.re / R ^ 2)
          ≤ M * ((-z.re) * Real.exp (z.re * T)) * (2 / R ^ 2) := by
        have h1 : ‖G z‖ * Real.exp (z.re * T) * (2 * -z.re / R ^ 2)
            = (‖G z‖ * ((-z.re) * Real.exp (z.re * T))) * (2 / R ^ 2) := by ring
        rw [h1]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right hM ?_
        exact mul_nonneg hnegre.le (Real.exp_pos _).le
      refine hstep.trans ?_
      have h2 : M * ((-z.re) * Real.exp (z.re * T)) * (2 / R ^ 2)
          ≤ M * (1 / T) * (2 / R ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hM0) ?_
        positivity
      refine h2.trans (le_of_eq ?_)
      field_simp
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    linarith

/-! ### The Cauchy value of the Newman kernel -/

open Metric in
/--
**The Cauchy step of Newman's proof.**  For `h` analytic on the closed disc `|z| \le R`,
$$\frac{1}{2\pi i}\oint_{|z| = R} h(z)\frac{1 + z^2/R^2}{z}\,dz = h(0).$$

The extra factor `1 + z^2/R^2` is `1` at the origin, so it does not change the residue; its
whole purpose is the boundary identity `Newman.kernel_eq`, which makes the kernel `O(1/R^2)`
times `|\mathrm{Re}\,z|` on the circle.  This is the piece of
`Newman.tendsto_integral_of_analyticOn` that mathlib's Cauchy integral formula supplies
directly; what is still missing there is only the *indented* contour needed because the
Laplace transform `G` is analytic on `\mathrm{Re}\,z \ge 0` and not on the full disc.
-/
@[category API, AMS 30]
theorem two_pi_I_inv_circleIntegral_kernel {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (closedBall (0 : ℂ) R)) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ z in C((0 : ℂ), R), h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)) = h 0 := by
  have hRne : ((R : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hR
  set f : ℂ → ℂ := fun z ↦ h z * (1 + z ^ 2 / (R : ℂ) ^ 2) with hf
  have hpoly : Differentiable ℂ fun z : ℂ ↦ 1 + z ^ 2 / (R : ℂ) ^ 2 := by fun_prop
  have hfd : DifferentiableOn ℂ f (closedBall (0 : ℂ) R) := hd.mul hpoly.differentiableOn
  have hw : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have hcauchy := hfd.circleIntegral_sub_inv_smul hw
  have hrw : (∮ z in C((0 : ℂ), R), (z - 0)⁻¹ • f z)
      = ∮ z in C((0 : ℂ), R), h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z) := by
    refine circleIntegral.integral_congr hR.le fun z _ ↦ ?_
    simp only [hf, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hrw] at hcauchy
  have hf0 : f 0 = h 0 := by
    simp [hf]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [hcauchy, smul_eq_mul, hf0, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- On a bounded window the Laplace integrand is integrable for **every** `w`. -/
@[category API, AMS 30]
theorem integrableOn_laplace_Ioc {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) (w : ℂ) (T : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-w * (t : ℂ))) (Set.Ioc 0 T) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-w * (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hFi.aestronglyMeasurable.restrict
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : ℝ ↦ C * Real.exp (‖w‖ * T)) (Set.Ioc (0 : ℝ) T) :=
    MeasureTheory.integrable_const _
  refine MeasureTheory.Integrable.mono' hconst hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with t ht
  obtain ⟨ht0, htT⟩ := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    show (-w * (t : ℂ)).re = -w.re * t by simp]
  have h1 : -w.re * t ≤ ‖w‖ * T := by
    have hre : -w.re ≤ ‖w‖ := neg_le_of_neg_le (neg_le_of_abs_le (Complex.abs_re_le_norm w))
    have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    nlinarith
  calc |F t| * Real.exp (-w.re * t) ≤ C * Real.exp (-w.re * t) :=
        mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le
    _ ≤ C * Real.exp (‖w‖ * T) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hC0

/--
**The truncated transform is entire.**  `w \mapsto \int_0^T F(t)e^{-wt}\,dt` is differentiable
on all of `\mathbb C`.

Differentiation under the integral sign: on the bounded window `(0,T]` the `w`-derivative
`-tF(t)e^{-wt}` is dominated, uniformly for `w` in a ball, by the constant
`CTe^{(\|w_0\|+1)T}`, which is integrable because the window has finite measure.  This is the
one hypothesis of `Newman.norm_sub_integral_le` that is not about `G`.
-/
@[category API, AMS 30]
theorem differentiable_truncLaplace {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℂ
      (fun w : ℂ ↦ ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-w * (t : ℂ))) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  intro w₀
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T) with hμ
  set bd : ℝ := C * T * Real.exp ((‖w₀‖ + 1) * T) with hbd
  have hmeas : ∀ w : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-w * (t : ℂ))) μ := by
    intro w
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hFi.aestronglyMeasurable.restrict
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (F t : ℂ) * (-(t : ℂ)) * Complex.exp (-w₀ * (t : ℂ))) μ := by
    refine MeasureTheory.AEStronglyMeasurable.mul (MeasureTheory.AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hFi.aestronglyMeasurable.restrict
    · exact (by fun_prop : Continuous fun t : ℝ ↦ (-(t : ℂ))).aestronglyMeasurable
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have : MeasureTheory.IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hbdint : MeasureTheory.Integrable (fun _ : ℝ ↦ bd) μ :=
    MeasureTheory.integrable_const _
  have hbound : ∀ᵐ t ∂μ, ∀ w ∈ Metric.ball w₀ 1,
      ‖(F t : ℂ) * (-(t : ℂ)) * Complex.exp (-w * (t : ℂ))‖ ≤ bd := by
    rw [hμ, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht w hw
    obtain ⟨ht0, htT⟩ := ht
    have hwn : ‖w‖ ≤ ‖w₀‖ + 1 := by
      have := (Metric.mem_ball.1 hw).le
      rw [dist_eq_norm] at this
      calc ‖w‖ = ‖w₀ + (w - w₀)‖ := by ring_nf
        _ ≤ ‖w₀‖ + ‖w - w₀‖ := norm_add_le _ _
        _ ≤ ‖w₀‖ + 1 := by linarith
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      show (-w * (t : ℂ)).re = -w.re * t by simp]
    have hre : -w.re ≤ ‖w‖ := neg_le_of_neg_le (neg_le_of_abs_le (Complex.abs_re_le_norm w))
    have h1 : -w.re * t ≤ (‖w₀‖ + 1) * T := by nlinarith [norm_nonneg w]
    have h2 : ‖(-(t : ℂ))‖ ≤ T := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htT
    have hexp : Real.exp (-w.re * t) ≤ Real.exp ((‖w₀‖ + 1) * T) := Real.exp_le_exp.2 h1
    have hT0 : (0 : ℝ) ≤ ‖(-(t : ℂ))‖ := norm_nonneg _
    have habs : (0 : ℝ) ≤ |F t| := abs_nonneg _
    have hFt := hFb t
    have hstep1 : |F t| * ‖(-(t : ℂ))‖ ≤ C * T := by nlinarith
    have hstep2 : |F t| * ‖(-(t : ℂ))‖ * Real.exp (-w.re * t)
        ≤ C * T * Real.exp ((‖w₀‖ + 1) * T) := by
      have hmul : (0 : ℝ) ≤ |F t| * ‖(-(t : ℂ))‖ := by positivity
      have hCT : (0 : ℝ) ≤ C * T := le_trans hmul hstep1
      nlinarith [Real.exp_pos (-w.re * t), Real.exp_pos ((‖w₀‖ + 1) * T)]
    rw [hbd]
    exact hstep2
  have hdiff : ∀ᵐ t ∂μ, ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun w : ℂ ↦ (F t : ℂ) * Complex.exp (-w * (t : ℂ)))
        ((F t : ℂ) * (-(t : ℂ)) * Complex.exp (-w * (t : ℂ))) w := by
    filter_upwards with t w _
    have h := (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).const_mul (F t : ℂ)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hint : MeasureTheory.Integrable
      (fun t : ℝ ↦ (F t : ℂ) * Complex.exp (-w₀ * (t : ℂ))) μ :=
    integrableOn_laplace_Ioc hFb hFi w₀ T
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w₀ one_pos) (Filter.Eventually.of_forall hmeas) hint hmeas'
    hbound hbdint hdiff).2.differentiableAt

/-! ### Newman's theorem on a disc -/

open Metric in
/--
**The Newman estimate.**  If `G` is analytic on the closed disc `|z| \le R` and bounded there
by `M` on the boundary, then
$$\Bigl|G(0) - \int_0^T F\Bigr| \le \frac{2C}{R} + \frac{2M}{RT}.$$

This is the whole of Newman's argument on a disc: the Cauchy value
`Newman.two_pi_I_inv_circleIntegral_kernel`, the single circle bound
`Newman.norm_sub_trunc_mul_kernel_le_circle`, and mathlib's
`circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`.  Letting `T \to \infty`
and then `R \to \infty` gives `\int_0^T F \to G(0)`.

-/
@[category API, AMS 30]
theorem norm_sub_integral_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {M R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hGd : DifferentiableOn ℂ G (closedBall (0 : ℂ) R))
    (hM : ∀ z : ℂ, ‖z‖ = R → ‖G z‖ ≤ M) :
    ‖G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ)‖ ≤ 2 * C / R + 2 * M / (R * T) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hgd : Differentiable ℂ
      (fun w : ℂ ↦ ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-w * (t : ℂ))) :=
    differentiable_truncLaplace hFb hFi hT.le
  set h : ℂ → ℂ := fun w ↦
    (G w - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-w * (t : ℂ))) *
      Complex.exp (w * (T : ℂ)) with hhdef
  have hexpd : Differentiable ℂ fun w : ℂ ↦ Complex.exp (w * (T : ℂ)) := by fun_prop
  have hd : DifferentiableOn ℂ h (closedBall (0 : ℂ) R) :=
    (hGd.sub hgd.differentiableOn).mul hexpd.differentiableOn
  have hh0 : h 0 = G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) := by
    simp [hhdef]
  have hcauchy := two_pi_I_inv_circleIntegral_kernel hR hd
  -- the uniform bound on the circle
  set B : ℝ := 2 * C / R ^ 2 + 2 * M / (R ^ 2 * T) with hB
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖ ≤ B := by
    intro z hzs
    have hz : ‖z‖ = R := by simpa using hzs
    have := norm_sub_trunc_mul_kernel_le_circle hFb hFi hGeq hR hz hT (hM z hz)
    rw [hhdef]
    simpa [mul_assoc] using this
  have hcirc := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z : ℂ ↦ h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)) (c := 0) hR.le hbound
  rw [smul_eq_mul, hcauchy, hh0] at hcirc
  refine hcirc.trans (le_of_eq ?_)
  rw [hB]
  field_simp

/-! ### Newman's contour, on a rectangle -/

/--
`h_T(z) = (G(z) - g_T(z))e^{zT}`, the function Newman integrates against the kernel.  Its
value at the origin is exactly the quantity to be estimated.
-/
noncomputable def newmanAux (F : ℝ → ℝ) (G : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  (G z - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
    Complex.exp (z * (T : ℂ))

@[category API, AMS 30]
theorem newmanAux_zero (F : ℝ → ℝ) (G : ℂ → ℂ) (T : ℝ) :
    newmanAux F G T 0 = G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) := by
  simp [newmanAux]

@[category API, AMS 30]
theorem differentiable_newmanAux {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ (newmanAux F G T) U := by
  have hg := differentiable_truncLaplace hFb hFi hT
  have hexp : Differentiable ℂ fun w : ℂ ↦ Complex.exp (w * (T : ℂ)) := by fun_prop
  exact (hG.sub hg.differentiableOn).mul hexp.differentiableOn

@[category API, AMS 30]
theorem norm_exp_mul_ofReal (z : ℂ) (T : ℝ) :
    ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
  rw [Complex.norm_exp]; congr 1; simp

/--
**The tail bound on the right.**  For `\mathrm{Re}\,z > 0`, `\|h_T(z)\| \le C/\mathrm{Re}\,z`,
uniformly in `T`.
-/
@[category API, AMS 30]
theorem norm_newmanAux_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {z : ℂ} {T : ℝ} (hzre : 0 < z.re) (hT : 0 ≤ T) :
    ‖newmanAux F G T z‖ ≤ C / z.re := by
  rw [newmanAux, hGeq z hzre, integral_Ioi_sub_integral_Ioc hFb hFi hzre hT, norm_mul,
    norm_exp_mul_ofReal]
  have htail := norm_integral_Ioi_le hFb hzre T
  have hprod : (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) = C / z.re := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ * Real.exp (z.re * T)
      ≤ (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
    _ = C / z.re := hprod

/--
**The truncated transform on the left.**  For `\mathrm{Re}\,z < 0`,
`\|g_T(z)e^{zT}\| \le C/(-\mathrm{Re}\,z)`, uniformly in `T`.
-/
@[category API, AMS 30]
theorem norm_trunc_mul_exp_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    {z : ℂ} {T : ℝ} (hzre : z.re < 0) (hT : 0 ≤ T) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
        * Complex.exp (z * (T : ℂ))‖ ≤ C / (-z.re) := by
  rw [norm_mul, norm_exp_mul_ofReal]
  have htr := norm_integral_Ioc_le hFb hzre hT
  have hprod : (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) = C / (-z.re) := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
        Real.exp (z.re * T)
      ≤ (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right htr (Real.exp_pos _).le
    _ = C / (-z.re) := hprod

/-- The crude kernel bound `\|k(z)\| \le \|z\|^{-1} + \|z\|/R^2`. -/
@[category API, AMS 30]
theorem norm_newmanKernel_le (R : ℝ) (z : ℂ) :
    ‖newmanKernel R z‖ ≤ ‖z‖⁻¹ + ‖z‖ / R ^ 2 := by
  have hRn : ‖((R : ℂ)) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ‖newmanKernel R z‖ ≤ ‖z⁻¹‖ + ‖z / (R : ℂ) ^ 2‖ := norm_add_le _ _
    _ = ‖z‖⁻¹ + ‖z‖ / R ^ 2 := by rw [norm_inv, norm_div, hRn]

/-! ### The four edges of the inner rectangle -/

/--
**The horizontal edges.**  On `|\mathrm{Im}\,z| = R`, `-\delta \le \mathrm{Re}\,z \le R`,
$$\|h_T(z)k(z)\| \le \frac{3(M\delta + C)}{R^2},$$
where `M` bounds `\|G\|`.  The kernel's factor `|\mathrm{Re}\,z|` cancels the `1/x` of the
Laplace bound on the right, and on the short left overhang it is at most `\delta`.
-/
@[category API, AMS 30]
theorem norm_integrand_horiz_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {M R δ T : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R) (hT : 0 ≤ T)
    {z : ℂ} (him : |z.im| = R) (hlo : -δ ≤ z.re) (hhi : z.re ≤ R) (hM : ‖G z‖ ≤ M) :
    ‖newmanAux F G T z * newmanKernel R z‖ ≤ 3 * (M * δ + C) / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hre : |z.re| ≤ R := abs_le.2 ⟨by linarith, hhi⟩
  have hk := norm_newmanKernel_horiz hR him hre
  rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
  · have hexple : Real.exp (z.re * T) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg (neg_nonneg.mpr hneg.le) hT])
    have hzne : z.re ≠ 0 := ne_of_lt hneg
    have h1 : ‖newmanAux F G T z‖ ≤ M + C / (-z.re) := by
      have hsplit : newmanAux F G T z
          = G z * Complex.exp (z * (T : ℂ))
            - (∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
                * Complex.exp (z * (T : ℂ)) := by
        rw [newmanAux]; ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ (norm_trunc_mul_exp_le hFb hneg hT))
      rw [norm_mul, norm_exp_mul_ofReal]
      calc ‖G z‖ * Real.exp (z.re * T) ≤ M * 1 :=
            mul_le_mul hM hexple (Real.exp_pos _).le hM0
        _ = M := mul_one M
    have hk' : ‖newmanKernel R z‖ ≤ 3 * (-z.re) / R ^ 2 := by rwa [abs_of_neg hneg] at hk
    have hxpos : 0 < -z.re := by linarith
    calc ‖newmanAux F G T z * newmanKernel R z‖
        = ‖newmanAux F G T z‖ * ‖newmanKernel R z‖ := norm_mul _ _
      _ ≤ (M + C / (-z.re)) * (3 * (-z.re) / R ^ 2) :=
          mul_le_mul h1 hk' (norm_nonneg _) (add_nonneg hM0 (div_nonneg hC0 hxpos.le))
      _ = 3 * (M * (-z.re) + C) / R ^ 2 := by
          field_simp
          ring
      _ ≤ 3 * (M * δ + C) / R ^ 2 := by
          have : M * (-z.re) ≤ M * δ := by
            refine mul_le_mul_of_nonneg_left ?_ hM0
            linarith
          have hR2 : (0 : ℝ) < R ^ 2 := by positivity
          rw [div_le_div_iff_of_pos_right hR2]
          linarith
  · have hk0 : ‖newmanKernel R z‖ = 0 := by
      have := hk
      rw [hzero] at this
      simp only [abs_zero, mul_zero, zero_div] at this
      exact le_antisymm this (norm_nonneg _)
    rw [norm_mul, hk0, mul_zero]
    positivity
  · have h1 : ‖newmanAux F G T z‖ ≤ C / z.re := norm_newmanAux_le hFb hFi hGeq hpos hT
    have hk' : ‖newmanKernel R z‖ ≤ 3 * z.re / R ^ 2 := by rwa [abs_of_pos hpos] at hk
    have hzne : z.re ≠ 0 := ne_of_gt hpos
    calc ‖newmanAux F G T z * newmanKernel R z‖
        = ‖newmanAux F G T z‖ * ‖newmanKernel R z‖ := norm_mul _ _
      _ ≤ (C / z.re) * (3 * z.re / R ^ 2) :=
          mul_le_mul h1 hk' (norm_nonneg _) (div_nonneg hC0 hpos.le)
      _ = 3 * C / R ^ 2 := by
          field_simp
      _ ≤ 3 * (M * δ + C) / R ^ 2 := by
          have hR2 : (0 : ℝ) < R ^ 2 := by positivity
          rw [div_le_div_iff_of_pos_right hR2]
          nlinarith

/--
**The right edge.**  On `\mathrm{Re}\,z = R`, `|\mathrm{Im}\,z| \le R`,
`\|h_T(z)k(z)\| \le 3C/R^2`.
-/
@[category API, AMS 30]
theorem norm_integrand_vert_right_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ}
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    {z : ℂ} (hre : z.re = R) (him : |z.im| ≤ R) :
    ‖newmanAux F G T z * newmanKernel R z‖ ≤ 3 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hzre : 0 < z.re := by rw [hre]; exact hR
  have habs : |z.re| = R := by rw [hre, abs_of_pos hR]
  have h1 : ‖newmanAux F G T z‖ ≤ C / z.re := norm_newmanAux_le hFb hFi hGeq hzre hT
  have hk := norm_newmanKernel_vert hR habs him
  calc ‖newmanAux F G T z * newmanKernel R z‖
      = ‖newmanAux F G T z‖ * ‖newmanKernel R z‖ := norm_mul _ _
    _ ≤ (C / z.re) * (3 / R) :=
        mul_le_mul h1 hk (norm_nonneg _) (div_nonneg hC0 hzre.le)
    _ = 3 * C / R ^ 2 := by
        rw [hre]
        field_simp

/--
**The truncated transform on a horizontal edge to the left of the axis.**
-/
@[category API, AMS 30]
theorem norm_trunc_integrand_horiz_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    {z : ℂ} (him : |z.im| = R) (hre : |z.re| ≤ R) (hneg : z.re < 0) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
        * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖ ≤ 3 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have h1 := norm_trunc_mul_exp_le hFb hneg hT
  have hk : ‖newmanKernel R z‖ ≤ 3 * (-z.re) / R ^ 2 := by
    have := norm_newmanKernel_horiz hR him hre
    rwa [abs_of_neg hneg] at this
  have hxpos : 0 < -z.re := by linarith
  calc ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
          * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      = ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
          * Complex.exp (z * (T : ℂ))‖ * ‖newmanKernel R z‖ := norm_mul _ _
    _ ≤ (C / (-z.re)) * (3 * (-z.re) / R ^ 2) :=
        mul_le_mul h1 hk (norm_nonneg _) (div_nonneg hC0 hxpos.le)
    _ = 3 * C / R ^ 2 := by
        have hzne : z.re ≠ 0 := ne_of_lt hneg
        field_simp

/-- **The truncated transform on the far left edge** `\mathrm{Re}\,z = -R`. -/
@[category API, AMS 30]
theorem norm_trunc_integrand_vert_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    {z : ℂ} (hre : z.re = -R) (him : |z.im| ≤ R) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
        * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖ ≤ 3 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hneg : z.re < 0 := by rw [hre]; linarith
  have habs : |z.re| = R := by rw [hre, abs_neg, abs_of_pos hR]
  have h1 := norm_trunc_mul_exp_le hFb hneg hT
  have hk := norm_newmanKernel_vert hR habs him
  calc ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
          * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      = ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
          * Complex.exp (z * (T : ℂ))‖ * ‖newmanKernel R z‖ := norm_mul _ _
    _ ≤ (C / (-z.re)) * (3 / R) :=
        mul_le_mul h1 hk (norm_nonneg _) (div_nonneg hC0 (by linarith))
    _ = 3 * C / R ^ 2 := by
        rw [hre]
        field_simp

/--
**The left edge, `G` part.**  On `\mathrm{Re}\,z = -\delta`, `|\mathrm{Im}\,z| \le R`,
$$\|G(z)e^{zT}k(z)\| \le M e^{-\delta T}\Bigl(\frac1\delta + \frac2R\Bigr),$$
which tends to `0` as `T \to \infty` with `\delta` and `R` fixed.  This is the one place the
analytic continuation past the imaginary axis is used.
-/
@[category API, AMS 30]
theorem norm_G_integrand_left_le {G : ℂ → ℂ} {M R δ T : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδR : δ ≤ R) {z : ℂ} (hre : z.re = -δ) (him : |z.im| ≤ R) (hM : ‖G z‖ ≤ M) :
    ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      ≤ M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hlow : δ ≤ ‖z‖ := by
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rwa [hre, abs_neg, abs_of_pos hδ] at this
  have hupp : ‖z‖ ≤ 2 * R := by
    have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : z.re ^ 2 ≤ R ^ 2 := by rw [hre]; nlinarith
    have h3 : z.im ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
    nlinarith [norm_nonneg z, hR]
  have hk : ‖newmanKernel R z‖ ≤ 1 / δ + 2 / R := by
    refine le_trans (norm_newmanKernel_le R z) ?_
    have ha : ‖z‖⁻¹ ≤ 1 / δ := by
      rw [inv_eq_one_div, div_le_div_iff₀ (lt_of_lt_of_le hδ hlow) hδ]; linarith
    have hb : ‖z‖ / R ^ 2 ≤ 2 / R := by
      rw [div_le_div_iff₀ (by positivity) hR]; nlinarith
    linarith
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (-(δ * T)) := by
    rw [norm_exp_mul_ofReal, hre]; ring_nf
  calc ‖G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z‖
      = ‖G z‖ * ‖Complex.exp (z * (T : ℂ))‖ * ‖newmanKernel R z‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) := by
        rw [hexp]
        refine mul_le_mul ?_ hk (norm_nonneg _) (mul_nonneg hM0 (Real.exp_pos _).le)
        exact mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le

/-! ### Newman's estimate on a rectangle -/

/--
**The Newman estimate.**  Let `G` be holomorphic on an open `U` containing the rectangle
`Q = [-\delta, R] \times [-R, R]`, bounded there by `M`, and equal to the Laplace transform of
`F` on `\mathrm{Re}\,z > 0`.  Then
$$\Bigl\|G(0) - \int_0^T F\Bigr\|
  \le \frac{2M\delta + 5C}{R} + RMe^{-\delta T}\Bigl(\frac1\delta + \frac2R\Bigr).$$

The first term is uniform in `T` and small for large `R` once `\delta` is small; the second
tends to `0` as `T \to \infty` for fixed `\delta` and `R`.  Taking `T \to \infty`, then
`\delta \to 0`, then `R \to \infty` gives `Newman.tendsto_integral_of_analyticOn`.
-/
@[category API, AMS 30]
theorem norm_sub_integral_le_rect {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hFi : MeasureTheory.LocallyIntegrable F) {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hGd : DifferentiableOn ℂ G U)
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
    {M R δ T : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R) (hT : 0 ≤ T)
    (hsub : rect (-δ) R (-R) R ⊆ U)
    (hM : ∀ z ∈ rect (-δ) R (-R) R, ‖G z‖ ≤ M) :
    ‖G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ)‖
      ≤ (2 * M * δ + 5 * C) / R + R * M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hIa : [[(-δ : ℝ), R]] = Set.Icc (-δ) R := Set.uIcc_of_le (by linarith)
  have hIc : [[(-R : ℝ), R]] = Set.Icc (-R) R := Set.uIcc_of_le (by linarith)
  have hIb : [[(-R : ℝ), -δ]] = Set.Icc (-R) (-δ) := Set.uIcc_of_le (by linarith)
  have h0rect : (0 : ℂ) ∈ rect (-δ) R (-R) R := by
    refine mem_rect_iff.2 ⟨?_, ?_⟩
    · rw [hIa]; simp only [Complex.zero_re]; exact ⟨by linarith, by linarith⟩
    · rw [hIc]; simp only [Complex.zero_im]; exact ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0rect)
  set A : ℝ := M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) with hA
  have hA0 : 0 ≤ A := by
    refine mul_nonneg (mul_nonneg hM0 (Real.exp_pos _).le) ?_
    have : (0 : ℝ) < 1 / δ := by positivity
    have : (0 : ℝ) < 2 / R := by positivity
    positivity
  -- the two integrands
  set gp : ℂ → ℂ := fun z ↦
    (∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ)))
      * Complex.exp (z * (T : ℂ)) * newmanKernel R z with hgp
  set Gp : ℂ → ℂ := fun z ↦ G z * Complex.exp (z * (T : ℂ)) * newmanKernel R z with hGp
  have hexpd : Differentiable ℂ fun z : ℂ ↦ Complex.exp (z * (T : ℂ)) := by fun_prop
  -- the residue
  have hres : rectInt (fun z ↦ newmanAux F G T z * newmanKernel R z) (-δ) R (-R) R
      = 2 * Real.pi * Complex.I * newmanAux F G T 0 :=
    rectInt_mul_kernel R hU hsub (differentiable_newmanAux hFb hFi hGd hT)
      (by linarith) hR (by linarith) hR
  -- the three pointwise edges
  have hbot : ∀ x ∈ [[(-δ : ℝ), R]],
      ‖newmanAux F G T ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
        * newmanKernel R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * (M * δ + C) / R ^ 2 := by
    intro x hx
    have hx' : x ∈ Set.Icc (-δ) R := hIa ▸ hx
    refine norm_integrand_horiz_le hFb hFi hGeq hR hδ hδR hT ?_ ?_ ?_ ?_
    · simp [abs_of_pos hR]
    · simpa using hx'.1
    · simpa using hx'.2
    · exact hM _ (horiz_mem_rect hx Set.left_mem_uIcc)
  have htop : ∀ x ∈ [[(-δ : ℝ), R]],
      ‖newmanAux F G T ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
        * newmanKernel R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * (M * δ + C) / R ^ 2 := by
    intro x hx
    have hx' : x ∈ Set.Icc (-δ) R := hIa ▸ hx
    refine norm_integrand_horiz_le hFb hFi hGeq hR hδ hδR hT ?_ ?_ ?_ ?_
    · simp [abs_of_pos hR]
    · simpa using hx'.1
    · simpa using hx'.2
    · exact hM _ (horiz_mem_rect hx Set.right_mem_uIcc)
  have hrig : ∀ y ∈ [[(-R : ℝ), R]],
      ‖newmanAux F G T (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        * newmanKernel R (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 3 * C / R ^ 2 := by
    intro y hy
    have hy' : y ∈ Set.Icc (-R) R := hIc ▸ hy
    refine norm_integrand_vert_right_le hFb hFi hGeq hR hT ?_ ?_
    · simp
    · simpa [abs_le] using hy'
  -- the left edge
  have hwne : ∀ y : ℝ, (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hwmem : ∀ y ∈ [[(-R : ℝ), R]],
      (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ rect (-δ) R (-R) R := by
    intro y hy
    exact vert_mem_rect Set.left_mem_uIcc hy
  have hcontw : Continuous fun y : ℝ ↦ ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by fun_prop
  have hGpc : ContinuousOn Gp (U ∩ {z : ℂ | z ≠ 0}) := by
    refine (((hGd.continuousOn).mono Set.inter_subset_left).mul ?_).mul
      ((continuousOn_newmanKernel R).mono Set.inter_subset_right)
    exact hexpd.continuous.continuousOn
  have hgc : ContinuousOn gp {z : ℂ | z ≠ 0} := by
    refine (((differentiable_truncLaplace hFb hFi hT).continuous.continuousOn).mul ?_).mul
      (continuousOn_newmanKernel R)
    exact hexpd.continuous.continuousOn
  have hint1 : IntervalIntegrable (fun y : ℝ ↦ Gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (-R) R :=
    intervalIntegrable_comp hGpc hcontw.continuousOn
      fun y hy ↦ ⟨hsub (hwmem y hy), hwne y⟩
  have hint2 : IntervalIntegrable (fun y : ℝ ↦ gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (-R) R :=
    intervalIntegrable_comp hgc hcontw.continuousOn fun y _ ↦ hwne y
  have hEq : (∫ y : ℝ in (-R : ℝ)..R, newmanAux F G T (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        * newmanKernel R (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in (-R : ℝ)..R, Gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        - ∫ y : ℝ in (-R : ℝ)..R, gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    rw [hGp, hgp, newmanAux]
    ring
  have hGpb : ‖∫ y : ℝ in (-R : ℝ)..R, Gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ A * |R - (-R)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc (-R) R := hIc ▸ (Set.Ioc_subset_Icc_self hy)
    exact norm_G_integrand_left_le hR hδ hδR (by simp) (by simpa [abs_le] using hy')
      (hM _ (hwmem y (hIc ▸ hy')))
  -- the deformation of the truncated transform off the left edge
  have hsubrect : rect (-R) (-δ) (-R) R ⊆ {z : ℂ | z ≠ 0} := by
    intro z hz
    obtain ⟨hre, -⟩ := mem_rect_iff.1 hz
    rw [hIb] at hre
    intro h
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.2 (by linarith)
  have hgd : DifferentiableOn ℂ gp {z : ℂ | z ≠ 0} :=
    (((differentiable_truncLaplace hFb hFi hT).differentiableOn).mul
      hexpd.differentiableOn).mul (differentiableOn_newmanKernel R)
  have hzero : rectInt gp (-R) (-δ) (-R) R = 0 := rectInt_eq_zero (hgd.mono hsubrect)
  have hhoriz_g : ∀ e : ℝ, |e| = R → ∀ x ∈ [[(-R : ℝ), -δ]],
      ‖gp ((x : ℂ) + (e : ℂ) * Complex.I)‖ ≤ 3 * C / R ^ 2 := by
    intro e he x hx
    have hx' : x ∈ Set.Icc (-R) (-δ) := hIb ▸ hx
    have hre : ((x : ℂ) + (e : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (e : ℂ) * Complex.I).im = e := by simp
    refine norm_trunc_integrand_horiz_le hFb hR hT ?_ ?_ ?_
    · rw [him]; exact he
    · rw [hre, abs_le]
      exact ⟨hx'.1, by linarith [hx'.2]⟩
    · rw [hre]; linarith [hx'.2]
  have hgpb : ‖∫ y : ℝ in (-R : ℝ)..R, gp (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ (3 * C / R ^ 2 + 3 * C / R ^ 2) * |(-δ) - (-R)| + (3 * C / R ^ 2) * |R - (-R)| := by
    refine norm_edge_le_of_rectInt_eq_zero hzero
      (hhoriz_g (-R) (by rw [abs_neg]; exact abs_of_pos hR))
      (hhoriz_g R (abs_of_pos hR)) ?_
    intro y hy
    have hy' : y ∈ Set.Icc (-R) R := hIc ▸ hy
    exact norm_trunc_integrand_vert_le hFb hR hT (by simp) (by simpa [abs_le] using hy')
  -- assemble
  have hmain : ‖rectInt (fun z ↦ newmanAux F G T z * newmanKernel R z) (-δ) R (-R) R‖
      ≤ (3 * (M * δ + C) / R ^ 2 + 3 * (M * δ + C) / R ^ 2) * |R - (-δ)|
        + (3 * C / R ^ 2) * |R - (-R)|
        + (A * |R - (-R)|
          + ((3 * C / R ^ 2 + 3 * C / R ^ 2) * |(-δ) - (-R)|
            + (3 * C / R ^ 2) * |R - (-R)|)) := by
    refine norm_rectInt_le_of_left hbot htop hrig ?_
    rw [hEq]
    exact le_trans (norm_sub_le _ _) (add_le_add hGpb hgpb)
  rw [hres, newmanAux_zero] at hmain
  -- the norm of the residue
  have hnormres : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I
      * (G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ))‖
      = 2 * Real.pi * ‖G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ)‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hnormres] at hmain
  -- simplify the absolute values
  rw [abs_of_pos (by linarith : (0:ℝ) < R - (-δ)), abs_of_pos (by linarith : (0:ℝ) < R - (-R)),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ (-δ) - (-R))] at hmain
  set X : ℝ := ‖G 0 - ∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ)‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have hQ0 : 0 ≤ R * A := mul_nonneg hR.le hA0
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hstep : 6 * X ≤ 2 * Real.pi * X := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.pi - 6) hX0]
  have hgoal : R * M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) = R * A := by
    rw [hA]; ring
  have hrw : (3 * (M * δ + C) / R ^ 2 + 3 * (M * δ + C) / R ^ 2) * (R - (-δ))
      + (3 * C / R ^ 2) * (R - (-R))
      + (A * (R - (-R))
        + ((3 * C / R ^ 2 + 3 * C / R ^ 2) * ((-δ) - (-R)) + (3 * C / R ^ 2) * (R - (-R))))
      ≤ 6 * ((2 * M * δ + 5 * C) / R) + 2 * (R * A) := by
    rw [← sub_nonneg]
    have hRne : R ≠ 0 := ne_of_gt hR
    have key : 6 * ((2 * M * δ + 5 * C) / R) + 2 * (R * A)
        - ((3 * (M * δ + C) / R ^ 2 + 3 * (M * δ + C) / R ^ 2) * (R - (-δ))
          + (3 * C / R ^ 2) * (R - (-R))
          + (A * (R - (-R))
            + ((3 * C / R ^ 2 + 3 * C / R ^ 2) * ((-δ) - (-R))
              + (3 * C / R ^ 2) * (R - (-R)))))
        = (6 * M * δ * (R - δ) + 6 * C * R) / R ^ 2 := by
      field_simp
      ring
    rw [key]
    refine div_nonneg (add_nonneg ?_ ?_) hR2.le
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hδ.le) (sub_nonneg.mpr hδR)
    · exact mul_nonneg (mul_nonneg (by norm_num) hC0) hR.le
  rw [hgoal]
  linarith [hmain, hstep, hrw]

/-! ### From the estimate to the limit -/

/-- A rectangle is compact. -/
@[category API, AMS 30]
theorem isCompact_rect (a b c d : ℝ) : IsCompact (rect a b c d) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- Shrinking the left edge shrinks the rectangle. -/
@[category API, AMS 30]
theorem rect_mono_left {δ δ₀ R : ℝ} (hδ : 0 < δ) (hδδ : δ ≤ δ₀) (hδR : δ₀ ≤ R) :
    rect (-δ) R (-R) R ⊆ rect (-δ₀) R (-R) R := by
  intro z hz
  obtain ⟨h1, h2⟩ := mem_rect_iff.1 hz
  refine mem_rect_iff.2 ⟨?_, h2⟩
  rw [Set.uIcc_of_le (by linarith)] at h1
  rw [Set.uIcc_of_le (by linarith)]
  exact ⟨by linarith [h1.1], h1.2⟩

/--
**The uniform bound that lets `δ → 0` with `M` fixed.**  If `G` is analytic on a neighbourhood
of the closed right half plane then for every `R > 0` there are `δ₀ > 0` and `M` such that the
rectangle `[-\delta_0, R] \times [-R, R]` lies in the domain of analyticity and `\|G\| \le M`
on it.  Every smaller `\delta` then reuses the *same* `M`.

The point of `\delta_0`: `\{iy : |y| \le R\}` is compact and contained in the open set where
`G` is analytic, so a uniform thickening of it stays inside.
-/
@[category API, AMS 30]
theorem exists_bound_rect {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G {z : ℂ | 0 ≤ z.re})
    {R : ℝ} (hR : 0 < R) :
    ∃ δ₀ M : ℝ, 0 < δ₀ ∧ δ₀ ≤ R ∧ rect (-δ₀) R (-R) R ⊆ {z : ℂ | AnalyticAt ℂ G z} ∧
      ∀ z ∈ rect (-δ₀) R (-R) R, ‖G z‖ ≤ M := by
  set U : Set ℂ := {z : ℂ | AnalyticAt ℂ G z} with hUdef
  have hU : IsOpen U := isOpen_analyticAt ℂ G
  have hK : IsCompact (rect 0 R (-R) R) := isCompact_rect _ _ _ _
  have hKU : rect 0 R (-R) R ⊆ U := by
    intro z hz
    obtain ⟨h1, -⟩ := mem_rect_iff.1 hz
    rw [Set.uIcc_of_le hR.le] at h1
    exact hG z h1.1
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  set δ₀ : ℝ := min (ε / 2) R with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) hR
  have hδ₀R : δ₀ ≤ R := min_le_right _ _
  have hsub : rect (-δ₀) R (-R) R ⊆ U := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_rect_iff.1 hz
    rw [Set.uIcc_of_le (by linarith)] at h1
    refine hεU ?_
    set c : ℝ := z.re - max z.re 0 with hc
    have hcabs : |c| ≤ δ₀ := by
      rcases le_total 0 z.re with h | h
      · rw [hc, max_eq_left h]
        simp [hδ₀.le]
      · rw [hc, max_eq_right h]
        rw [abs_of_nonpos (by simpa using h)]
        simp only [sub_zero]
        linarith [h1.1]
    refine Metric.mem_thickening_iff.2 ⟨z - (c : ℂ), ?_, ?_⟩
    · refine mem_rect_iff.2 ⟨?_, ?_⟩
      · have hre : (z - (c : ℂ)).re = max z.re 0 := by simp [hc]
        rw [hre, Set.uIcc_of_le hR.le]
        exact ⟨le_max_right _ _, max_le h1.2 hR.le⟩
      · simpa using h2
    · have hd : dist z (z - (c : ℂ)) = |c| := by
        rw [dist_eq_norm]; simp
      rw [hd]
      calc |c| ≤ δ₀ := hcabs
        _ ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
  have hcont : ContinuousOn G (rect (-δ₀) R (-R) R) := fun z hz ↦
    ((hsub hz).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_rect (-δ₀) R (-R) R).exists_bound_of_continuousOn hcont
  exact ⟨δ₀, M, hδ₀, hδ₀R, hsub, hM⟩

/--
**Newman's analytic theorem.**  A bounded, locally integrable `F : [0,∞) → ℝ` whose Laplace
transform continues analytically to the closed half plane has a convergent improper integral,
with the value given by the continuation at `0`.

Newman's contour argument: for `R > 0` let `Γ` be the boundary of
`\{|z| \le R\} \cap \{re z > -δ\}` and integrate `G(z)e^{zT}(1 + z^2/R^2)/z`.  On `|z| = R`
the kernel has modulus `2|re z|/R^2`, which balances the `e^{(re z)T}` factor on both sides;
the contribution of each piece is `O(1/R)`, uniformly in `T`.

This is the only genuinely new analytic content in the PNT step; everything else is
bookkeeping.  It is stated here rather than in `FormalConjecturesForMathlib/` because that
directory must stay `sorry`-free.
-/
@[category API, AMS 11 30]
theorem tendsto_integral_of_analyticOn {F : ℝ → ℝ} {C : ℝ}
    (hFb : ∀ t, |F t| ≤ C) (hFi : MeasureTheory.LocallyIntegrable F)
    {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G {z : ℂ | 0 ≤ z.re})
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ))) :
    Tendsto (fun T : ℝ ↦ ∫ t in Set.Ioc (0 : ℝ) T, F t) atTop (𝓝 (G 0).re) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hU : IsOpen {z : ℂ | AnalyticAt ℂ G z} := isOpen_analyticAt ℂ G
  have hGd : DifferentiableOn ℂ G {z : ℂ | AnalyticAt ℂ G z} := fun z hz ↦
    hz.differentiableAt.differentiableWithinAt
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `R` so that the `C/R` term is small
  set R : ℝ := 1 + 15 * C / ε with hRdef
  have hR : 0 < R := by
    have : 0 ≤ 15 * C / ε := by positivity
    linarith
  have hRb : 5 * C / R < ε / 3 := by
    rw [div_lt_iff₀ hR, hRdef]
    have : ε / 3 * (1 + 15 * C / ε) = ε / 3 + 5 * C := by field_simp; ring
    rw [this]
    linarith
  -- the uniform bound on the rectangle
  obtain ⟨δ₀, M, hδ₀, hδ₀R, hsub₀, hM₀⟩ := exists_bound_rect hG hR
  have h0rect : (0 : ℂ) ∈ rect (-δ₀) R (-R) R := by
    refine mem_rect_iff.2 ⟨?_, ?_⟩
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by simpa using hδ₀.le, by simpa using hR.le⟩
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by simpa using hR.le, by simpa using hR.le⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM₀ 0 h0rect)
  -- choose `δ` so that the `Mδ/R` term is small
  set d : ℝ := ε * R / (6 * (M + 1)) with hddef
  have hd0 : 0 < d := by positivity
  set δ : ℝ := min δ₀ d with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hd0
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδR : δ ≤ R := le_trans hδδ₀ hδ₀R
  have hδb : 2 * M * δ / R < ε / 3 := by
    have h1 : 2 * M * δ / R ≤ 2 * M * d / R := by
      gcongr
      exact min_le_right _ _
    have h2 : 2 * M * d / R = M * ε / (3 * (M + 1)) := by
      rw [hddef]; field_simp; ring
    have h3 : M * ε / (3 * (M + 1)) < ε / 3 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith [h2 ▸ h1]
  -- the rectangle at `δ` still sits inside the domain, with the same bound
  have hmono : rect (-δ) R (-R) R ⊆ rect (-δ₀) R (-R) R := rect_mono_left hδ hδδ₀ hδ₀R
  -- choose `T`
  set K : ℝ := R * M * (1 / δ + 2 / R) with hKdef
  have hKt : Tendsto (fun T : ℝ ↦ K * Real.exp (-(δ * T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ ↦ -(δ * T)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hδ tendsto_id)
    have h2 : Tendsto (fun T : ℝ ↦ Real.exp (-(δ * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul K
  obtain ⟨T₀, hT₀⟩ := (hKt.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith))).exists_forall_of_atTop
  refine ⟨max T₀ 0, fun T hT ↦ ?_⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hkey := norm_sub_integral_le_rect hFb hFi hU hGd hGeq hR hδ hδR hT0
    (subset_trans hmono hsub₀) (fun z hz ↦ hM₀ z (hmono hz))
  have hreal : (∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ))
      = ((∫ t in Set.Ioc (0 : ℝ) T, F t : ℝ) : ℂ) := integral_complex_ofReal
  rw [hreal] at hkey
  have hre : |(∫ t in Set.Ioc (0 : ℝ) T, F t) - (G 0).re|
      ≤ ‖G 0 - ((∫ t in Set.Ioc (0 : ℝ) T, F t : ℝ) : ℂ)‖ := by
    have := Complex.abs_re_le_norm (G 0 - ((∫ t in Set.Ioc (0 : ℝ) T, F t : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    rwa [abs_sub_comm]
  have hsplit : (2 * M * δ + 5 * C) / R = 2 * M * δ / R + 5 * C / R := by ring
  have hlast : R * M * Real.exp (-(δ * T)) * (1 / δ + 2 / R) = K * Real.exp (-(δ * T)) := by
    rw [hKdef]; ring
  have hTb : K * Real.exp (-(δ * T)) < ε / 3 := hT₀ T hTT₀
  rw [Real.dist_eq]
  rw [hsplit, hlast] at hkey
  linarith

end Newman
