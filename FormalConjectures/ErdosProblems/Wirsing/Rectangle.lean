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

/-!
# Contour integrals over the boundary of a rectangle

Mathlib has Cauchy's theorem for a disc, for an annulus and for a **rectangle**
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), but not for a general
contour.  Newman's Tauberian theorem needs a contour that surrounds `0` while staying inside
`\{\mathrm{Re}\,z > -\delta\}`, and no disc around `0` does that: `closedBall 0 R` always
contains `-R/2`.  So the contour has to be a rectangle, and this file packages the two facts
about rectangle contours that the argument uses:

* `Newman.rectInt_eq_zero` — Cauchy's theorem, a restatement of mathlib's;
* `Newman.rectInt_div_self` — the residue at an interior `0`:
  $$\frac{1}{2\pi i}\oint_{\partial Q}\frac{h(z)}{z}\,dz = h(0),$$
  proved from the removable singularity theorem (`Complex.differentiableOn_dslope`) together
  with the explicit evaluation `Newman.rectInt_inv` of `\oint_{\partial Q} dz/z = 2\pi i`,
  which is four applications of the fundamental theorem of calculus with `Complex.log` as the
  antiderivative.

The rectangle is described by its four real coordinates `a b c d` rather than by two complex
corners; all the statements below assume `a < 0 < b` and `c < 0 < d`, that is, that the origin
is interior.
-/

@[expose] public section

open scoped Interval

namespace Newman

/--
The integral of `f` over the boundary of the rectangle `[a,b] × [c,d]`, traversed
counterclockwise.  This is exactly the combination appearing in mathlib's Cauchy-Goursat
theorem for a rectangle.
-/
noncomputable def rectInt (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * Complex.I)) - (∫ x : ℝ in a..b, f (x + d * Complex.I)) +
    Complex.I * (∫ y : ℝ in c..d, f (b + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in c..d, f (a + y * Complex.I))

/-- The closed rectangle with corners `a + ci` and `b + di`. -/
def rect (a b c d : ℝ) : Set ℂ := [[a, b]] ×ℂ [[c, d]]

@[category API, AMS 30]
theorem mem_rect_iff {a b c d : ℝ} {z : ℂ} : z ∈ rect a b c d ↔ z.re ∈ [[a, b]] ∧ z.im ∈ [[c, d]] :=
  Iff.rfl

/-- **Cauchy's theorem for a rectangle.** -/
@[category API, AMS 30]
theorem rectInt_eq_zero {f : ℂ → ℂ} {a b c d : ℝ}
    (H : DifferentiableOn ℂ f (rect a b c d)) : rectInt f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ H
  simpa [rectInt, smul_eq_mul] using h

/-! ### Integrability along the four edges -/

/--
A path `γ` that is continuous on `[[a,b]]` and lands in a set on which `f` is continuous gives
an interval-integrable composite.
-/
@[category API, AMS 30]
theorem intervalIntegrable_comp {f : ℂ → ℂ} {K : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hf : ContinuousOn f K) (hγ : ContinuousOn γ [[a, b]]) (hmem : ∀ t ∈ [[a, b]], γ t ∈ K) :
    IntervalIntegrable (fun t : ℝ ↦ f (γ t)) MeasureTheory.volume a b :=
  (hf.comp hγ hmem).intervalIntegrable

/-- The horizontal edge at height `c`, as a path. -/
@[category API, AMS 30]
theorem continuous_horiz (c : ℝ) : Continuous fun x : ℝ ↦ (x : ℂ) + c * Complex.I := by
  fun_prop

/-- The vertical edge at abscissa `a`, as a path. -/
@[category API, AMS 30]
theorem continuous_vert (a : ℝ) : Continuous fun y : ℝ ↦ (a : ℂ) + y * Complex.I := by
  fun_prop

@[category API, AMS 30]
theorem horiz_mem_rect {a b c d x e : ℝ} (hx : x ∈ [[a, b]]) (he : e ∈ [[c, d]]) :
    (x : ℂ) + e * Complex.I ∈ rect a b c d := by
  refine mem_rect_iff.2 ⟨?_, ?_⟩
  · simpa using hx
  · simpa using he

@[category API, AMS 30]
theorem vert_mem_rect {a b c d e y : ℝ} (he : e ∈ [[a, b]]) (hy : y ∈ [[c, d]]) :
    (e : ℂ) + y * Complex.I ∈ rect a b c d := by
  refine mem_rect_iff.2 ⟨?_, ?_⟩
  · simpa using he
  · simpa using hy

/-! ### The winding integral `∮ dz/z = 2πi` -/

/-- `\log(-w) = \log w + \pi i` when `w` lies in the open lower half plane. -/
@[category API, AMS 30]
theorem log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw, norm_neg]
  push_cast
  ring

/-- `\log(-w) = \log w - \pi i` when `w` lies in the open upper half plane. -/
@[category API, AMS 30]
theorem log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw, norm_neg]
  push_cast
  ring

/-- On a horizontal line off the real axis, `\log` is a primitive of `1/z`. -/
@[category API, AMS 30]
theorem integral_inv_horiz {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (∫ x : ℝ in a..b, ((x : ℂ) + c * Complex.I)⁻¹)
      = Complex.log ((b : ℂ) + c * Complex.I) - Complex.log ((a : ℂ) + c * Complex.I) := by
  have hne : ∀ x : ℝ, ((x : ℂ) + c * Complex.I) ∈ Complex.slitPlane := by
    intro x
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    simpa using hc
  have hderiv : ∀ x ∈ [[a, b]],
      HasDerivAt (fun t : ℝ ↦ Complex.log ((t : ℂ) + c * Complex.I))
        (((x : ℂ) + c * Complex.I)⁻¹) x := by
    intro x _
    have h0 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + c * Complex.I) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (c * Complex.I)
    simpa [one_div] using h0.clog_real (hne x)
  have hint : IntervalIntegrable (fun x : ℝ ↦ ((x : ℂ) + c * Complex.I)⁻¹)
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    exact (continuous_horiz c).inv₀ fun x ↦ Complex.slitPlane_ne_zero (hne x)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- On a vertical line in the open right half plane, `-i\log` is a primitive of `1/z`. -/
@[category API, AMS 30]
theorem integral_inv_vert_pos {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    (∫ y : ℝ in c..d, ((b : ℂ) + y * Complex.I)⁻¹)
      = -Complex.I * (Complex.log ((b : ℂ) + d * Complex.I)
          - Complex.log ((b : ℂ) + c * Complex.I)) := by
  have hne : ∀ y : ℝ, ((b : ℂ) + y * Complex.I) ∈ Complex.slitPlane := by
    intro y
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hb))
  have hderiv : ∀ y ∈ [[c, d]],
      HasDerivAt (fun t : ℝ ↦ -Complex.I * Complex.log ((b : ℂ) + t * Complex.I))
        (((b : ℂ) + y * Complex.I)⁻¹) y := by
    intro y _
    have h0 : HasDerivAt (fun t : ℝ ↦ (b : ℂ) + t * Complex.I) Complex.I y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add
        ((b : ℂ))
    have hz : ((b : ℂ) + y * Complex.I) ≠ 0 := Complex.slitPlane_ne_zero (hne y)
    have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, ← sq, Complex.I_sq]; ring
    have key : -Complex.I * (Complex.I / ((b : ℂ) + y * Complex.I))
        = ((b : ℂ) + y * Complex.I)⁻¹ := by
      rw [← mul_div_assoc, hII, one_div]
    have h1 : HasDerivAt (fun t : ℝ ↦ -Complex.I * Complex.log ((b : ℂ) + t * Complex.I))
        (-Complex.I * (Complex.I / ((b : ℂ) + y * Complex.I))) y :=
      (h0.clog_real (hne y)).const_mul (-Complex.I)
    rwa [key] at h1
  have hint : IntervalIntegrable (fun y : ℝ ↦ ((b : ℂ) + y * Complex.I)⁻¹)
      MeasureTheory.volume c d := by
    apply Continuous.intervalIntegrable
    exact (continuous_vert b).inv₀ fun y ↦ Complex.slitPlane_ne_zero (hne y)
  rw [mul_sub]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- On a vertical line in the open left half plane, `-i\log(-z)` is a primitive of `1/z`. -/
@[category API, AMS 30]
theorem integral_inv_vert_neg {a : ℝ} (ha : a < 0) (c d : ℝ) :
    (∫ y : ℝ in c..d, ((a : ℂ) + y * Complex.I)⁻¹)
      = -Complex.I * (Complex.log (-((a : ℂ) + d * Complex.I))
          - Complex.log (-((a : ℂ) + c * Complex.I))) := by
  have hne : ∀ y : ℝ, (-((a : ℂ) + y * Complex.I)) ∈ Complex.slitPlane := by
    intro y
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    simpa using ha
  have hz : ∀ y : ℝ, ((a : ℂ) + y * Complex.I) ≠ 0 := by
    intro y hy
    exact Complex.slitPlane_ne_zero (hne y) (by rw [hy, neg_zero])
  have hderiv : ∀ y ∈ [[c, d]],
      HasDerivAt (fun t : ℝ ↦ -Complex.I * Complex.log (-((a : ℂ) + t * Complex.I)))
        (((a : ℂ) + y * Complex.I)⁻¹) y := by
    intro y _
    have hbase : HasDerivAt (fun t : ℝ ↦ (a : ℂ) + t * Complex.I) Complex.I y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add
        ((a : ℂ))
    have h0 : HasDerivAt (fun t : ℝ ↦ -((a : ℂ) + t * Complex.I)) (-Complex.I) y := hbase.neg
    have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, ← sq, Complex.I_sq]; ring
    have key : -Complex.I * (-Complex.I / (-((a : ℂ) + y * Complex.I)))
        = ((a : ℂ) + y * Complex.I)⁻¹ := by
      rw [neg_div_neg_eq, ← mul_div_assoc, hII, one_div]
    have h1 : HasDerivAt (fun t : ℝ ↦ -Complex.I * Complex.log (-((a : ℂ) + t * Complex.I)))
        (-Complex.I * (-Complex.I / (-((a : ℂ) + y * Complex.I)))) y :=
      (h0.clog_real (hne y)).const_mul (-Complex.I)
    rwa [key] at h1
  have hint : IntervalIntegrable (fun y : ℝ ↦ ((a : ℂ) + y * Complex.I)⁻¹)
      MeasureTheory.volume c d := by
    apply Continuous.intervalIntegrable
    exact (continuous_vert a).inv₀ hz
  rw [mul_sub]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/--
**The winding integral.**  If the origin is interior to the rectangle then
$$\oint_{\partial Q}\frac{dz}{z} = 2\pi i .$$

The four edges each contribute a difference of two values of `Complex.log`; the moduli cancel
in pairs, and the two arguments on the left edge differ from those on the right by `\pm\pi`
(`Newman.log_neg_of_im_neg`, `Newman.log_neg_of_im_pos`), which is where the `2\pi` comes from.
-/
@[category API, AMS 30]
theorem rectInt_inv {a b c d : ℝ} (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectInt (fun z ↦ z⁻¹) a b c d = 2 * Real.pi * Complex.I := by
  have hI : Complex.I * -Complex.I = 1 := by
    simp [Complex.I_mul_I]
  rw [rectInt, integral_inv_horiz hc.ne a b, integral_inv_horiz hd.ne' a b,
    integral_inv_vert_pos hb c d, integral_inv_vert_neg ha c d]
  have him_c : ((a : ℂ) + c * Complex.I).im < 0 := by simpa using hc
  have him_d : (0 : ℝ) < ((a : ℂ) + d * Complex.I).im := by simpa using hd
  rw [log_neg_of_im_neg him_c, log_neg_of_im_pos him_d]
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  rw [hI3, Complex.I_sq]
  ring

/-! ### The residue at an interior zero -/

/--
Along a path avoiding `0`, `h(z)/z` splits as `dslope h 0` plus `h(0)/z`.
-/
@[category API, AMS 30]
theorem integral_path_div {h : ℂ → ℂ} {K : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hd : ContinuousOn (dslope h 0) K) (hγ : ContinuousOn γ [[a, b]])
    (hmem : ∀ t ∈ [[a, b]], γ t ∈ K) (hne : ∀ t ∈ [[a, b]], γ t ≠ 0) :
    (∫ t : ℝ in a..b, h (γ t) / γ t)
      = (∫ t : ℝ in a..b, dslope h 0 (γ t)) + h 0 * ∫ t : ℝ in a..b, (γ t)⁻¹ := by
  have hsplit : ∀ t ∈ [[a, b]], h (γ t) / γ t = dslope h 0 (γ t) + h 0 * (γ t)⁻¹ := by
    intro t ht
    have hz : γ t ≠ 0 := hne t ht
    rw [dslope_of_ne _ hz, slope_def_field, sub_zero]
    field_simp
    ring
  have h1 : IntervalIntegrable (fun t : ℝ ↦ dslope h 0 (γ t)) MeasureTheory.volume a b :=
    intervalIntegrable_comp hd hγ hmem
  have h2 : IntervalIntegrable (fun t : ℝ ↦ h 0 * (γ t)⁻¹) MeasureTheory.volume a b := by
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    exact hγ.inv₀ hne
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul]

/--
**The residue at an interior origin.**  If `h` is holomorphic on an open set containing the
closed rectangle, and the origin is interior to it, then
$$\frac{1}{2\pi i}\oint_{\partial Q}\frac{h(z)}{z}\,dz = h(0).$$
-/
@[category API, AMS 30]
theorem rectInt_div_self {h : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ} (hU : IsOpen U)
    (hsub : rect a b c d ⊆ U) (hh : DifferentiableOn ℂ h U)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectInt (fun z ↦ h z / z) a b c d = 2 * Real.pi * Complex.I * h 0 := by
  have h0mem : (0 : ℂ) ∈ rect a b c d := by
    refine mem_rect_iff.2 ⟨?_, ?_⟩ <;>
      simp [Set.mem_uIcc] <;> [exact Or.inl ⟨ha.le, hb.le⟩; exact Or.inl ⟨hc.le, hd.le⟩]
  have hUnhds : U ∈ nhds (0 : ℂ) := hU.mem_nhds (hsub h0mem)
  have hds : DifferentiableOn ℂ (dslope h 0) U :=
    (Complex.differentiableOn_dslope hUnhds).2 hh
  have hcont : ContinuousOn (dslope h 0) U := hds.continuousOn
  have hzero : rectInt (dslope h 0) a b c d = 0 :=
    rectInt_eq_zero (hds.mono hsub)
  have hac : a ∈ [[a, b]] := Set.left_mem_uIcc
  have hbc : b ∈ [[a, b]] := Set.right_mem_uIcc
  have hcc : c ∈ [[c, d]] := Set.left_mem_uIcc
  have hdc : d ∈ [[c, d]] := Set.right_mem_uIcc
  have hhoriz : ∀ e : ℝ, e ≠ 0 → e ∈ [[c, d]] →
      (∫ x : ℝ in a..b, h ((x : ℂ) + e * Complex.I) / ((x : ℂ) + e * Complex.I))
        = (∫ x : ℝ in a..b, dslope h 0 ((x : ℂ) + e * Complex.I))
          + h 0 * ∫ x : ℝ in a..b, ((x : ℂ) + e * Complex.I)⁻¹ := by
    intro e he hem
    refine integral_path_div hcont (continuous_horiz e).continuousOn ?_ ?_
    · exact fun t ht ↦ hsub (horiz_mem_rect ht hem)
    · intro t _ hcon
      apply he
      simpa using congrArg Complex.im hcon
  have hvert : ∀ e : ℝ, e ≠ 0 → e ∈ [[a, b]] →
      (∫ y : ℝ in c..d, h ((e : ℂ) + y * Complex.I) / ((e : ℂ) + y * Complex.I))
        = (∫ y : ℝ in c..d, dslope h 0 ((e : ℂ) + y * Complex.I))
          + h 0 * ∫ y : ℝ in c..d, ((e : ℂ) + y * Complex.I)⁻¹ := by
    intro e he hem
    refine integral_path_div hcont (continuous_vert e).continuousOn ?_ ?_
    · exact fun t ht ↦ hsub (vert_mem_rect hem ht)
    · intro t _ hcon
      apply he
      simpa using congrArg Complex.re hcon
  have hsplit : rectInt (fun z ↦ h z / z) a b c d
      = rectInt (dslope h 0) a b c d + h 0 * rectInt (fun z ↦ z⁻¹) a b c d := by
    simp only [rectInt]
    rw [hhoriz c hc.ne hcc, hhoriz d hd.ne' hdc, hvert b hb.ne' hbc, hvert a ha.ne hac]
    ring
  rw [hsplit, hzero, rectInt_inv ha hb hc hd, zero_add]
  ring

/-! ### The Newman kernel -/

/--
**Newman's kernel** `k(z) = 1/z + z/R^2`.  It has a simple pole at `0` with residue `1`, and
on the top and bottom edges of the square `[-R,R]^2` its modulus is `O(|\mathrm{Re}\,z|/R^2)`
— the cancellation that drives Newman's proof.
-/
noncomputable def newmanKernel (R : ℝ) (z : ℂ) : ℂ := z⁻¹ + z / (R : ℂ) ^ 2

/-- `k(z) = (z^2 + R^2)/(zR^2)`. -/
@[category API, AMS 30]
theorem newmanKernel_eq {R : ℝ} (hR : R ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    newmanKernel R z = (z ^ 2 + (R : ℂ) ^ 2) / (z * (R : ℂ) ^ 2) := by
  have hR' : ((R : ℂ)) ≠ 0 := by exact_mod_cast hR
  rw [newmanKernel]
  field_simp
  ring

/-- `z^2 + R^2 = (z + iR)(z - iR)`. -/
@[category API, AMS 30]
theorem sq_add_sq_eq_mul (R : ℝ) (z : ℂ) :
    z ^ 2 + (R : ℂ) ^ 2 = (z + (R : ℂ) * Complex.I) * (z - (R : ℂ) * Complex.I) := by
  have : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [this]
  ring

/--
**The horizontal-edge bound.**  If `|\mathrm{Im}\,z| = R` and `|\mathrm{Re}\,z| \le R` then
$$\|k(z)\| \le \frac{3|\mathrm{Re}\,z|}{R^2}.$$

One of the factors `z \pm iR` is the real number `\mathrm{Re}\,z`, and the other has modulus
at most `(1 + \sqrt2)R \le 3R`.  The factor `|\mathrm{Re}\,z|` is what cancels the `1/x` in
the Laplace tail bound.
-/
@[category API, AMS 30]
theorem norm_newmanKernel_horiz {R : ℝ} (hR : 0 < R) {z : ℂ} (him : |z.im| = R)
    (hre : |z.re| ≤ R) : ‖newmanKernel R z‖ ≤ 3 * |z.re| / R ^ 2 := by
  have hnz : R ≤ ‖z‖ := by
    calc R = |z.im| := him.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hnz
    simp at hnz
    linarith
  -- the "small" factor is real, the other has modulus at most `3R`
  have hsplit : ∃ u v : ℂ, z ^ 2 + (R : ℂ) ^ 2 = u * v ∧ ‖u‖ = |z.re| ∧ ‖v‖ ≤ 3 * R := by
    have hbig : ∀ w : ℂ, w = z + (R : ℂ) * Complex.I ∨ w = z - (R : ℂ) * Complex.I →
        ‖w‖ ≤ 3 * R := by
      intro w hw
      have hzn : ‖z‖ ≤ 2 * R := by
        have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have h2 : z.re ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
        have h3 : z.im ^ 2 = R ^ 2 := by rw [← sq_abs, him]
        nlinarith [norm_nonneg z, hR]
      have hRI : ‖(R : ℂ) * Complex.I‖ = R := by
        simp [abs_of_pos hR]
      rcases hw with hw | hw <;> rw [hw]
      · calc ‖z + (R : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(R : ℂ) * Complex.I‖ := norm_add_le _ _
          _ ≤ 2 * R + R := by rw [hRI]; linarith
          _ = 3 * R := by ring
      · calc ‖z - (R : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(R : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ 2 * R + R := by rw [hRI]; linarith
          _ = 3 * R := by ring
    rcases abs_eq hR.le |>.1 him with h | h
    · refine ⟨z - (R : ℂ) * Complex.I, z + (R : ℂ) * Complex.I, ?_, ?_,
        hbig _ (Or.inl rfl)⟩
      · rw [sq_add_sq_eq_mul]; ring
      · have : z - (R : ℂ) * Complex.I = (z.re : ℂ) := by
          apply Complex.ext <;> simp [h]
        rw [this, Complex.norm_real, Real.norm_eq_abs]
    · refine ⟨z + (R : ℂ) * Complex.I, z - (R : ℂ) * Complex.I, sq_add_sq_eq_mul R z, ?_,
        hbig _ (Or.inr rfl)⟩
      · have : z + (R : ℂ) * Complex.I = (z.re : ℂ) := by
          apply Complex.ext <;> simp [h]
        rw [this, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨u, v, huv, hu, hv⟩ := hsplit
  rw [newmanKernel_eq hR.ne' hz0, huv, norm_div, norm_mul, norm_mul, hu]
  have hRn : ‖((R : ℂ)) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hRn]
  have hden : 0 < ‖z‖ * R ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < R ^ 2)]
  have hx0 : 0 ≤ |z.re| := abs_nonneg _
  calc |z.re| * ‖v‖ * R ^ 2 ≤ |z.re| * (3 * R) * R ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hx0) (by positivity)
    _ = 3 * |z.re| * (R * R ^ 2) := by ring
    _ ≤ 3 * |z.re| * (‖z‖ * R ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnz (by positivity)) (by positivity)

/--
**The vertical-edge bound.**  If `|\mathrm{Re}\,z| = R` and `|\mathrm{Im}\,z| \le R` then
`\|k(z)\| \le 3/R`.
-/
@[category API, AMS 30]
theorem norm_newmanKernel_vert {R : ℝ} (hR : 0 < R) {z : ℂ} (hre : |z.re| = R)
    (him : |z.im| ≤ R) : ‖newmanKernel R z‖ ≤ 3 / R := by
  have hnz : R ≤ ‖z‖ := by
    calc R = |z.re| := hre.symm
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR hnz
  have hzn : ‖z‖ ≤ 2 * R := by
    have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : z.re ^ 2 = R ^ 2 := by rw [← sq_abs, hre]
    have h3 : z.im ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
    nlinarith [norm_nonneg z, hR]
  have hRn : ‖((R : ℂ)) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h1 : ‖z⁻¹‖ ≤ 1 / R := by
    rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hzpos hR]
    linarith
  have h2 : ‖z / (R : ℂ) ^ 2‖ ≤ 2 / R := by
    rw [norm_div, hRn, div_le_div_iff₀ (by positivity) hR]
    nlinarith
  calc ‖newmanKernel R z‖ ≤ ‖z⁻¹‖ + ‖z / (R : ℂ) ^ 2‖ := norm_add_le _ _
    _ ≤ 1 / R + 2 / R := add_le_add h1 h2
    _ = 3 / R := by ring

/-! ### The residue of `h · k` -/

/--
Along a path avoiding `0`, `h(z)k(z)` splits as an analytic part plus `h(0)/z`.
-/
@[category API, AMS 30]
theorem integral_path_kernel {h : ℂ → ℂ} {K : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} (R : ℝ)
    (hds : ContinuousOn (dslope h 0) K) (hh : ContinuousOn h K) (hγ : ContinuousOn γ [[a, b]])
    (hmem : ∀ t ∈ [[a, b]], γ t ∈ K) (hne : ∀ t ∈ [[a, b]], γ t ≠ 0) :
    (∫ t : ℝ in a..b, h (γ t) * newmanKernel R (γ t))
      = (∫ t : ℝ in a..b, (dslope h 0 (γ t) + h (γ t) * γ t / (R : ℂ) ^ 2))
        + h 0 * ∫ t : ℝ in a..b, (γ t)⁻¹ := by
  have hsplit : ∀ t ∈ [[a, b]], h (γ t) * newmanKernel R (γ t)
      = (dslope h 0 (γ t) + h (γ t) * γ t / (R : ℂ) ^ 2) + h 0 * (γ t)⁻¹ := by
    intro t ht
    have hz : γ t ≠ 0 := hne t ht
    rw [dslope_of_ne _ hz, slope_def_field, sub_zero, newmanKernel]
    field_simp
    ring
  have hc1 : ContinuousOn (fun t : ℝ ↦ dslope h 0 (γ t) + h (γ t) * γ t / (R : ℂ) ^ 2)
      [[a, b]] := by
    exact ((hds.comp hγ hmem).add (((hh.comp hγ hmem).mul hγ).div_const _))
  have h1 : IntervalIntegrable (fun t : ℝ ↦ dslope h 0 (γ t) + h (γ t) * γ t / (R : ℂ) ^ 2)
      MeasureTheory.volume a b := hc1.intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ ↦ h 0 * (γ t)⁻¹) MeasureTheory.volume a b :=
    (IntervalIntegrable.const_mul (hγ.inv₀ hne).intervalIntegrable _)
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul]

/--
**Newman's residue on a rectangle.**  If `h` is holomorphic on an open set containing the
closed rectangle and the origin is interior, then
$$\oint_{\partial Q} h(z)k(z)\,dz = 2\pi i\,h(0).$$

The `z/R^2` half of the kernel contributes nothing, and the `1/z` half contributes the
residue.
-/
@[category API, AMS 30]
theorem rectInt_mul_kernel {h : ℂ → ℂ} {U : Set ℂ} {a b c d : ℝ} (R : ℝ) (hU : IsOpen U)
    (hsub : rect a b c d ⊆ U) (hh : DifferentiableOn ℂ h U)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectInt (fun z ↦ h z * newmanKernel R z) a b c d = 2 * Real.pi * Complex.I * h 0 := by
  have h0mem : (0 : ℂ) ∈ rect a b c d := by
    refine mem_rect_iff.2 ⟨?_, ?_⟩ <;> simp [Set.mem_uIcc]
    · exact Or.inl ⟨ha.le, hb.le⟩
    · exact Or.inl ⟨hc.le, hd.le⟩
  have hUnhds : U ∈ nhds (0 : ℂ) := hU.mem_nhds (hsub h0mem)
  have hds : DifferentiableOn ℂ (dslope h 0) U :=
    (Complex.differentiableOn_dslope hUnhds).2 hh
  have hA : DifferentiableOn ℂ (fun z ↦ dslope h 0 z + h z * z / (R : ℂ) ^ 2) U :=
    hds.add ((hh.mul differentiableOn_id).div_const _)
  have hzero : rectInt (fun z ↦ dslope h 0 z + h z * z / (R : ℂ) ^ 2) a b c d = 0 :=
    rectInt_eq_zero (hA.mono hsub)
  have hcds : ContinuousOn (dslope h 0) U := hds.continuousOn
  have hch : ContinuousOn h U := hh.continuousOn
  have hac : a ∈ [[a, b]] := Set.left_mem_uIcc
  have hbc : b ∈ [[a, b]] := Set.right_mem_uIcc
  have hcc : c ∈ [[c, d]] := Set.left_mem_uIcc
  have hdc : d ∈ [[c, d]] := Set.right_mem_uIcc
  have hhoriz : ∀ e : ℝ, e ≠ 0 → e ∈ [[c, d]] →
      (∫ x : ℝ in a..b, h ((x : ℂ) + e * Complex.I) * newmanKernel R ((x : ℂ) + e * Complex.I))
        = (∫ x : ℝ in a..b, (dslope h 0 ((x : ℂ) + e * Complex.I)
            + h ((x : ℂ) + e * Complex.I) * ((x : ℂ) + e * Complex.I) / (R : ℂ) ^ 2))
          + h 0 * ∫ x : ℝ in a..b, ((x : ℂ) + e * Complex.I)⁻¹ := by
    intro e he hem
    refine integral_path_kernel R hcds hch (continuous_horiz e).continuousOn ?_ ?_
    · exact fun t ht ↦ hsub (horiz_mem_rect ht hem)
    · intro t _ hcon
      exact he (by simpa using congrArg Complex.im hcon)
  have hvert : ∀ e : ℝ, e ≠ 0 → e ∈ [[a, b]] →
      (∫ y : ℝ in c..d, h ((e : ℂ) + y * Complex.I) * newmanKernel R ((e : ℂ) + y * Complex.I))
        = (∫ y : ℝ in c..d, (dslope h 0 ((e : ℂ) + y * Complex.I)
            + h ((e : ℂ) + y * Complex.I) * ((e : ℂ) + y * Complex.I) / (R : ℂ) ^ 2))
          + h 0 * ∫ y : ℝ in c..d, ((e : ℂ) + y * Complex.I)⁻¹ := by
    intro e he hem
    refine integral_path_kernel R hcds hch (continuous_vert e).continuousOn ?_ ?_
    · exact fun t ht ↦ hsub (vert_mem_rect hem ht)
    · intro t _ hcon
      exact he (by simpa using congrArg Complex.re hcon)
  have hsplit : rectInt (fun z ↦ h z * newmanKernel R z) a b c d
      = rectInt (fun z ↦ dslope h 0 z + h z * z / (R : ℂ) ^ 2) a b c d
        + h 0 * rectInt (fun z ↦ z⁻¹) a b c d := by
    simp only [rectInt]
    rw [hhoriz c hc.ne hcc, hhoriz d hd.ne' hdc, hvert b hb.ne' hbc, hvert a ha.ne hac]
    ring
  rw [hsplit, hzero, rectInt_inv ha hb hc hd, zero_add]
  ring

/-! ### Bounding a boundary integral edge by edge -/

/--
**The edge-by-edge bound.**  A pointwise bound on each of the four edges bounds the whole
boundary integral, each edge weighted by its length.
-/
@[category API, AMS 30]
theorem norm_rectInt_le {f : ℂ → ℂ} {a b c d B₁ B₂ B₃ B₄ : ℝ}
    (h₁ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + c * Complex.I)‖ ≤ B₁)
    (h₂ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + d * Complex.I)‖ ≤ B₂)
    (h₃ : ∀ y ∈ [[c, d]], ‖f ((b : ℂ) + y * Complex.I)‖ ≤ B₃)
    (h₄ : ∀ y ∈ [[c, d]], ‖f ((a : ℂ) + y * Complex.I)‖ ≤ B₄) :
    ‖rectInt f a b c d‖ ≤ (B₁ + B₂) * |b - a| + (B₃ + B₄) * |d - c| := by
  have hsub₁ : Set.uIoc a b ⊆ [[a, b]] := Set.Ioc_subset_Icc_self
  have hsub₂ : Set.uIoc c d ⊆ [[c, d]] := Set.Ioc_subset_Icc_self
  have e₁ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)‖ ≤ B₁ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₁ x (hsub₁ hx)
  have e₂ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I)‖ ≤ B₂ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₂ x (hsub₁ hx)
  have e₃ : ‖∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I)‖ ≤ B₃ * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ h₃ y (hsub₂ hy)
  have e₄ : ‖∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ ≤ B₄ * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ h₄ y (hsub₂ hy)
  have hI : ∀ w : ℂ, ‖Complex.I * w‖ = ‖w‖ := by
    intro w; rw [norm_mul, Complex.norm_I, one_mul]
  have key : ∀ w x y z : ℂ, ‖w - x + y - z‖ ≤ ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by
    intro w x y z
    calc ‖w - x + y - z‖ ≤ ‖w - x + y‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (‖w - x‖ + ‖y‖) + ‖z‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖w‖ + ‖x‖) + ‖y‖) + ‖z‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by ring
  have hmain := key (∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I))
    (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))
    (Complex.I * ∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I))
    (Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I))
  rw [hI, hI] at hmain
  rw [rectInt]
  linarith

/--
A variant of `Newman.norm_rectInt_le` in which the left edge is bounded as a whole rather
than pointwise.  This is the form Newman's argument needs: on the left edge the truncated
transform has no pointwise bound and must first be deformed away.
-/
@[category API, AMS 30]
theorem norm_rectInt_le_of_left {f : ℂ → ℂ} {a b c d B₁ B₂ B₃ E : ℝ}
    (h₁ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + c * Complex.I)‖ ≤ B₁)
    (h₂ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + d * Complex.I)‖ ≤ B₂)
    (h₃ : ∀ y ∈ [[c, d]], ‖f ((b : ℂ) + y * Complex.I)‖ ≤ B₃)
    (h₄ : ‖∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ ≤ E) :
    ‖rectInt f a b c d‖ ≤ (B₁ + B₂) * |b - a| + B₃ * |d - c| + E := by
  have hsub₁ : Set.uIoc a b ⊆ [[a, b]] := Set.Ioc_subset_Icc_self
  have hsub₂ : Set.uIoc c d ⊆ [[c, d]] := Set.Ioc_subset_Icc_self
  have e₁ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)‖ ≤ B₁ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₁ x (hsub₁ hx)
  have e₂ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I)‖ ≤ B₂ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₂ x (hsub₁ hx)
  have e₃ : ‖∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I)‖ ≤ B₃ * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ h₃ y (hsub₂ hy)
  have hI : ∀ w : ℂ, ‖Complex.I * w‖ = ‖w‖ := by
    intro w; rw [norm_mul, Complex.norm_I, one_mul]
  have key : ∀ w x y z : ℂ, ‖w - x + y - z‖ ≤ ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by
    intro w x y z
    calc ‖w - x + y - z‖ ≤ ‖w - x + y‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (‖w - x‖ + ‖y‖) + ‖z‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖w‖ + ‖x‖) + ‖y‖) + ‖z‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by ring
  have hmain := key (∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I))
    (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))
    (Complex.I * ∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I))
    (Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I))
  rw [hI, hI] at hmain
  rw [rectInt]
  linarith

/--
**Deformation.**  If the boundary integral over a rectangle vanishes then its right edge is
bounded by the other three.  Newman uses this to move the truncated transform off the edge
`\mathrm{Re}\,z = -\delta`, which passes close to the origin, onto the far edge
`\mathrm{Re}\,z = -R`, where the kernel is small.
-/
@[category API, AMS 30]
theorem norm_edge_le_of_rectInt_eq_zero {f : ℂ → ℂ} {a b c d B₁ B₂ B₄ : ℝ}
    (hzero : rectInt f a b c d = 0)
    (h₁ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + c * Complex.I)‖ ≤ B₁)
    (h₂ : ∀ x ∈ [[a, b]], ‖f ((x : ℂ) + d * Complex.I)‖ ≤ B₂)
    (h₄ : ∀ y ∈ [[c, d]], ‖f ((a : ℂ) + y * Complex.I)‖ ≤ B₄) :
    ‖∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I)‖ ≤ (B₁ + B₂) * |b - a| + B₄ * |d - c| := by
  have hsub₁ : Set.uIoc a b ⊆ [[a, b]] := Set.Ioc_subset_Icc_self
  have hsub₂ : Set.uIoc c d ⊆ [[c, d]] := Set.Ioc_subset_Icc_self
  have e₁ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)‖ ≤ B₁ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₁ x (hsub₁ hx)
  have e₂ : ‖∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I)‖ ≤ B₂ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ h₂ x (hsub₁ hx)
  have e₄ : ‖∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ ≤ B₄ * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ h₄ y (hsub₂ hy)
  have hI : ∀ w : ℂ, ‖Complex.I * w‖ = ‖w‖ := by
    intro w; rw [norm_mul, Complex.norm_I, one_mul]
  have hEq : Complex.I * ∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I)
      = -(∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I))
        + (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))
        + Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I) := by
    rw [rectInt] at hzero
    linear_combination hzero
  have hb : ‖Complex.I * ∫ y : ℝ in c..d, f ((b : ℂ) + y * Complex.I)‖
      ≤ ‖∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)‖
        + ‖∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I)‖
        + ‖Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ := by
    rw [hEq]
    calc ‖-(∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I))
            + (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))
            + Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖
        ≤ ‖-(∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I))
            + (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))‖
          + ‖Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ := norm_add_le _ _
      _ ≤ (‖∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)‖
            + ‖∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I)‖)
          + ‖Complex.I * ∫ y : ℝ in c..d, f ((a : ℂ) + y * Complex.I)‖ := by
          gcongr
          simpa using norm_add_le (-(∫ x : ℝ in a..b, f ((x : ℂ) + c * Complex.I)))
            (∫ x : ℝ in a..b, f ((x : ℂ) + d * Complex.I))
  rw [hI, hI] at hb
  linarith

/-! ### Regularity of the kernel away from the origin -/

@[category API, AMS 30]
theorem differentiableOn_newmanKernel (R : ℝ) :
    DifferentiableOn ℂ (newmanKernel R) {z : ℂ | z ≠ 0} := by
  intro z hz
  have hz0 : z ≠ 0 := hz
  have h : DifferentiableAt ℂ (fun w : ℂ ↦ w⁻¹ + w / (R : ℂ) ^ 2) z :=
    (differentiableAt_id.inv hz0).add (differentiableAt_id.div_const _)
  exact h.differentiableWithinAt

@[category API, AMS 30]
theorem continuousOn_newmanKernel (R : ℝ) :
    ContinuousOn (newmanKernel R) {z : ℂ | z ≠ 0} :=
  (differentiableOn_newmanKernel R).continuousOn

end Newman
