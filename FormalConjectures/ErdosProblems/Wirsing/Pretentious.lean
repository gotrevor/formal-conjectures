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
public import FormalConjectures.ErdosProblems.Wirsing.Basic

/-!
# `f` is pretentious to no `n^{it}`

For a multiplicative `f : ℕ → ℝ` with values in `{±1}` and a real `t`, the *pretentious
distance* of `f` to the character `n \mapsto n^{it}` is
$$\mathbb{D}(f, n^{it}; x)^2 = \sum_{p \le x} \frac{1 - f(p)\cos(t\log p)}{p}.$$
The divergent case of Wirsing's theorem assumes this diverges at `t = 0`.  This file proves
that it then diverges for **every** real `t`, which is the uniformity that the Halász-type
endgame needs.

The mechanism is:

* for `t \ne 0`, $\sum_p (1 - \cos(t\log p))/p = \infty$, because `ζ` has a pole at `1` and is
  finite at `1 + it` (`Wirsing.not_summable_one_sub_cos`);
* since `f(p)^2 = 1`, the inequality `|f(p)^2 - (p^{it})^2| \le 2|f(p) - p^{it}|` transfers
  divergence at `2t` to divergence at `t` (`Wirsing.one_sub_cos_two_mul_le`).

Only *continuity* of `ζ` at `1 + it` is used, not the non-vanishing
`riemannZeta_ne_zero_of_one_le_re`.

*References:*
- [GS] Granville, A. and Soundararajan, K., *Multiplicative Number Theory I: the pretentious
  view*, chapters on the pretentious distance.
-/

@[expose] public section

open Filter Complex

open scoped Topology

namespace Wirsing

/-- The elementary inequality `1 - \cos 2θ ≤ 4(1 - ε\cos θ)` for `ε = ±1`.

It is the trigonometric form of `|z^2 - w^2| ≤ 2|z - w|` for `z, w` on the unit circle, and is
what lets a `{±1}`-valued `f` inherit non-pretentiousness from the constant function `1`. -/
@[category API, AMS 11]
theorem one_sub_cos_two_mul_le {θ ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    1 - Real.cos (2 * θ) ≤ 4 * (1 - ε * Real.cos θ) := by
  have h : 1 - Real.cos (2 * θ) = 2 * ((1 - Real.cos θ) * (1 + Real.cos θ)) := by
    rw [Real.cos_two_mul]; ring
  have h1 := Real.neg_one_le_cos θ
  have h2 := Real.cos_le_one θ
  rcases hε with rfl | rfl <;> rw [h] <;> nlinarith

/-- The prime zeta function `∑_p p^{-(1+x)}` tends to `∞` as `x → 0⁺`.

This is the only place where the divergence of `∑_p 1/p` is used. -/
@[category API, AMS 11]
theorem tendsto_tsum_primes_rpow :
    Tendsto (fun x : ℝ ↦ ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + x))) (𝓝[>] (0 : ℝ)) atTop := by
  have hpos : ∀ p : Nat.Primes, (0 : ℝ) < (p : ℝ) := fun p ↦ by exact_mod_cast p.2.pos
  rw [tendsto_atTop]
  intro M
  obtain ⟨F, hF⟩ : ∃ F : Finset Nat.Primes, M < ∑ p ∈ F, (1 / (p : ℝ)) := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (f := fun p : Nat.Primes ↦ (1 / (p : ℝ)))
        (fun p ↦ by have := hpos p; positivity) h)
  have hcont : Continuous (fun x : ℝ ↦ ∑ p ∈ F, (p : ℝ) ^ (-(1 + x))) := by
    refine continuous_finsetSum _ fun p _ ↦ ?_
    simp only [Real.rpow_def_of_pos (hpos p)]
    fun_prop
  have h0 : ∑ p ∈ F, ((p : ℝ)) ^ (-(1 + (0 : ℝ))) = ∑ p ∈ F, (1 / (p : ℝ)) := by
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [add_zero, Real.rpow_neg_one, one_div]
  have hev : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), M < ∑ p ∈ F, (p : ℝ) ^ (-(1 + x)) := by
    have ht : Tendsto (fun x : ℝ ↦ ∑ p ∈ F, ((p : ℝ)) ^ (-(1 + x))) (𝓝 (0 : ℝ))
        (𝓝 (∑ p ∈ F, (1 / (p : ℝ)))) := by
      simpa only [h0] using hcont.tendsto (0 : ℝ)
    exact ht.eventually_const_lt hF
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with x hx hx0
  have hsum : Summable fun p : Nat.Primes ↦ (p : ℝ) ^ (-(1 + x)) :=
    Nat.Primes.summable_rpow.2 (by simp only [Set.mem_Ioi] at hx0; linarith)
  exact le_trans hx.le (hsum.sum_le_tsum F fun p _ ↦ Real.rpow_nonneg (hpos p).le _)

/-- The Euler factor of `ζ` at a prime `p` and `s = y + it`, in polar form:
$$|1 - p^{-y-it}|^2 = (1 - p^{-y})^2 + 2p^{-y}(1 - \cos(t\log p)).$$
Everything in this file flows from this identity: the deficit `1 - \cos(t\log p)` is exactly
the excess of `|1 - p^{-s}|` over `1 - p^{-y}`. -/
@[category API, AMS 11]
theorem norm_sq_one_sub_prime_cpow (p : Nat.Primes) (y t : ℝ) :
    ‖1 - ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))‖ ^ 2 =
      (1 - (p : ℝ) ^ (-y)) ^ 2 + 2 * (p : ℝ) ^ (-y) * (1 - Real.cos (t * Real.log p)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 p.2.ne_zero
  set L := Real.log (p : ℝ) with hL
  have hcast : ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
  have hlog : Complex.log ((p : ℕ) : ℂ) = (L : ℂ) := by
    rw [hcast, hL, Complex.ofReal_log hp.le]
  have hcpow : ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))
      = Complex.exp (((-(L * y) : ℝ) : ℂ) + ((-(L * t) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hpne, hlog]
    push_cast
    ring_nf
  have hexp : (p : ℝ) ^ (-y) = Real.exp (-(L * y)) := by
    rw [Real.rpow_def_of_pos hp, hL]; ring_nf
  rw [hcpow, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_re, Complex.exp_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one, zero_add, add_zero]
  rw [← hexp]
  have hcos : Real.cos (-(L * t)) = Real.cos (t * L) := by rw [Real.cos_neg]; ring_nf
  have hsin : Real.sin (-(L * t)) = -Real.sin (t * L) := by
    rw [Real.sin_neg]; ring_nf
  have hpyth : Real.cos (t * L) ^ 2 + Real.sin (t * L) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  simp only [hcos, hsin]
  nlinarith [hpyth, sq_nonneg ((p : ℝ) ^ (-y))]

/-- The logarithms of the Euler factors of `ζ` are summable over the primes for `re s > 1`. -/
@[category API, AMS 11]
theorem summable_neg_log_one_sub_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
  have := DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
    (1 : DirichletCharacter ℂ 1) hs
  simpa only [MulChar.one_apply (isUnit_of_subsingleton _), one_mul] using this

/-- `\log|ζ(s)|` is the sum over primes of `-\log|1 - p^{-s}|`, for `re s > 1`. -/
@[category API, AMS 11]
theorem log_norm_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ = ∑' p : Nat.Primes, -Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-s)‖ := by
  rw [← riemannZeta_eulerProduct_exp_log hs, Complex.norm_exp, Real.log_exp,
    Complex.re_tsum (summable_neg_log_one_sub_prime_cpow hs)]
  exact tsum_congr fun p ↦ by rw [Complex.neg_re, Complex.log_re]

/-- The termwise comparison of the Euler factors at `y` and at `y + it`:
$$\log|1 - p^{-y-it}| - \log(1 - p^{-y}) \le 4(1 - \cos(t\log p))p^{-y}.$$
The constant `4` is wasteful; only the linear order in `1 - \cos` matters. -/
@[category API, AMS 11]
theorem log_norm_sub_log_norm_le (p : Nat.Primes) {y : ℝ} (hy : 1 ≤ y) (t : ℝ) :
    Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))‖
      - Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖
      ≤ 4 * ((1 - Real.cos (t * Real.log p)) * (p : ℝ) ^ (-y)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  set a := (p : ℝ) ^ (-y) with hadef
  have hapos : 0 < a := Real.rpow_pos_of_pos (by linarith) _
  have hahalf : a ≤ 1 / 2 := by
    have h1 : a ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one, ← one_div] at h1
    exact h1.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  set c := Real.cos (t * Real.log (p : ℝ)) with hcdef
  have hc1 : c ≤ 1 := Real.cos_le_one _
  set u := 2 * a * (1 - c) with hudef
  set v := (1 - a) ^ 2 with hvdef
  have hu : 0 ≤ u := by rw [hudef]; nlinarith
  have hv : 1 / 4 ≤ v := by rw [hvdef]; nlinarith
  have hvpos : (0 : ℝ) < v := by linarith
  have hvu : (0 : ℝ) < v + u := by linarith
  have h1 : ‖1 - ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))‖ ^ 2 = v + u := by
    rw [norm_sq_one_sub_prime_cpow p y t, ← hadef, ← hcdef, hudef, hvdef]
  have h0 : ‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖ = 1 - a := by
    have h := norm_sq_one_sub_prime_cpow p y 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, sub_self,
      mul_zero] at h
    rw [← hadef] at h
    have hnn : (0 : ℝ) ≤ 1 - a := by linarith
    have hsq : Real.sqrt (‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖ ^ 2) = Real.sqrt ((1 - a) ^ 2) := by
      rw [h]
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsq
  have hlog : Real.log (v + u) - Real.log v ≤ 4 * u := by
    have hdiv : Real.log ((v + u) / v) ≤ (v + u) / v - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hvu) (ne_of_gt hvpos)] at hdiv
    have heq : (v + u) / v - 1 = u / v := by
      field_simp
      ring
    rw [heq] at hdiv
    have hle : u / v ≤ 4 * u := by
      rw [div_le_iff₀ hvpos]; nlinarith
    linarith
  have hlogX : Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))‖
      = Real.log (v + u) / 2 := by
    rw [← h1, Real.log_pow]; push_cast; ring
  have hlogX0 : Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖ = Real.log v / 2 := by
    rw [h0, hvdef, Real.log_pow]; push_cast; ring
  have hexpand : (4 : ℝ) * u = 8 * ((1 - c) * a) := by rw [hudef]; ring
  rw [hlogX, hlogX0]
  linarith

/-- On the real axis the Euler factor is real: `|1 - p^{-y}| = 1 - p^{-y}` for `y ≥ 1`. -/
@[category API, AMS 11]
theorem norm_one_sub_prime_cpow_ofReal (p : Nat.Primes) {y : ℝ} (hy : 1 ≤ y) :
    ‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖ = 1 - (p : ℝ) ^ (-y) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hapos : 0 < (p : ℝ) ^ (-y) := Real.rpow_pos_of_pos (by linarith) _
  have hahalf : (p : ℝ) ^ (-y) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-y) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one, ← one_div] at h1
    exact h1.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have h := norm_sq_one_sub_prime_cpow p y 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, sub_self, mul_zero] at h
  have hnn : (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-y) := by linarith
  have hsq : Real.sqrt (‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖ ^ 2)
      = Real.sqrt ((1 - (p : ℝ) ^ (-y)) ^ 2) := by rw [h]
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hnn] at hsq

/-- The real form of the summability of the Euler logarithms. -/
@[category API, AMS 11]
theorem summable_neg_log_norm {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-s)‖ := by
  refine ((Complex.hasSum_re (summable_neg_log_one_sub_prime_cpow hs).hasSum).summable).congr
    fun p ↦ ?_
  rw [Complex.neg_re, Complex.log_re]

/-- The prime zeta function is dominated by `\log|ζ|` on the real axis:
`∑_p p^{-y} ≤ \log ζ(y)` for `y > 1`.  This is `a ≤ -\log(1 - a)` summed over the primes. -/
@[category API, AMS 11]
theorem tsum_rpow_le_log_norm_riemannZeta {y : ℝ} (hy : 1 < y) :
    ∑' p : Nat.Primes, (p : ℝ) ^ (-y) ≤ Real.log ‖riemannZeta (y : ℂ)‖ := by
  have hs : (1 : ℝ) < ((y : ℂ)).re := by simpa using hy
  rw [log_norm_riemannZeta hs]
  refine (Nat.Primes.summable_rpow.2 (by linarith : (-y : ℝ) < -1)).tsum_le_tsum ?_
    (summable_neg_log_norm hs)
  intro p
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hapos : 0 < (p : ℝ) ^ (-y) := Real.rpow_pos_of_pos (by linarith) _
  rw [norm_one_sub_prime_cpow_ofReal p hy.le]
  have hlt : (p : ℝ) ^ (-y) < 1 := by
    have h1 : (p : ℝ) ^ (-y) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one, ← one_div] at h1
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - (p : ℝ) ^ (-y) by linarith)
  linarith

/-- Summing the termwise comparison over the primes:
$$\log|ζ(y)| - \log|ζ(y + it)| \le 4\sum_p \frac{1 - \cos(t\log p)}{p}$$
whenever the right-hand series converges.  The left-hand side is unbounded as `y \to 1^+`,
which is the contradiction. -/
@[category API, AMS 11]
theorem log_norm_riemannZeta_sub_le {y : ℝ} (hy : 1 < y) {t : ℝ}
    (hS : Summable fun p : Nat.Primes ↦ (1 - Real.cos (t * Real.log p)) / p) :
    Real.log ‖riemannZeta (y : ℂ)‖ - Real.log ‖riemannZeta ((y : ℂ) + (t : ℂ) * I)‖
      ≤ 4 * ∑' p : Nat.Primes, (1 - Real.cos (t * Real.log p)) / p := by
  have hsy : (1 : ℝ) < ((y : ℂ)).re := by simpa using hy
  have hsyt : (1 : ℝ) < ((y : ℂ) + (t : ℂ) * I).re := by simpa using hy
  have hf := summable_neg_log_norm hsy
  have hg := summable_neg_log_norm hsyt
  -- pointwise facts about a prime
  have hpbound : ∀ p : Nat.Primes, (p : ℝ) ^ (-y) ≤ 1 / (p : ℝ) := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have h1 : (p : ℝ) ^ (-y) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h1
  have hcosnn : ∀ p : Nat.Primes, 0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
    intro p; have := Real.cos_le_one (t * Real.log (p : ℝ)); linarith
  have hcos2 : ∀ p : Nat.Primes, 1 - Real.cos (t * Real.log (p : ℝ)) ≤ 2 := by
    intro p; have := Real.neg_one_le_cos (t * Real.log (p : ℝ)); linarith
  have hrpownn : ∀ p : Nat.Primes, 0 ≤ (p : ℝ) ^ (-y) := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    exact (Real.rpow_pos_of_pos (by linarith) _).le
  -- the middle series is summable
  have hmid : Summable fun p : Nat.Primes ↦
      (1 - Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-y) := by
    refine Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (hcosnn p) (hrpownn p))
      (fun p ↦ ?_) ((Nat.Primes.summable_rpow.2 (by linarith : (-y : ℝ) < -1)).mul_left 2)
    exact mul_le_mul_of_nonneg_right (hcos2 p) (hrpownn p)
  calc Real.log ‖riemannZeta (y : ℂ)‖ - Real.log ‖riemannZeta ((y : ℂ) + (t : ℂ) * I)‖
      = ∑' p : Nat.Primes, (-Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-(y : ℂ))‖
          - -Real.log ‖1 - ((p : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))‖) := by
        rw [log_norm_riemannZeta hsy, log_norm_riemannZeta hsyt, hf.tsum_sub hg]
    _ ≤ ∑' p : Nat.Primes, 4 * ((1 - Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-y)) := by
        refine (hf.sub hg).tsum_le_tsum (fun p ↦ ?_) (hmid.mul_left 4)
        have := log_norm_sub_log_norm_le p hy.le t
        linarith
    _ = 4 * ∑' p : Nat.Primes, (1 - Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-y) :=
        tsum_mul_left
    _ ≤ 4 * ∑' p : Nat.Primes, (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
        refine mul_le_mul_of_nonneg_left (hmid.tsum_le_tsum (fun p ↦ ?_) hS) (by norm_num)
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (hpbound p) (hcosnn p)

/-- For `t ≠ 0` the series `∑_p (1 - \cos(t\log p))/p` diverges: the constant function `1`
is not pretentious to `n^{it}`. -/
@[category API, AMS 11]
theorem not_summable_one_sub_cos {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (fun p : Nat.Primes ↦ (1 - Real.cos (t * Real.log p)) / p) := by
  intro hS
  set S := ∑' p : Nat.Primes, (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) with hSdef
  -- `ζ` is continuous at `1 + it`, hence bounded near it
  have hne : ((1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    rw [Complex.ofReal_one] at h
    have h0 : (t : ℂ) * I = 0 := by linear_combination h
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact ht (Complex.ofReal_eq_zero.1 h1)
    · exact Complex.I_ne_zero h1
  have hcont : ContinuousAt riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta hne).continuousAt
  set B := ‖riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖ + 1 with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hBdef]; linarith [norm_nonneg (riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I))]
  have hmap : Tendsto (fun x : ℝ ↦ (((1 + x : ℝ) : ℂ) + (t : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (((1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    have hc : Continuous fun x : ℝ ↦ (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) := by fun_prop
    have h0 := hc.tendsto (0 : ℝ)
    rw [show (1 : ℝ) + 0 = 1 by ring] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun x : ℝ ↦ ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
    (hcont.tendsto.comp hmap).norm
  have hevB : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B := by
    filter_upwards [hnorm (Iio_mem_nhds (show
      ‖riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖ < B by rw [hBdef]; linarith))] with x hx
    exact le_of_lt hx
  have hdiv := tendsto_tsum_primes_rpow.eventually_ge_atTop (Real.log B + 4 * S + 1)
  obtain ⟨x, ⟨hxB, hxdiv⟩, hxpos⟩ := ((hevB.and hdiv).and self_mem_nhdsWithin).exists
  have hx0 : (0 : ℝ) < x := hxpos
  have hy : (1 : ℝ) < 1 + x := by linarith
  have hA : ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + x))
      ≤ Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ))‖ := tsum_rpow_le_log_norm_riemannZeta hy
  have hcomp := log_norm_riemannZeta_sub_le hy hS
  have hlogB : Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Real.log B := by
    rcases eq_or_lt_of_le (norm_nonneg (riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I))) with h | h
    · rw [← h, Real.log_zero]; exact Real.log_nonneg hB1
    · exact Real.log_le_log h hxB
  rw [← hSdef] at hcomp
  linarith

/-- **`f` is pretentious to no `n^{it}` with `t ≠ 0`.**  For a `{±1}`-valued multiplicative `f`
and `t ≠ 0`,
$$\sum_p \frac{1 - f(p)\cos(t\log p)}{p} = \infty.$$

This needs no hypothesis on `f` beyond `f(p) = ±1`: the values being *signs* rather than
phases is exactly what makes `f(p)^2 = 1`, so the divergence at `2t` transfers to `t`. -/
@[category API, AMS 11]
theorem not_summable_one_sub_mul_cos (f : ℕ → ℝ) (hf : IsPMOneMultiplicative f) {t : ℝ}
    (ht : t ≠ 0) :
    ¬ Summable fun p : Nat.Primes ↦ (1 - f p * Real.cos (t * Real.log p)) / p := by
  intro hS
  refine not_summable_one_sub_cos (t := 2 * t) (by simpa using ht) ?_
  have hppos : ∀ p : Nat.Primes, (0 : ℝ) < (p : ℝ) := fun p ↦ by exact_mod_cast p.2.pos
  refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_) (hS.mul_left 4)
  · have := Real.cos_le_one (2 * t * Real.log (p : ℝ))
    have := hppos p
    positivity
  · have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
    have hε := hf.pmOne (p : ℕ) hp1
    have hkey := one_sub_cos_two_mul_le (θ := t * Real.log (p : ℝ)) (ε := f p) hε
    rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring] at hkey
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (hppos p)]
    linarith

/-- The uniform non-pretentiousness that the divergent case of Wirsing's theorem provides:
if `∑_p (1 - f(p))/p` diverges, then so does `∑_p (1 - f(p)\cos(t\log p))/p` for **every**
real `t`.  The case `t = 0` is the hypothesis itself; the others come from the pole of `ζ`
at `1`.

This is the input that a Halász-type endgame needs, and the place where `f` real-valued
enters the proof of Wirsing's theorem. -/
@[category API, AMS 11]
theorem not_summable_one_sub_mul_cos_of_not_summable (f : ℕ → ℝ) (hf : IsPMOneMultiplicative f)
    (h0 : ¬ Summable (pretentiousSeries f)) (t : ℝ) :
    ¬ Summable fun p : Nat.Primes ↦ (1 - f p * Real.cos (t * Real.log p)) / p := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact fun h ↦ h0 (h.congr fun p ↦ by simp [pretentiousSeries])
  · exact not_summable_one_sub_mul_cos f hf ht

end Wirsing
