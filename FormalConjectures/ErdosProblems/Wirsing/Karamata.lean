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
# Karamata's Tauberian theorem for Dirichlet series

If `a n ≥ 0` and the Dirichlet series `S(x) = ∑_n a_n n^{-x}` satisfies `x S(x) → c` as
`x → 0⁺`, then `∑_{n ≤ e^V} a_n ∼ cV`.

This is Karamata's Tauberian theorem in the form needed for Erdős 239.  Applied to
`a_n = (Λ(n)/n)(1 - \cos(t\log n))`, whose transform is `1/x + O_t(1)` by
`Wirsing.exists_abs_tsum_vonMangoldt_twisted_sub_le`, it gives
$$\sum_{p \le N} \frac{\log p}{p}\cos(t\log p) = o(\log N) \qquad (t \ne 0),$$
the estimate that the resonance step of the crux needs.

The proof is the classical one and uses no measure theory.  Write
`Λ_x(g) = x ∑_n a_n n^{-x} g(n^{-x})`, a positive linear functional on `C[0,1]` (the points
`n^{-x}` lie in `(0,1]`).  On the monomial `u^k` it is `((k+1)x S((k+1)x))/(k+1)`, which tends
to `c/(k+1) = c∫_0^1 u^k du`; by Weierstrass approximation and positivity, `Λ_x(g) → c∫_0^1 g`
for every continuous `g`.  Taking `g` to be a continuous approximation of
`u \mapsto u^{-1}\mathbf 1_{[e^{-1},1]}(u)` — whose value under `Λ_x` is exactly
`x\sum_{n \le e^{1/x}} a_n` — gives the conclusion.

*References:*
- [Ka31] Karamata, J., Neuer Beweis und Verallgemeinerung der Tauberschen Sätze.
  Math. Z. 33 (1931), 294-299.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Karamata

variable (a : ℕ → ℝ)

/-- The Karamata functional `Λ_x(g) = x ∑_n a_n n^{-x} g(n^{-x})`. -/
noncomputable def functional (x : ℝ) (g : ℝ → ℝ) : ℝ :=
  x * ∑' n : ℕ, a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))

/-- The Dirichlet series `S(x) = ∑_n a_n n^{-x}`. -/
noncomputable def series (x : ℝ) : ℝ := ∑' n : ℕ, a n * (n : ℝ) ^ (-x)

variable {a}

/-- The points `n^{-x}` of the Karamata functional lie in `[0,1]` for `x > 0`. -/
@[category API, AMS 11]
theorem rpow_neg_mem_Icc {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (n : ℝ) ^ (-x) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg n) _, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [show (-x) = -x from rfl]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

/-- On the monomial `u ^ k` the Karamata functional is an explicit rescaling of the series. -/
@[category API, AMS 11]
theorem functional_pow (ha0 : a 0 = 0) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    functional a x (fun u ↦ u ^ k)
      = (((k : ℝ) + 1) * x * series a (((k : ℝ) + 1) * x)) / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcongr : ∀ n : ℕ, a n * (n : ℝ) ^ (-x) * ((n : ℝ) ^ (-x)) ^ k
      = a n * (n : ℝ) ^ (-(((k : ℝ) + 1) * x)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-x)) k, ← Real.rpow_mul hn0.le, mul_assoc,
        ← Real.rpow_add hn0]
      congr 2
      ring
  rw [functional, series]
  simp only [hcongr]
  field_simp

/-- Summability of the Karamata sum for a bounded `g`. -/
@[category API, AMS 11]
theorem summable_term (ha : ∀ n, 0 ≤ a n) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {g : ℝ → ℝ} {M : ℝ}
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M) :
    Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))) := by
  refine Summable.of_norm_bounded (hsum.mul_left M) fun n ↦ ?_
  have h1 : 0 ≤ a n * (n : ℝ) ^ (-x) :=
    mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hg _ (rpow_neg_mem_Icc hx n)) h1

/-- The Karamata functional is linear in `g` (additivity). -/
@[category API, AMS 11]
theorem functional_add (ha : ∀ n, 0 ≤ a n) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {g h : ℝ → ℝ} {M M' : ℝ}
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M) (hh : ∀ u ∈ Set.Icc (0 : ℝ) 1, |h u| ≤ M') :
    functional a x (fun u ↦ g u + h u) = functional a x g + functional a x h := by
  rw [functional, functional, functional, ← mul_add,
    ← (summable_term ha hx hsum hg).tsum_add (summable_term ha hx hsum hh)]
  congr 1
  exact tsum_congr fun n ↦ by ring

/-- The Karamata functional is linear in `g` (homogeneity). -/
@[category API, AMS 11]
theorem functional_const_mul {x : ℝ} (r : ℝ) (g : ℝ → ℝ) :
    functional a x (fun u ↦ r * g u) = r * functional a x g := by
  have hkey : ∑' n : ℕ, a n * (n : ℝ) ^ (-x) * (r * g ((n : ℝ) ^ (-x)))
      = r * ∑' n : ℕ, a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ by ring
  rw [functional, functional, hkey]
  ring

/-- The Karamata functional is monotone in `g`. -/
@[category API, AMS 11]
theorem functional_mono (ha : ∀ n, 0 ≤ a n) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {g h : ℝ → ℝ} {M M' : ℝ}
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M) (hh : ∀ u ∈ Set.Icc (0 : ℝ) 1, |h u| ≤ M')
    (hgh : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≤ h u) :
    functional a x g ≤ functional a x h := by
  rw [functional, functional]
  refine mul_le_mul_of_nonneg_left ?_ hx.le
  refine (summable_term ha hx hsum hg).tsum_le_tsum (fun n ↦ ?_) (summable_term ha hx hsum hh)
  have h1 : 0 ≤ a n * (n : ℝ) ^ (-x) :=
    mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact mul_le_mul_of_nonneg_left (hgh _ (rpow_neg_mem_Icc hx n)) h1

/-- A uniform bound for `g` on `[0,1]` gives a bound for the Karamata functional. -/
@[category API, AMS 11]
theorem abs_functional_le (ha : ∀ n, 0 ≤ a n) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {g : ℝ → ℝ} {M : ℝ}
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M) :
    |functional a x g| ≤ M * (x * series a x) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hg 1 ⟨zero_le_one, le_refl 1⟩)
  rw [functional, abs_mul, abs_of_nonneg hx.le, series, ← mul_assoc, mul_comm M x, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hx.le
  have habs : Summable (fun n : ℕ ↦ ‖a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))‖) :=
    (summable_term ha hx hsum hg).abs
  calc |∑' n : ℕ, a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))|
      ≤ ∑' n : ℕ, ‖a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ, M * (a n * (n : ℝ) ^ (-x)) := by
        refine habs.tsum_le_tsum (fun n ↦ ?_) (hsum.mul_left M)
        have h1 : 0 ≤ a n * (n : ℝ) ^ (-x) :=
          mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hg _ (rpow_neg_mem_Icc hx n)) h1
    _ = M * ∑' n : ℕ, a n * (n : ℝ) ^ (-x) := tsum_mul_left

/-- A continuous function is bounded on `[0,1]`. -/
@[category API, AMS 11]
theorem exists_bound_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∃ M : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨M, fun u hu ↦ by simpa [Real.norm_eq_abs] using hM u hu⟩

/-- **The monomial limit.**  `Λ_x(u^k) → c/(k+1) = c∫_0^1 u^k`. -/
@[category API, AMS 11]
theorem tendsto_functional_pow (ha0 : a 0 = 0) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c)) (k : ℕ) :
    Tendsto (fun x ↦ functional a x (fun u ↦ u ^ k)) (𝓝[>] (0 : ℝ))
      (𝓝 (c / ((k : ℝ) + 1))) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hscale : Tendsto (fun x : ℝ ↦ ((k : ℝ) + 1) * x) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun x : ℝ ↦ ((k : ℝ) + 1) * x) (𝓝 0) (𝓝 (((k : ℝ) + 1) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx using mul_pos hk1 hx
  refine ((hlim.comp hscale).div_const ((k : ℝ) + 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (functional_pow ha0 hx k).symm

/-- **The polynomial limit.**  `Λ_x(P) → c∫_0^1 P`. -/
@[category API, AMS 11]
theorem tendsto_functional_polynomial (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c)) (P : Polynomial ℝ) :
    Tendsto (fun x ↦ functional a x (fun u ↦ P.eval u)) (𝓝[>] (0 : ℝ))
      (𝓝 (c * ∫ u in (0 : ℝ)..1, P.eval u)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have hbp := exists_bound_of_continuousOn (g := fun u ↦ p.eval u) p.continuous.continuousOn
    have hbq := exists_bound_of_continuousOn (g := fun u ↦ q.eval u) q.continuous.continuousOn
    obtain ⟨Mp, hMp⟩ := hbp
    obtain ⟨Mq, hMq⟩ := hbq
    have hint : (∫ u in (0 : ℝ)..1, (p + q).eval u)
        = (∫ u in (0 : ℝ)..1, p.eval u) + ∫ u in (0 : ℝ)..1, q.eval u := by
      simp only [Polynomial.eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable 0 1)
        (q.continuous.intervalIntegrable 0 1)
    rw [hint, mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Polynomial.eval_add]
    exact (functional_add ha hx (hsum x hx) hMp hMq).symm
  | monomial k r =>
    have hint : (∫ u in (0 : ℝ)..1, (Polynomial.monomial k r).eval u) = r / ((k : ℝ) + 1) := by
      simp only [Polynomial.eval_monomial]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      ring
    rw [hint, show c * (r / ((k : ℝ) + 1)) = r * (c / ((k : ℝ) + 1)) by ring]
    refine ((tendsto_functional_pow ha0 hlim k).const_mul r).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    simp only [Polynomial.eval_monomial]
    exact (functional_const_mul r (fun u ↦ u ^ k)).symm

end Karamata
