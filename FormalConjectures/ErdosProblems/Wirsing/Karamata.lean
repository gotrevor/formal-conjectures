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
      ring
    rw [hint, show c * (r / ((k : ℝ) + 1)) = r * (c / ((k : ℝ) + 1)) by ring]
    refine ((tendsto_functional_pow ha0 hlim k).const_mul r).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    simp only [Polynomial.eval_monomial]
    exact (functional_const_mul r (fun u ↦ u ^ k)).symm

/-- The Karamata functional is subtractive in `g`. -/
@[category API, AMS 11]
theorem functional_sub (ha : ∀ n, 0 ≤ a n) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {g h : ℝ → ℝ} {M M' : ℝ}
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |g u| ≤ M) (hh : ∀ u ∈ Set.Icc (0 : ℝ) 1, |h u| ≤ M') :
    functional a x (fun u ↦ g u - h u) = functional a x g - functional a x h := by
  have hneg : ∀ u ∈ Set.Icc (0 : ℝ) 1, |(-1 : ℝ) * h u| ≤ M' := by
    intro u hu; simpa using hh u hu
  have := functional_add ha hx hsum hg hneg
  rw [functional_const_mul (-1 : ℝ) h] at this
  simpa [sub_eq_add_neg] using this

/--
**Karamata's limit for continuous test functions.**  If `x S(x) → c` then
`Λ_x(g) → c\int_0^1 g` for every `g` continuous on `[0,1]`.

Weierstrass approximation plus the uniform bound `|Λ_x(g)| ≤ ‖g‖_∞ · x S(x)`.
-/
@[category API, AMS 11]
theorem tendsto_functional_continuousOn (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c)) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    Tendsto (fun x ↦ functional a x g) (𝓝[>] (0 : ℝ))
      (𝓝 (c * ∫ u in (0 : ℝ)..1, g u)) := by
  obtain ⟨Mg, hMg⟩ := exists_bound_of_continuousOn hg
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    hg.intervalIntegrable_of_Icc zero_le_one
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set K := |c| + 2 with hK
  have hKpos : 0 < K := by positivity
  set δ := ε / (3 * K) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg δ hδpos
  obtain ⟨MP, hMP⟩ := exists_bound_of_continuousOn (g := fun u ↦ P.eval u)
    P.continuous.continuousOn
  -- the polynomial limit
  have hpoly := tendsto_functional_polynomial ha ha0 hsum hlim P
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      |functional a x (fun u ↦ P.eval u) - c * ∫ u in (0 : ℝ)..1, P.eval u| < ε / 3 :=
    Metric.tendsto_nhds.1 hpoly (ε / 3) (by positivity)
  have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), |x * series a x| < K := by
    have := Metric.tendsto_nhds.1 hlim 1 one_pos
    filter_upwards [this] with x hx
    have : |x * series a x - c| < 1 := hx
    have h1 := abs_sub_abs_le_abs_sub (x * series a x) c
    have h2 : |c| ≤ |c| := le_refl _
    calc |x * series a x| ≤ |c| + 1 := by linarith [abs_sub_abs_le_abs_sub (x * series a x) c]
      _ < K := by rw [hK]; linarith
  -- the integral comparison
  have hintdiff : |(∫ u in (0 : ℝ)..1, P.eval u) - ∫ u in (0 : ℝ)..1, g u| ≤ δ := by
    rw [← intervalIntegral.integral_sub (P.continuous.intervalIntegrable 0 1) hgint]
    have hbd : ∀ u ∈ Set.uIoc (0 : ℝ) 1, ‖P.eval u - g u‖ ≤ δ := by
      intro u hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      exact le_of_lt (hP u ⟨le_of_lt hu.1, hu.2⟩)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with x h1 h2 hx
  have hxpos : (0 : ℝ) < x := hx
  -- |Λ_x(g) - Λ_x(P)| ≤ δ · x S(x)
  have hdiff : |functional a x g - functional a x (fun u ↦ P.eval u)| ≤ δ * (x * series a x) := by
    rw [← functional_sub ha hxpos (hsum x hxpos) hMg hMP]
    refine abs_functional_le ha hxpos (hsum x hxpos) (M := δ) fun u hu ↦ ?_
    rw [abs_sub_comm]
    exact le_of_lt (hP u hu)
  have hSnn : 0 ≤ x * series a x := by
    refine mul_nonneg hxpos.le (tsum_nonneg fun n ↦ ?_)
    exact mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hdiff2 : |functional a x g - functional a x (fun u ↦ P.eval u)| < ε / 3 := by
    have h3 : x * series a x < K := lt_of_le_of_lt (le_abs_self _) h2
    have hδK : δ * K = ε / 3 := by rw [hδ]; field_simp
    nlinarith [hdiff, hδpos, hSnn]
  have hintdiff2 : |c * (∫ u in (0 : ℝ)..1, P.eval u) - c * ∫ u in (0 : ℝ)..1, g u| < ε / 3 := by
    rw [← mul_sub, abs_mul]
    have hlt : |c| < K := by rw [hK]; linarith [abs_nonneg c]
    have hδK : K * δ = ε / 3 := by rw [hδ]; field_simp
    nlinarith [hintdiff, abs_nonneg c, abs_nonneg ((∫ u in (0 : ℝ)..1, P.eval u) -
      ∫ u in (0 : ℝ)..1, g u), hδpos]
  rw [Real.dist_eq]
  have t1 := abs_sub_le (functional a x g) (functional a x (fun u ↦ P.eval u))
    (c * ∫ u in (0 : ℝ)..1, g u)
  have t2 := abs_sub_le (functional a x (fun u ↦ P.eval u))
    (c * ∫ u in (0 : ℝ)..1, P.eval u) (c * ∫ u in (0 : ℝ)..1, g u)
  linarith

/-! ### The discontinuous test function and its continuous brackets -/

/-- The test function `u \mapsto u^{-1}\mathbf 1_{[\theta,1]}(u)`, whose Karamata value is
`x\sum_{n \le \theta^{-1/x}} a_n`. -/
noncomputable def testFun (θ u : ℝ) : ℝ := if θ ≤ u then 1 / u else 0

/-- A continuous function below `Karamata.testFun θ`, rising from `0` to `u^{-1}` on
`[θ, θ+η]`. -/
noncomputable def bracketLow (θ η u : ℝ) : ℝ :=
  min 1 (max 0 ((u - θ) / η)) / max u (θ / 2)

/-- A continuous function above `Karamata.testFun θ`, rising from `0` to `u^{-1}` on
`[θ-η, θ]`. -/
noncomputable def bracketHigh (θ η u : ℝ) : ℝ :=
  min 1 (max 0 ((u - θ + η) / η)) / max u (θ / 2)

@[category API, AMS 11]
theorem continuous_bracketLow {θ η : ℝ} (hθ : 0 < θ) (_hη : 0 < η) :
    Continuous (bracketLow θ η) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_
  have : θ / 2 ≤ max u (θ / 2) := le_max_right _ _
  positivity

@[category API, AMS 11]
theorem continuous_bracketHigh {θ η : ℝ} (hθ : 0 < θ) (_hη : 0 < η) :
    Continuous (bracketHigh θ η) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun u ↦ ?_
  have : θ / 2 ≤ max u (θ / 2) := le_max_right _ _
  positivity

@[category API, AMS 11]
theorem bracketLow_nonneg {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : 0 ≤ bracketLow θ η u := by
  have hd : 0 < max u (θ / 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  exact div_nonneg (le_min zero_le_one (le_max_left _ _)) hd.le

@[category API, AMS 11]
theorem bracketHigh_nonneg {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : 0 ≤ bracketHigh θ η u := by
  have hd : 0 < max u (θ / 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  exact div_nonneg (le_min zero_le_one (le_max_left _ _)) hd.le

/-- The shape shared by the two brackets: `r / \max(u, θ/2) \le 2/θ` for `r \in [0,1]`. -/
@[category API, AMS 11]
theorem div_max_le {θ : ℝ} (hθ : 0 < θ) {r u : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r / max u (θ / 2) ≤ 2 / θ := by
  have hd : θ / 2 ≤ max u (θ / 2) := le_max_right _ _
  have hd0 : (0 : ℝ) < θ / 2 := by positivity
  rw [div_le_div_iff₀ (lt_of_lt_of_le hd0 hd) hθ]
  nlinarith

@[category API, AMS 11]
theorem bracketLow_le {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : bracketLow θ η u ≤ 2 / θ :=
  div_max_le hθ (le_min zero_le_one (le_max_left _ _)) (min_le_left _ _)

@[category API, AMS 11]
theorem bracketHigh_le {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : bracketHigh θ η u ≤ 2 / θ :=
  div_max_le hθ (le_min zero_le_one (le_max_left _ _)) (min_le_left _ _)

@[category API, AMS 11]
theorem abs_bracketLow_le {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : |bracketLow θ η u| ≤ 2 / θ := by
  rw [abs_of_nonneg (bracketLow_nonneg hθ u)]; exact bracketLow_le hθ u

@[category API, AMS 11]
theorem abs_bracketHigh_le {θ η : ℝ} (hθ : 0 < θ) (u : ℝ) : |bracketHigh θ η u| ≤ 2 / θ := by
  rw [abs_of_nonneg (bracketHigh_nonneg hθ u)]; exact bracketHigh_le hθ u

/-- The lower bracket is below the test function. -/
@[category API, AMS 11]
theorem bracketLow_le_testFun {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (u : ℝ) :
    bracketLow θ η u ≤ testFun θ u := by
  rcases lt_or_ge u θ with hu | hu
  · have : (u - θ) / η < 0 := div_neg_of_neg_of_pos (by linarith) hη
    have hmax : max 0 ((u - θ) / η) = 0 := max_eq_left this.le
    simp [bracketLow, testFun, hmax, not_le.2 hu]
  · have hmaxu : max u (θ / 2) = u := max_eq_left (by linarith)
    have hnum : min 1 (max 0 ((u - θ) / η)) ≤ 1 := min_le_left _ _
    simp only [bracketLow, testFun, if_pos hu, hmaxu]
    rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < u)]
    exact hnum

/-- The test function is below the upper bracket. -/
@[category API, AMS 11]
theorem testFun_le_bracketHigh {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (u : ℝ) :
    testFun θ u ≤ bracketHigh θ η u := by
  rcases lt_or_ge u θ with hu | hu
  · simp only [testFun, if_neg (not_le.2 hu)]
    exact bracketHigh_nonneg hθ u
  · have hmaxu : max u (θ / 2) = u := max_eq_left (by linarith)
    have h1 : 1 ≤ (u - θ + η) / η := by
      rw [le_div_iff₀ hη]; linarith
    have hnum : min 1 (max 0 ((u - θ + η) / η)) = 1 :=
      min_eq_left (le_max_of_le_right h1)
    simp [bracketHigh, testFun, if_pos hu, hmaxu, hnum]

/-! ### Integrals of the brackets -/

/-- On `[θ+η, 1]` the lower bracket is exactly `u^{-1}`. -/
@[category API, AMS 11]
theorem bracketLow_eq {θ η u : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hu : θ + η ≤ u) :
    bracketLow θ η u = 1 / u := by
  have h1 : (1 : ℝ) ≤ (u - θ) / η := by rw [le_div_iff₀ hη]; linarith
  have hmaxu : max u (θ / 2) = u := max_eq_left (by linarith)
  simp [bracketLow, hmaxu, min_eq_left (le_max_of_le_right h1)]

/-- On `[0, θ-η]` the upper bracket vanishes. -/
@[category API, AMS 11]
theorem bracketHigh_eq_zero {θ η u : ℝ} (hη : 0 < η) (hu : u ≤ θ - η) :
    bracketHigh θ η u = 0 := by
  have h1 : (u - θ + η) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  simp [bracketHigh, max_eq_left h1]

/-- Off `[0, θ-η]` the upper bracket is at most `u^{-1}`. -/
@[category API, AMS 11]
theorem bracketHigh_le_inv {θ η u : ℝ} (hθ : 0 < θ) (hη : η < θ / 2) (hu : θ - η ≤ u) :
    bracketHigh θ η u ≤ 1 / u := by
  have hupos : 0 < u := by linarith
  have hmaxu : max u (θ / 2) = u := max_eq_left (by linarith)
  simp only [bracketHigh, hmaxu]
  rw [div_le_div_iff_of_pos_right hupos]
  exact min_le_left _ _

/-- The integral of the lower bracket is at least `-\log(θ+η)`. -/
@[category API, AMS 11]
theorem integral_bracketLow_ge {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hsum1 : θ + η ≤ 1) :
    -Real.log (θ + η) ≤ ∫ u in (0 : ℝ)..1, bracketLow θ η u := by
  have hcont := continuous_bracketLow hθ hη
  have hsplit : (∫ u in (0 : ℝ)..1, bracketLow θ η u)
      = (∫ u in (0 : ℝ)..(θ + η), bracketLow θ η u)
        + ∫ u in (θ + η)..1, bracketLow θ η u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have h1 : 0 ≤ ∫ u in (0 : ℝ)..(θ + η), bracketLow θ η u :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ ↦ bracketLow_nonneg hθ u
  have h2 : (∫ u in (θ + η)..1, bracketLow θ η u) = Real.log (1 / (θ + η)) := by
    rw [← integral_one_div (Set.notMem_uIcc_of_lt (by linarith : (0:ℝ) < θ + η)
      (by linarith : (0:ℝ) < 1))]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [Set.uIcc_of_le hsum1] at hu
    exact bracketLow_eq hθ hη hu.1
  have h4 : Real.log (1 / (θ + η)) = -Real.log (θ + η) := by
    rw [Real.log_div one_ne_zero (by linarith), Real.log_one]; ring
  rw [hsplit, h2, h4]
  linarith

/-- The integral of the upper bracket is at most `-\log(θ-η)`. -/
@[category API, AMS 11]
theorem integral_bracketHigh_le {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hηθ : η < θ / 2)
    (hθ1 : θ ≤ 1) :
    (∫ u in (0 : ℝ)..1, bracketHigh θ η u) ≤ -Real.log (θ - η) := by
  have hcont := continuous_bracketHigh hθ hη
  have hd : 0 < θ - η := by linarith
  have hd1 : θ - η ≤ 1 := by linarith
  have hsplit : (∫ u in (0 : ℝ)..1, bracketHigh θ η u)
      = (∫ u in (0 : ℝ)..(θ - η), bracketHigh θ η u)
        + ∫ u in (θ - η)..1, bracketHigh θ η u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have h1 : (∫ u in (0 : ℝ)..(θ - η), bracketHigh θ η u) = 0 := by
    have hz : Set.EqOn (bracketHigh θ η) (fun _ ↦ (0 : ℝ)) (Set.uIcc (0 : ℝ) (θ - η)) := by
      intro u hu
      rw [Set.uIcc_of_le hd.le] at hu
      exact bracketHigh_eq_zero hη hu.2
    rw [intervalIntegral.integral_congr hz]
    simp
  have hinvint : IntervalIntegrable (fun u : ℝ ↦ 1 / u) MeasureTheory.volume (θ - η) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hd1]
    exact continuousOn_const.div continuousOn_id fun u hu ↦ ne_of_gt (lt_of_lt_of_le hd hu.1)
  have h2 : (∫ u in (θ - η)..1, bracketHigh θ η u) ≤ ∫ u in (θ - η)..1, 1 / u := by
    refine intervalIntegral.integral_mono_on hd1 (hcont.intervalIntegrable _ _) hinvint ?_
    intro u hu
    exact bracketHigh_le_inv hθ hηθ hu.1
  have h3 : (∫ u in (θ - η)..1, (1 : ℝ) / u) = Real.log (1 / (θ - η)) :=
    integral_one_div (Set.notMem_uIcc_of_lt hd (by linarith : (0:ℝ) < 1))
  have h4 : Real.log (1 / (θ - η)) = -Real.log (θ - η) := by
    rw [Real.log_div one_ne_zero (by linarith), Real.log_one]; ring
  rw [hsplit, h1, zero_add]
  rw [h3, h4] at h2
  linarith

/-! ### The Karamata value of the test function -/

/-- For `n ≥ 1` the point `n^{-x}` lies above `θ` exactly when `n ≤ (1/θ)^{1/x}`. -/
@[category API, AMS 11]
theorem le_rpow_neg_iff {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    θ ≤ (n : ℝ) ^ (-x) ↔ (n : ℝ) ≤ (1 / θ) ^ (1 / x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxx : x ≠ 0 := ne_of_gt hx
  have hpx : (0 : ℝ) < (n : ℝ) ^ x := Real.rpow_pos_of_pos hn0 x
  have hrn : ((n : ℝ) ^ x) ^ (1 / x) = (n : ℝ) := by
    rw [← Real.rpow_mul hn0.le, mul_one_div, div_self hxx, Real.rpow_one]
  have hrb : ((1 / θ) ^ (1 / x)) ^ x = 1 / θ := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hxx, Real.rpow_one]
  rw [Real.rpow_neg hn0.le, le_inv_comm₀ hθ hpx]
  constructor
  · intro h
    calc (n : ℝ) = ((n : ℝ) ^ x) ^ (1 / x) := hrn.symm
      _ ≤ (1 / θ) ^ (1 / x) := by
          refine Real.rpow_le_rpow hpx.le ?_ (by positivity)
          rwa [one_div]
  · intro h
    calc (n : ℝ) ^ x ≤ ((1 / θ) ^ (1 / x)) ^ x := Real.rpow_le_rpow hn0.le h hx.le
      _ = 1 / θ := hrb
      _ = θ⁻¹ := one_div θ

/--
**The Karamata value of the test function.**  `Λ_x(\mathrm{testFun}\ θ)` is exactly the
partial sum `x\sum_{n \le (1/θ)^{1/x}} a_n`.
-/
@[category API, AMS 11]
theorem functional_testFun (ha0 : a 0 = 0) {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    functional a x (testFun θ) = x * ∑ n ∈ Finset.Icc 1 ⌊(1 / θ) ^ (1 / x)⌋₊, a n := by
  set B := (1 / θ) ^ (1 / x) with hB
  have hB0 : (0 : ℝ) ≤ B := Real.rpow_nonneg (by positivity) _
  have hmem : ∀ n : ℕ, 1 ≤ n →
      (n ∈ Finset.Icc 1 ⌊B⌋₊ ↔ θ ≤ (n : ℝ) ^ (-x)) := by
    intro n hn
    rw [Finset.mem_Icc, le_rpow_neg_iff hθ hx hn, Nat.le_floor_iff hB0]
    simp [hn, hB]
  have hzero : ∀ n ∉ Finset.Icc 1 ⌊B⌋₊,
      a n * (n : ℝ) ^ (-x) * testFun θ ((n : ℝ) ^ (-x)) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp [ha0]
    · have : ¬ θ ≤ (n : ℝ) ^ (-x) := fun h ↦ hn ((hmem n hn1).2 h)
      simp [testFun, this]
  have heq : ∀ n ∈ Finset.Icc 1 ⌊B⌋₊,
      a n * (n : ℝ) ^ (-x) * testFun θ ((n : ℝ) ^ (-x)) = a n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) ^ (-x) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
    have hle : θ ≤ (n : ℝ) ^ (-x) := (hmem n hn1).1 hn
    rw [testFun, if_pos hle]
    field_simp
  rw [functional, tsum_eq_sum hzero, Finset.sum_congr rfl heq]

/-! ### The pinch -/

/-- `\log(θ+η) - \log θ \le η/θ`. -/
@[category API, AMS 11]
theorem log_add_sub_le {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    Real.log (θ + η) - Real.log θ ≤ η / θ := by
  have h1 : Real.log (θ + η) - Real.log θ = Real.log ((θ + η) / θ) := by
    rw [Real.log_div (by linarith) (ne_of_gt hθ)]
  rw [h1]
  have := Real.log_le_sub_one_of_pos (x := (θ + η) / θ) (by positivity)
  have h2 : (θ + η) / θ - 1 = η / θ := by field_simp; ring
  linarith

/-- `\log θ - \log(θ-η) \le 2η/θ` when `η ≤ θ/2`. -/
@[category API, AMS 11]
theorem log_sub_sub_le {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (h : η ≤ θ / 2) :
    Real.log θ - Real.log (θ - η) ≤ 2 * η / θ := by
  have hd : 0 < θ - η := by linarith
  have h1 : Real.log θ - Real.log (θ - η) = Real.log (θ / (θ - η)) := by
    rw [Real.log_div (ne_of_gt hθ) (ne_of_gt hd)]
  rw [h1]
  have h2 := Real.log_le_sub_one_of_pos (x := θ / (θ - η)) (by positivity)
  have h3 : θ / (θ - η) - 1 = η / (θ - η) := by field_simp; ring
  have h4 : η / (θ - η) ≤ 2 * η / θ := by
    rw [div_le_div_iff₀ hd hθ]
    nlinarith
  linarith

/-- The test function is bounded by `1/θ` on `[0,1]`. -/
@[category API, AMS 11]
theorem abs_testFun_le {θ : ℝ} (hθ : 0 < θ) {u : ℝ} (_hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |testFun θ u| ≤ 1 / θ := by
  rcases lt_or_ge u θ with h | h
  · simp only [testFun, if_neg (not_le.2 h), abs_zero]
    positivity
  · have hupos : 0 < u := lt_of_lt_of_le hθ h
    rw [testFun, if_pos h, abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hθ h

/--
**Karamata's pinch.**  `Λ_x(\mathrm{testFun}\ θ) → c\cdot(-\log θ)`.

The test function is squeezed between the two continuous brackets, whose Karamata limits are
`c\int_0^1` of them, and those integrals converge to `-\log θ` as the bracket width `η → 0`.
-/
@[category API, AMS 11]
theorem tendsto_functional_testFun (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (fun x ↦ functional a x (testFun θ)) (𝓝[>] (0 : ℝ))
      (𝓝 (c * -Real.log θ)) := by
  have hc0 : 0 ≤ c := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hs : 0 ≤ series a x :=
      tsum_nonneg fun n ↦ mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact mul_nonneg (le_of_lt hx) hs
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set L := c * -Real.log θ with hL
  -- choose the bracket width
  set η := min (min (θ / 4) ((1 - θ) / 2)) (ε * θ / (4 * (c + 1))) with hηdef
  have hη : 0 < η := by
    refine lt_min (lt_min (by positivity) (by linarith)) (by positivity)
  have hη4 : η ≤ θ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη1 : θ + η ≤ 1 := by
    have : η ≤ (1 - θ) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hηε : η ≤ ε * θ / (4 * (c + 1)) := min_le_right _ _
  have hηθ : η < θ / 2 := by linarith
  -- the key numerical consequence: `c·η/θ ≤ ε/4`
  have hkey : c * (η / θ) ≤ ε / 4 := by
    have hc1 : (0 : ℝ) < 4 * (c + 1) := by positivity
    have hmul : η * (4 * (c + 1)) ≤ ε * θ := (le_div_iff₀ hc1).1 hηε
    rw [mul_div_assoc', div_le_div_iff₀ hθ0 (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hη.le, hc0]
  -- integral bounds
  have hIL : c * -Real.log (θ + η) ≤ c * ∫ u in (0 : ℝ)..1, bracketLow θ η u :=
    mul_le_mul_of_nonneg_left (integral_bracketLow_ge hθ0 hη hη1) hc0
  have hIH : c * (∫ u in (0 : ℝ)..1, bracketHigh θ η u) ≤ c * -Real.log (θ - η) :=
    mul_le_mul_of_nonneg_left (integral_bracketHigh_le hθ0 hη hηθ hθ1.le) hc0
  have hAL : L - ε / 4 ≤ c * -Real.log (θ + η) := by
    have hd := log_add_sub_le hθ0 hη
    have hmul := mul_le_mul_of_nonneg_left hd hc0
    have hexp := mul_sub c (Real.log (θ + η)) (Real.log θ)
    rw [hL]
    simp only [mul_neg]
    linarith
  have hAH : c * -Real.log (θ - η) ≤ L + ε / 2 := by
    have hd := log_sub_sub_le hθ0 hη (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hd hc0
    have hexp := mul_sub c (Real.log θ) (Real.log (θ - η))
    have hdiv : c * (2 * η / θ) = 2 * (c * (η / θ)) := by ring
    rw [hL]
    simp only [mul_neg]
    linarith
  -- the two bracket limits
  have hbL := tendsto_functional_continuousOn ha ha0 hsum hlim
    (g := bracketLow θ η) (continuous_bracketLow hθ0 hη).continuousOn
  have hbH := tendsto_functional_continuousOn ha ha0 hsum hlim
    (g := bracketHigh θ η) (continuous_bracketHigh hθ0 hη).continuousOn
  have hevL := Metric.tendsto_nhds.1 hbL (ε / 4) (by positivity)
  have hevH := Metric.tendsto_nhds.1 hbH (ε / 4) (by positivity)
  filter_upwards [hevL, hevH, self_mem_nhdsWithin] with x hxL hxH hx
  have hxpos : (0 : ℝ) < x := hx
  rw [Real.dist_eq] at hxL hxH ⊢
  have hmL : functional a x (bracketLow θ η) ≤ functional a x (testFun θ) :=
    functional_mono ha hxpos (hsum x hxpos) (M := 2 / θ) (M' := 1 / θ)
      (fun u _ ↦ abs_bracketLow_le hθ0 u) (fun u hu ↦ abs_testFun_le hθ0 hu)
      (fun u _ ↦ bracketLow_le_testFun hθ0 hη u)
  have hmH : functional a x (testFun θ) ≤ functional a x (bracketHigh θ η) :=
    functional_mono ha hxpos (hsum x hxpos) (M := 1 / θ) (M' := 2 / θ)
      (fun u hu ↦ abs_testFun_le hθ0 hu) (fun u _ ↦ abs_bracketHigh_le hθ0 u)
      (fun u _ ↦ testFun_le_bracketHigh hθ0 hη u)
  have h1 := abs_lt.1 hxL
  have h2 := abs_lt.1 hxH
  rw [abs_lt]
  constructor
  · linarith [h1.1, hIL, hAL, hmL]
  · linarith [h2.2, hIH, hAH, hmH]

/--
**Karamata's Tauberian theorem** (`x`-form).  If `a_n ≥ 0` and `x S(x) → c` as `x → 0⁺`, then
`x\sum_{n \le e^{1/x}} a_n → c`.
-/
@[category API, AMS 11]
theorem tendsto_partialSum (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun x ↦ x * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (1 / x)⌋₊, a n)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  set θ := Real.exp (-1) with hθ
  have hθ0 : 0 < θ := Real.exp_pos _
  have hθ1 : θ < 1 := by rw [hθ]; exact Real.exp_lt_one_iff.2 (by norm_num)
  have hlog : c * -Real.log θ = c := by rw [hθ, Real.log_exp]; ring
  have hmain := tendsto_functional_testFun ha ha0 hsum hlim hθ0 hθ1
  rw [hlog] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : (0 : ℝ) < x := hx
  have hinv : 1 / θ = Real.exp 1 := by
    rw [hθ, Real.exp_neg]; simp
  have hpow : (1 / θ) ^ (1 / x) = Real.exp (1 / x) := by
    rw [hinv, Real.exp_one_rpow]
  rw [functional_testFun ha0 hθ0 hxpos, hpow]

/--
**Karamata's Tauberian theorem** (`V`-form).  `(\sum_{n \le e^V} a_n)/V → c` as `V → ∞`.
-/
@[category API, AMS 11]
theorem tendsto_partialSum_div (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-x))) {c : ℝ}
    (hlim : Tendsto (fun x ↦ x * series a x) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun V ↦ (∑ n ∈ Finset.Icc 1 ⌊Real.exp V⌋₊, a n) / V) atTop (𝓝 c) := by
  have hcomp : Tendsto (fun V : ℝ ↦ 1 / V) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa [one_div] using tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
      show (0 : ℝ) < 1 / V
      positivity
  have := (tendsto_partialSum ha ha0 hsum hlim).comp hcomp
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  have h1 : 1 / (1 / V) = V := by field_simp
  simp only [Function.comp_apply, h1]
  ring

end Karamata
