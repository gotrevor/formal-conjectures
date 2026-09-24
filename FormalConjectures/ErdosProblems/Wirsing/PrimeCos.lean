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
public import FormalConjectures.ErdosProblems.Wirsing.Weighted
public import FormalConjectures.ErdosProblems.Wirsing.Karamata

/-!
# The prime cosine sum is `o(log N)`

For every fixed `t ≠ 0`,
$$\sum_{p \le N} \frac{\log p}{p}\cos(t\log p) = o(\log N).$$

This is the PNT-strength estimate that the resonance step of the Hildebrand crux needs.  The
proof combines `Wirsing.exists_abs_tsum_vonMangoldt_twisted_sub_le` (the two-sided bound
`∑_n Λ(n)n^{-(1+x)}(1-\cos(t\log n)) = 1/x + O_t(1)`, which rests on
`riemannZeta_ne_zero_of_one_le_re`) with `Karamata.tendsto_partialSum_div`, then subtracts
Mertens' first theorem and drops the proper prime powers.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-- The nonnegative von Mangoldt weight `Λ(n)/n·(1 - \cos(t\log n))`. -/
noncomputable def vmWeight (t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / n * (1 - Real.cos (t * Real.log n))

@[category API, AMS 11]
theorem vmWeight_nonneg (t : ℝ) (n : ℕ) : 0 ≤ vmWeight t n := by
  refine mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)) ?_
  linarith [Real.cos_le_one (t * Real.log n)]

@[category API, AMS 11]
theorem vmWeight_zero (t : ℝ) : vmWeight t 0 = 0 := by
  simp [vmWeight]

/-- The Dirichlet term of `Wirsing.vmWeight` is the twisted von Mangoldt term. -/
@[category API, AMS 11]
theorem vmWeight_mul_rpow (t x : ℝ) (n : ℕ) :
    vmWeight t n * (n : ℝ) ^ (-x)
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        (1 - Real.cos (t * Real.log n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vmWeight]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : (n : ℝ) ^ (-(1 + x)) = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-x) := by
      rw [← Real.rpow_add hn0]; ring_nf
    rw [vmWeight, hsplit, Real.rpow_neg_one]
    field_simp

/-- Summability of the `Wirsing.vmWeight` Dirichlet series for `x > 0`. -/
@[category API, AMS 11]
theorem summable_vmWeight_rpow (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ vmWeight t n * (n : ℝ) ^ (-x)) := by
  have h1 := summable_vonMangoldt_rpow hx
  have h2 := summable_vonMangoldt_rpow_cos hx t
  refine (h1.sub h2).congr fun n ↦ ?_
  rw [vmWeight_mul_rpow]
  ring

/-- The Karamata hypothesis for `Wirsing.vmWeight`: `x S(x) → 1`. -/
@[category API, AMS 11]
theorem tendsto_vmWeight_series {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x ↦ x * Karamata.series (vmWeight t) x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_abs_tsum_vonMangoldt_twisted_sub_le ht
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 1 one_pos le_rfl)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : (0 : ℝ) < min 1 (ε / (C + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with x hx
  have hxpos : (0 : ℝ) < x := hx.1
  have hxle : x ≤ 1 := le_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _))
  have hxε : x < ε / (C + 1) := lt_of_lt_of_le hx.2 (min_le_right _ _)
  have hser : Karamata.series (vmWeight t) x
      = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        (1 - Real.cos (t * Real.log n)) := tsum_congr fun n ↦ vmWeight_mul_rpow t x n
  have hb := hC x hxpos hxle
  rw [Real.dist_eq, hser]
  set S := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
    (1 - Real.cos (t * Real.log n)) with hS
  have heq : x * S - 1 = x * (S - 1 / x) := by field_simp
  rw [heq, abs_mul, abs_of_pos hxpos]
  have hxC : x * (C + 1) < ε := by rw [← lt_div_iff₀ (by positivity)]; exact hxε
  nlinarith [mul_le_mul_of_nonneg_left hb hxpos.le, hxpos, abs_nonneg (S - 1 / x)]

/--
**The weighted prime-power sum is asymptotic to `\log N`.**  For `t ≠ 0`,
$$\sum_{n \le N} \frac{\Lambda(n)}{n}\bigl(1 - \cos(t\log n)\bigr) \sim \log N.$$

Karamata's Tauberian theorem applied to `Wirsing.vmWeight`.
-/
@[category API, AMS 11]
theorem tendsto_sum_vmWeight_div_log {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, vmWeight t n) / Real.log N) atTop (𝓝 1) := by
  have hK := Karamata.tendsto_partialSum_div (a := vmWeight t) (vmWeight_nonneg t)
    (vmWeight_zero t) (fun x hx ↦ summable_vmWeight_rpow t hx) (tendsto_vmWeight_series ht)
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine (hK.comp hlog).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : ⌊Real.exp (Real.log N)⌋₊ = N := by
    rw [Real.exp_log hN0, Nat.floor_natCast]
  simp only [Function.comp_apply, hfloor]

/-- The prime part of `Wirsing.vmWeight` differs from the whole by at most `2·4`. -/
@[category API, AMS 11]
theorem abs_sum_vonMangoldt_cos_sub_prime_le (t : ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n *
        Real.cos (t * Real.log n))
      - ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p *
        Real.cos (t * Real.log p)| ≤ 4 := by
  classical
  have hsplit : ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n *
      Real.cos (t * Real.log n)
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / p *
          Real.cos (t * Real.log p))
        + ∑ d ∈ (Finset.Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d / d * Real.cos (t * Real.log d) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt p / p * Real.cos (t * Real.log p)
        = Real.log p / p * Real.cos (t * Real.log p) := by
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2]
  rw [hsplit, Finset.sum_congr rfl hprime, add_sub_cancel_left]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun d ↦ ArithmeticFunction.vonMangoldt d / d)
    ?_) (Mertens.sum_vonMangoldt_div_nonprime_le N)
  intro d _
  have hnn : 0 ≤ ArithmeticFunction.vonMangoldt d / d :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  rw [abs_mul, abs_of_nonneg hnn]
  calc ArithmeticFunction.vonMangoldt d / d * |Real.cos (t * Real.log d)|
      ≤ ArithmeticFunction.vonMangoldt d / d * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hnn
    _ = ArithmeticFunction.vonMangoldt d / d := mul_one _

/--
**The prime cosine sum is `o(\log N)`.**  For every `t ≠ 0`,
$$\sum_{p \le N} \frac{\log p}{p}\cos(t\log p) = o(\log N).$$

This is the PNT-strength input of the development: `1 - \cos` weighted sum is `\log N(1+o(1))`
by Karamata, Mertens says the unweighted sum is `\log N + O(1)`, and the proper prime powers
contribute `O(1)`.
-/
@[category API, AMS 11]
theorem tendsto_sum_primeWeight_cos {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun N : ℕ ↦ (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / p * Real.cos (t * Real.log p)) / Real.log N) atTop (𝓝 0) := by
  classical
  -- `∑_{n ≤ N} Λ(n)/n·cos(t log n) / log N → 0`
  have hW := tendsto_sum_vmWeight_div_log ht
  have hM : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / n) / Real.log N) atTop (𝓝 1) := by
    have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hbd : ∀ᶠ N : ℕ in atTop, |(∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / n) / Real.log N - 1|
        ≤ (Real.log 4 + 4) / Real.log N := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_of_lt hN
      have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
      have hme := Mertens.abs_sum_vonMangoldt_div_sub_log_le hN1
      rw [Nat.floor_natCast] at hme
      have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := rfl
      rw [hIoc] at hme
      rw [div_sub_one (ne_of_gt hlogpos), abs_div, abs_of_pos hlogpos]
      rw [div_le_div_iff_of_pos_right hlogpos]
      exact hme
    have hz : Tendsto (fun N : ℕ ↦ (Real.log 4 + 4) / Real.log N) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlog
    have h0 : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / n) / Real.log N - 1) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [hbd] with N hN using by simpa [Real.norm_eq_abs] using hN
    simpa using h0.add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the cosine sum over all prime powers
  have hC : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / n * Real.cos (t * Real.log n)) / Real.log N)
      atTop (𝓝 0) := by
    have h := hM.sub hW
    rw [sub_self] at h
    refine h.congr fun N ↦ ?_
    rw [← sub_div, ← Finset.sum_sub_distrib]
    exact congrArg (· / Real.log N) (Finset.sum_congr rfl fun n _ ↦ by rw [vmWeight]; ring)
  -- drop the proper prime powers
  have h4 : Tendsto (fun N : ℕ ↦ (4 : ℝ) / Real.log N) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  have hdiff : Tendsto (fun N : ℕ ↦ ((∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / n * Real.cos (t * Real.log n))
      - ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p / p * Real.cos (t * Real.log p)) / Real.log N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h4
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogpos, div_le_div_iff_of_pos_right hlogpos]
    exact abs_sum_vonMangoldt_cos_sub_prime_le t N
  have hfin := hC.sub hdiff
  rw [sub_zero] at hfin
  refine hfin.congr fun N ↦ ?_
  rw [← sub_div]
  congr 1
  ring


end Wirsing
