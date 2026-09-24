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

end Wirsing
