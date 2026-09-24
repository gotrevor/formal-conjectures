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
public import FormalConjectures.ErdosProblems.Wirsing.Decay

/-!
# The mean side: the Dirichlet inversion

The bridge between the partial sums `S(N) = ∑_{n ≤ N} f(n)` and the logarithmic average
`L(N) = ∑_{n ≤ N} f(n)/n`, which is the "inversion of the order of summation" at the start of
Hildebrand's elementary proof of Wirsing's theorem.

The identity is exact:
$$\sum_{k \le N} S(\lfloor N/k\rfloor) = \sum_{m \le N} f(m) \lfloor N/m \rfloor,$$
and replacing `⌊N/m⌋` by `N/m` costs at most `N`, so
$$\sum_{k \le N} S(\lfloor N/k\rfloor) = N\,L(N) + O(N).$$

*References:*
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The hyperbola swap in the form needed here: `∑_{k ≤ N} ∑_{m ≤ N/k} = ∑_{m ≤ N} ∑_{k ≤ N/m}`,
both sides running over the pairs `(k, m)` of positive integers with `k m ≤ N`. -/
@[category API, AMS 11]
theorem sum_Icc_one_div_comm (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / k), F k m)
      = ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / m), F k m := by
  refine Finset.sum_comm' ?_
  intro k m
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, hm1, hmk⟩
    have hmk' : m * k ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmk
    have hkm : k * m ≤ N := by rwa [Nat.mul_comm] at hmk'
    have hmle : m ≤ m * k := Nat.le_mul_of_pos_right m (by omega)
    exact ⟨⟨hk1, (Nat.le_div_iff_mul_le (by omega)).2 hkm⟩, hm1, by omega⟩
  · rintro ⟨⟨hk1, hkm⟩, hm1, hmN⟩
    have hkm' : k * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hkm
    have hmk : m * k ≤ N := by rwa [Nat.mul_comm] at hkm'
    have hkle : k ≤ k * m := Nat.le_mul_of_pos_right k (by omega)
    exact ⟨⟨hk1, by omega⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).2 hmk⟩

/--
**The Dirichlet inversion.**  The exact identity
`∑_{k ≤ N} S(⌊N/k⌋) = ∑_{m ≤ N} f(m) ⌊N/m⌋`.
-/
@[category API, AMS 11]
theorem sum_partialSum_div_eq (N : ℕ) :
    ∑ k ∈ Icc 1 N, partialSum f (N / k) = ∑ m ∈ Icc 1 N, f m * ((N / m : ℕ) : ℝ) := by
  have hL : ∑ k ∈ Icc 1 N, partialSum f (N / k)
      = ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / k), f m := rfl
  rw [hL, sum_Icc_one_div_comm N (fun _ m ↦ f m)]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

/--
**The inversion, with `⌊N/m⌋` replaced by `N/m`.**  `∑_{k ≤ N} S(⌊N/k⌋) = N L(N) + O(N)`.

The error is at most `N` because `|f(m)| = 1` and `0 ≤ N/m - ⌊N/m⌋ < 1` for each of the `N`
terms.
-/
@[category API, AMS 11]
theorem abs_sum_partialSum_div_sub_mul_logMean_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |∑ k ∈ Icc 1 N, partialSum f (N / k) - (N : ℝ) * logMean f N| ≤ (N : ℝ) := by
  rw [sum_partialSum_div_eq f N, logMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ m ∈ Icc 1 N, |f m * ((N / m : ℕ) : ℝ) - (N : ℝ) * (f m / m)| ≤ 1 := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have habs : |f m| = 1 := abs_eq_one_of_one_le f hf hm1
    have hrw : f m * ((N / m : ℕ) : ℝ) - (N : ℝ) * (f m / m)
        = f m * (((N / m : ℕ) : ℝ) - (N : ℝ) / m) := by
      field_simp
    rw [hrw, abs_mul, habs, one_mul, abs_le]
    have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
      rw [le_div_iff₀ (by linarith)]
      have : (N / m) * m ≤ N := Nat.div_mul_le_self N m
      calc ((N / m : ℕ) : ℝ) * (m : ℝ) = (((N / m) * m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) := by exact_mod_cast this
    have hfl2 : (N : ℝ) / m - 1 ≤ ((N / m : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
      have : N < (N / m + 1) * m := by
        have h1 := Nat.div_add_mod N m
        have h2 := Nat.mod_lt N (show 0 < m by omega)
        have h3 : (N / m + 1) * m = m * (N / m) + m := by ring
        omega
      calc (N : ℝ) ≤ (((N / m + 1) * m : ℕ) : ℝ) := by exact_mod_cast this.le
      _ = (((N / m : ℕ) : ℝ) + 1) * (m : ℝ) := by push_cast; ring
    constructor <;> linarith
  calc |∑ m ∈ Icc 1 N, (f m * ((N / m : ℕ) : ℝ) - (N : ℝ) * (f m / m))|
      ≤ ∑ m ∈ Icc 1 N, |f m * ((N / m : ℕ) : ℝ) - (N : ℝ) * (f m / m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Icc 1 N, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- `|⌊N/m⌋ - N/m| ≤ 1`. -/
@[category API, AMS 11]
theorem abs_natDiv_sub_div_le_one {N m : ℕ} (hm : 1 ≤ m) :
    |((N / m : ℕ) : ℝ) - (N : ℝ) / m| ≤ 1 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ (by linarith)]
    have h : (N / m) * m ≤ N := Nat.div_mul_le_self N m
    calc ((N / m : ℕ) : ℝ) * (m : ℝ) = (((N / m) * m : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (N : ℝ) := by exact_mod_cast h
  have hfl2 : (N : ℝ) / m - 1 ≤ ((N / m : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
    have h : N < (N / m + 1) * m := by
      have h1 := Nat.div_add_mod N m
      have h2 := Nat.mod_lt N (show 0 < m by omega)
      have h3 : (N / m + 1) * m = m * (N / m) + m := by ring
      omega
    calc (N : ℝ) ≤ (((N / m + 1) * m : ℕ) : ℝ) := by exact_mod_cast h.le
    _ = (((N / m : ℕ) : ℝ) + 1) * (m : ℝ) := by push_cast; ring
  rw [abs_le]
  constructor <;> linarith

/--
**The hyperbola identity on the mean side.**  The logarithmic average of `σ` along the
quotients equals `L(N)` up to an absolute constant:
$$\Big|\sum_{k \le N} \frac{\sigma(\lfloor N/k\rfloor)}{k} - L(N)\Big| \le 2.$$

This is the first place where `L(N) = o(\log N)` gives information about the mean: the left
sum has `N` terms and its trivial bound is `\log N`, so the identity is not vacuous.
-/
@[category API, AMS 11]
theorem abs_sum_mean_div_sub_logMean_le (hf : IsPMOneMultiplicative f) {N : ℕ} (hN : 1 ≤ N) :
    |∑ k ∈ Icc 1 N, mean f (N / k) / k - logMean f N| ≤ 2 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set T : ℝ := ∑ k ∈ Icc 1 N, mean f (N / k) / k with hT
  -- compare the exact sum of partial sums with `N * T`
  have hcmp : |∑ k ∈ Icc 1 N, partialSum f (N / k) - (N : ℝ) * T| ≤ (N : ℝ) := by
    rw [hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Icc 1 N,
        |partialSum f (N / k) - (N : ℝ) * (mean f (N / k) / k)| ≤ 1 := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hrw : partialSum f (N / k) - (N : ℝ) * (mean f (N / k) / k)
          = (((N / k : ℕ) : ℝ) - (N : ℝ) / k) * mean f (N / k) := by
        rw [partialSum_eq_mul_mean]
        field_simp
      rw [hrw, abs_mul]
      calc |((N / k : ℕ) : ℝ) - (N : ℝ) / k| * |mean f (N / k)|
          ≤ 1 * 1 := mul_le_mul (abs_natDiv_sub_div_le_one hk1) (abs_mean_le_one f hf _)
            (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc |∑ k ∈ Icc 1 N, (partialSum f (N / k) - (N : ℝ) * (mean f (N / k) / k))|
        ≤ ∑ k ∈ Icc 1 N, |partialSum f (N / k) - (N : ℝ) * (mean f (N / k) / k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Icc 1 N, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (N : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have hinv := abs_sum_partialSum_div_sub_mul_logMean_le f hf N
  have hcomb : |(N : ℝ) * T - (N : ℝ) * logMean f N| ≤ 2 * (N : ℝ) := by
    have h := abs_sub ((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * logMean f N)
      ((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * T)
    have hid : (N : ℝ) * T - (N : ℝ) * logMean f N
        = ((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * logMean f N)
          - ((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * T) := by ring
    rw [hid]
    calc |((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * logMean f N)
        - ((∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * T)|
        ≤ |(∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * logMean f N|
          + |(∑ k ∈ Icc 1 N, partialSum f (N / k)) - (N : ℝ) * T| := abs_sub _ _
      _ ≤ (N : ℝ) + (N : ℝ) := by linarith [hinv, hcmp]
      _ = 2 * (N : ℝ) := by ring
  have hfac : (N : ℝ) * T - (N : ℝ) * logMean f N = (N : ℝ) * (T - logMean f N) := by ring
  rw [hfac, abs_mul, abs_of_pos hNpos] at hcomb
  have hfinal : (N : ℝ) * |T - logMean f N| ≤ (N : ℝ) * 2 := by linarith
  exact le_of_mul_le_mul_left hfinal hNpos

end Wirsing
