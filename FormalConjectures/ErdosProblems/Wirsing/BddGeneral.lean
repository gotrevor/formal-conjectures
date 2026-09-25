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
public import FormalConjectures.ErdosProblems.Wirsing.General
public import FormalConjectures.ErdosProblems.Wirsing.BddLog

/-!
# The Turán–Kubilius functional relation for bounded multiplicative functions

`Wirsing/General.lean` proves, for a `±1`-valued multiplicative `f` and any finite set `S` of
primes `p \le N`,
$$\Big|\sigma(N)\sum_{p \in S}\frac1p - \sum_{p \in S}\frac{f(p)}{p}\sigma(\lfloor N/p\rfloor)
  \Big| \le 3\big(\sqrt{L_S + 1} + 1\big), \qquad L_S = \sum_{p \in S}\frac1p .$$

This is the engine of Hildebrand's elementary proof of the Lipschitz estimate
`\sigma(x) = \sigma(x/w) + O\big((\log(\log x/\log 2w))^{-1/2}\big)`, whose error exponent
`-1/2` is exactly the `\sqrt{L_S}` of Turán–Kubilius.  Hildebrand's hypothesis is
`-1 \le f \le 1`, i.e. `Wirsing.IsBddMultiplicative`, so the relation is needed in that
generality.  The `±1` proof uses the values only through `|f| \le 1` and `f(n)^2 \le 1`, so it
transfers.

*References:*
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (g : ℕ → ℝ) (S : Finset ℕ)

/-- `∑_{n ≤ N} g(n)^2 ≤ N` for a bounded multiplicative `g`. -/
@[category API, AMS 11]
theorem bdd_sum_sq_le (hg : IsBddMultiplicative g) (N : ℕ) :
    ∑ n ∈ Icc 1 N, g n ^ 2 ≤ (N : ℝ) := by
  calc ∑ n ∈ Icc 1 N, g n ^ 2 ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have h := hg.abs_le_one n (mem_Icc.1 hn).1
        nlinarith [abs_nonneg (g n), sq_abs (g n)]
  _ = (N : ℝ) := by simp

/-- The hyperbola estimate for a bounded multiplicative `g`. -/
@[category API, AMS 11]
theorem bdd_sum_mul_omegaOn_approx (hg : IsBddMultiplicative g) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    |(∑ n ∈ Icc 1 N, g n * omegaOn S n)
      - ∑ p ∈ S, g p * partialSum g (N / p)| ≤ 2 * N := by
  rw [sum_mul_omegaOn_eq g S hS, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ p ∈ S,
      |∑ m ∈ Icc 1 (N / p), g (p * m) - g p * partialSum g (N / p)|
        ≤ 2 * (N : ℝ) * ((1 : ℝ) / p ^ 2) := by
    intro p hp
    have hprime := hS p hp
    have hppos : 0 < p := hprime.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hppos
    rw [partialSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ Icc 1 (N / p),
        |g (p * m) - g p * g m| ≤ if p ∣ m then (2 : ℝ) else 0 := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      by_cases hd : p ∣ m
      · rw [if_pos hd]
        have h1 := hg.abs_le_one (p * m) (Nat.mul_pos hppos (by omega))
        have h2 := hg.abs_le_one p hppos
        have h3 := hg.abs_le_one m hm.1
        calc |g (p * m) - g p * g m| ≤ |g (p * m)| + |g p * g m| := abs_sub _ _
          _ ≤ 2 := by
              rw [abs_mul]
              nlinarith [abs_nonneg (g p), abs_nonneg (g m)]
      · rw [if_neg hd, hg.map_mul_of_coprime p m ((Nat.Prime.coprime_iff_not_dvd hprime).2 hd)]
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcount : ∑ m ∈ Icc 1 (N / p), (if p ∣ m then (2 : ℝ) else 0)
        = 2 * ((N / p / p : ℕ) : ℝ) := by
      have hsplit : ∀ m : ℕ, (if p ∣ m then (2 : ℝ) else 0)
          = 2 * (if p ∣ m then (1 : ℝ) else 0) := by
        intro m; split <;> simp
      rw [Finset.sum_congr rfl fun m _ ↦ hsplit m, ← Finset.mul_sum, Finset.sum_boole,
        card_filter_dvd_Icc]
    rw [hcount, Nat.div_div_eq_div_mul]
    have h4 : ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / (p * p) := by
      rw [← Nat.cast_mul]; exact Nat.cast_div_le
    have h5 : (N : ℝ) / (p * p) = N * (1 / p ^ 2) := by ring
    nlinarith [h4]
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.mul_sum]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [sum_recipSq_le S hS hSN, hN]

/-- Cauchy–Schwarz applied to `∑_{n ≤ N} g(n)(ω_S(n) - L_S)`, bounded class. -/
@[category API, AMS 11]
theorem bdd_abs_sum_mul_omegaOn_sub_le (hg : IsBddMultiplicative g) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    |∑ n ∈ Icc 1 N, g n * ((omegaOn S n : ℝ) - recipSum S)|
      ≤ 3 * N * Real.sqrt (recipSum S + 1) := by
  have hE := recipSum_nonneg S
  have hB : (0 : ℝ) ≤ recipSum S + 1 := by linarith
  have hBsq : Real.sqrt (recipSum S + 1) ^ 2 = recipSum S + 1 := Real.sq_sqrt hB
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) g
    (fun n ↦ (omegaOn S n : ℝ) - recipSum S)
  have hsq := bdd_sum_sq_le g hg N
  have hX : (0 : ℝ) ≤ ∑ n ∈ Icc 1 N, ((omegaOn S n : ℝ) - recipSum S) ^ 2 :=
    Finset.sum_nonneg fun n _ ↦ sq_nonneg _
  have hTK := turan_kubilius_on S hS hSN
  have hkey : (∑ n ∈ Icc 1 N, g n * ((omegaOn S n : ℝ) - recipSum S)) ^ 2
      ≤ (3 * N * Real.sqrt (recipSum S + 1)) ^ 2 := by
    refine hCS.trans ?_
    have heq : (3 * (N : ℝ) * Real.sqrt (recipSum S + 1)) ^ 2
        = 9 * N ^ 2 * (recipSum S + 1) := by
      rw [mul_pow, mul_pow, hBsq]; ring
    rw [heq]
    nlinarith [hTK, hN, hE, hsq, hX]
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((∑ n ∈ Icc 1 N, g n * ((omegaOn S n : ℝ) - recipSum S)) ^ 2)
      ≤ Real.sqrt ((3 * N * Real.sqrt (recipSum S + 1)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = 3 * N * Real.sqrt (recipSum S + 1) := Real.sqrt_sq (by positivity)

/--
**The Turán–Kubilius functional relation, for a bounded multiplicative `g`.**

For every finite set `S` of primes with `p \le N`,
$$\Big|\sigma(N) L_S - \sum_{p \in S}\frac{g(p)}{p}\sigma(\lfloor N/p\rfloor)\Big|
  \le 3\big(\sqrt{L_S + 1} + 1\big), \qquad L_S = \sum_{p \in S}\frac1p .$$

Dividing by `L_S`, the mean at `N` is the `1/p`-weighted average of `g(p)\sigma(\lfloor N/p
\rfloor)` up to `O(L_S^{-1/2})`.  This is the engine of Hildebrand's elementary Lipschitz
estimate.
-/
@[category API, AMS 11]
theorem bdd_functional_relation_on (hg : IsBddMultiplicative g) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hN : 1 ≤ N) (hSN : ∀ p ∈ S, p ≤ N) :
    |mean g N * recipSum S - ∑ p ∈ S, g p * mean g (N / p) / p|
      ≤ 3 * (Real.sqrt (recipSum S + 1) + 1) := by
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b ↦ by
    rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set B := Real.sqrt (recipSum S + 1) with hBdef
  have hB0 : (0 : ℝ) ≤ B := Real.sqrt_nonneg _
  have hcard : (#S : ℝ) ≤ N := by
    have hsub : S ⊆ Icc 1 N := fun p hp ↦ Finset.mem_Icc.2 ⟨(hS p hp).one_lt.le, hSN p hp⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans_eq (by omega)
  have hexp : ∑ n ∈ Icc 1 N, g n * ((omegaOn S n : ℝ) - recipSum S)
      = (∑ n ∈ Icc 1 N, g n * omegaOn S n) - recipSum S * partialSum g N := by
    rw [partialSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  have hA := bdd_abs_sum_mul_omegaOn_sub_le g S hg hS hSN
  rw [hexp] at hA
  have hC := bdd_sum_mul_omegaOn_approx g S hg hS hSN
  have h1 : |recipSum S * partialSum g N - ∑ p ∈ S, g p * partialSum g (N / p)|
      ≤ 3 * N * B + 2 * N := by
    have heq : recipSum S * partialSum g N - ∑ p ∈ S, g p * partialSum g (N / p)
        = ((∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, g p * partialSum g (N / p))
          - ((∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - recipSum S * partialSum g N) := by ring
    rw [heq]
    calc |((∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, g p * partialSum g (N / p))
          - ((∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - recipSum S * partialSum g N)|
        ≤ |(∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, g p * partialSum g (N / p)|
          + |(∑ n ∈ Icc 1 N, g n * (omegaOn S n : ℝ))
            - recipSum S * partialSum g N| := habs _ _
      _ ≤ 2 * N + 3 * N * B := add_le_add hC hA
      _ = 3 * N * B + 2 * N := by ring
  have h2 : |mean g N * recipSum S - ∑ p ∈ S, g p * partialSum g (N / p) / N|
      ≤ 3 * B + 2 := by
    have hdiv : mean g N * recipSum S - ∑ p ∈ S, g p * partialSum g (N / p) / N
        = (recipSum S * partialSum g N - ∑ p ∈ S, g p * partialSum g (N / p)) / N := by
      rw [sub_div, Finset.sum_div, mean_eq_partialSum_div]
      ring
    rw [hdiv, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
    calc |recipSum S * partialSum g N - ∑ p ∈ S, g p * partialSum g (N / p)|
        ≤ 3 * N * B + 2 * N := h1
      _ = (3 * B + 2) * N := by ring
  have h3 : |∑ p ∈ S, (g p * partialSum g (N / p) / N - g p * mean g (N / p) / p)| ≤ 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ p ∈ S,
        |g p * partialSum g (N / p) / N - g p * mean g (N / p) / p| ≤ 1 / N := by
      intro p hp
      have hprime := hS p hp
      have hppos : 0 < p := hprime.pos
      have hpR : (0 : ℝ) < p := by exact_mod_cast hppos
      have hfabs : |g p| ≤ 1 := hg.abs_le_one p hppos
      have hfac : g p * partialSum g (N / p) / N - g p * mean g (N / p) / p
          = g p * (partialSum g (N / p) / N - mean g (N / p) / p) := by ring
      rw [hfac, abs_mul]
      have hrest : |partialSum g (N / p) / N - mean g (N / p) / p| ≤ 1 / N := by
        rcases Nat.eq_zero_or_pos (N / p) with hk | hk
        · rw [hk]
          simp [partialSum, mean]
        · have hkR : (0 : ℝ) < ((N / p : ℕ) : ℝ) := by exact_mod_cast hk
          have hpos : (0 : ℝ) < (N : ℝ) * (((N / p : ℕ) : ℝ) * p) := by positivity
          have hkey : partialSum g (N / p) / N - mean g (N / p) / p
              = partialSum g (N / p) * (((N / p : ℕ) : ℝ) * p - N)
                / ((N : ℝ) * (((N / p : ℕ) : ℝ) * p)) := by
            rw [mean_eq_partialSum_div, div_div]
            field_simp
          have hle : ((N / p : ℕ) : ℝ) * p ≤ N := by exact_mod_cast Nat.div_mul_le_self N p
          have hgt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
            have hnat : N < (N / p + 1) * p := by
              have h1' := Nat.div_add_mod N p
              have h2' := Nat.mod_lt N hppos
              calc N = p * (N / p) + N % p := h1'.symm
                _ < p * (N / p) + p := by omega
                _ = (N / p + 1) * p := by ring
            have := (Nat.cast_lt (α := ℝ)).2 hnat
            push_cast at this
            linarith
          have habsS : |partialSum g (N / p)| ≤ ((N / p : ℕ) : ℝ) :=
            bdd_abs_partialSum_le g hg _
          have hfac2 : |((N / p : ℕ) : ℝ) * p - N| ≤ p := by
            rw [abs_le]; constructor <;> linarith
          have h5 : |partialSum g (N / p) * (((N / p : ℕ) : ℝ) * p - N)|
              ≤ ((N / p : ℕ) : ℝ) * p := by
            rw [abs_mul]
            exact mul_le_mul habsS hfac2 (abs_nonneg _) hkR.le
          rw [hkey, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hNR]
          nlinarith [h5, hNR, hkR, hpR]
      calc |g p| * |partialSum g (N / p) / N - mean g (N / p) / p|
          ≤ 1 * (1 / N) := mul_le_mul hfabs hrest (abs_nonneg _) zero_le_one
        _ = 1 / N := one_mul _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hmul : (#S : ℝ) * (1 / N) ≤ (N : ℝ) * (1 / N) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have hone : (N : ℝ) * (1 / N) = 1 := by field_simp
    linarith [hmul, hone]
  have hsplit : mean g N * recipSum S - ∑ p ∈ S, g p * mean g (N / p) / p
      = (mean g N * recipSum S - ∑ p ∈ S, g p * partialSum g (N / p) / N)
      + ∑ p ∈ S, (g p * partialSum g (N / p) / N - g p * mean g (N / p) / p) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  calc |(mean g N * recipSum S - ∑ p ∈ S, g p * partialSum g (N / p) / N)
      + ∑ p ∈ S, (g p * partialSum g (N / p) / N - g p * mean g (N / p) / p)|
      ≤ |mean g N * recipSum S - ∑ p ∈ S, g p * partialSum g (N / p) / N|
        + |∑ p ∈ S, (g p * partialSum g (N / p) / N - g p * mean g (N / p) / p)| :=
        abs_add_le _ _
    _ ≤ (3 * B + 2) + 1 := add_le_add h2 h3
    _ = 3 * (B + 1) := by ring

end Wirsing
