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
public import FormalConjectures.ErdosProblems.Wirsing.Split
public import FormalConjectures.ErdosProblems.Wirsing.Log

/-!
# The log-weighted functional relation for bounded multiplicative functions

`Wirsing/Log.lean` proves
$$\sigma(N)\log N = \sum_{p \le N}\frac{\log p}{p} g(p)\,\sigma(\lfloor N/p\rfloor) + O(1)$$
for `±1`-valued multiplicative `g`.  The attack on `Wirsing.DilationInvariant` needs it for the
wider class `Wirsing.IsBddMultiplicative`, because the coprime restrictions produced by the
splitting of `Wirsing/Split.lean` take the value `0`.

Every step of the `±1` proof uses `|g n| = 1` only through `|g n| ≤ 1`, so the whole chain
transfers verbatim with the equalities relaxed to inequalities.

*References:*
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (g : ℕ → ℝ)

/-- Shifting by a prime, for a bounded multiplicative `g`: the difference between
`∑_{m ≤ M} g(pm)` and `g(p)∑_{m ≤ M} g(m)` is supported on the multiples of `p`. -/
@[category API, AMS 11]
theorem bdd_abs_sum_shift_prime_sub_le (hg : IsBddMultiplicative g) {p M : ℕ} (hp : p.Prime) :
    |(∑ m ∈ Icc 1 M, g (p * m)) - g p * partialSum g M| ≤ 2 * ((M / p : ℕ) : ℝ) := by
  classical
  have hdiff : (∑ m ∈ Icc 1 M, g (p * m)) - g p * partialSum g M
      = ∑ m ∈ Icc 1 M, (g (p * m) - g p * g m) := by
    rw [Finset.sum_sub_distrib, partialSum, Finset.mul_sum]
  have hvanish : ∀ m ∈ Icc 1 M, m ∉ {m ∈ Icc 1 M | p ∣ m} → g (p * m) - g p * g m = 0 := by
    intro m hm hm'
    simp only [Finset.mem_filter] at hm'
    have hnd : ¬ p ∣ m := fun h ↦ hm' ⟨hm, h⟩
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [hg.map_mul_of_coprime p m hcop, sub_self]
  rw [hdiff, ← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ {m ∈ Icc 1 M | p ∣ m}, |g (p * m) - g p * g m| ≤ 2 := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1.1
    have hpm : 1 ≤ p * m := Nat.mul_pos hp.pos hm1
    have h1 := hg.abs_le_one _ hpm
    have h2 := hg.abs_le_one _ hp.one_lt.le
    have h3 := hg.abs_le_one _ hm1
    calc |g (p * m) - g p * g m| ≤ |g (p * m)| + |g p * g m| := abs_sub _ _
    _ ≤ 2 := by
        rw [abs_mul]
        nlinarith [abs_nonneg (g p), abs_nonneg (g m)]
  calc ∑ m ∈ {m ∈ Icc 1 M | p ∣ m}, |g (p * m) - g p * g m|
      ≤ ∑ _m ∈ {m ∈ Icc 1 M | p ∣ m}, (2 : ℝ) := Finset.sum_le_sum hterm
  _ = 2 * ((M / p : ℕ) : ℝ) := by
      rw [Finset.sum_const, card_filter_dvd_Icc, nsmul_eq_mul]
      ring

/-- The shifted partial sums are bounded by the length of the range. -/
@[category API, AMS 11]
theorem bdd_abs_sum_shift_le (hg : IsBddMultiplicative g) {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    |∑ m ∈ Icc 1 M, g (d * m)| ≤ M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Icc 1 M, |g (d * m)| ≤ ∑ _m ∈ Icc 1 M, (1 : ℝ) :=
        Finset.sum_le_sum fun m hm ↦ hg.abs_le_one _ (Nat.mul_pos hd (mem_Icc.1 hm).1)
  _ = M := by simp

/-- The proper prime powers contribute `O(N)` to the von Mangoldt identity. -/
@[category API, AMS 11]
theorem bdd_abs_sum_vonMangoldt_nonprime_le (hg : IsBddMultiplicative g) (N : ℕ) :
    |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m)| ≤ 4 * N := by
  classical
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        |ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m)|
      ≤ ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by
        refine Finset.sum_le_sum fun d hd ↦ ?_
        have hd1 : 1 ≤ d := (mem_Icc.1 (mem_filter.1 hd).1).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc ArithmeticFunction.vonMangoldt d * |∑ m ∈ Icc 1 (N / d), g (d * m)|
            ≤ ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (bdd_abs_sum_shift_le g hg hd1 _)
                ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) :=
              mul_le_mul_of_nonneg_left (Nat.cast_div_le) ArithmeticFunction.vonMangoldt_nonneg
        _ = (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by ring
  _ = (N : ℝ) * ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        ArithmeticFunction.vonMangoldt d / d := (Finset.mul_sum _ _ _).symm
  _ ≤ (N : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left (Mertens.sum_vonMangoldt_div_nonprime_le N) (Nat.cast_nonneg _)
  _ = 4 * N := by ring

/-- Replacing `g(pm)` by `g(p) g(m)` in the prime terms costs `O(N)`. -/
@[category API, AMS 11]
theorem bdd_abs_sum_vonMangoldt_prime_sub_le (hg : IsBddMultiplicative g) (N : ℕ) :
    |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), g (p * m))
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))|
      ≤ 4 * N := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        |Real.log p * (∑ m ∈ Icc 1 (N / p), g (p * m))
          - Real.log p * (g p * partialSum g (N / p))|
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, 2 * (N : ℝ) * (Real.log p / (p : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hpp : p.Prime := (mem_filter.1 hp).2
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
        rw [← mul_sub, abs_mul, abs_of_nonneg hlog]
        have hshift := bdd_abs_sum_shift_prime_sub_le g hg (p := p) (M := N / p) hpp
        have hcast : ((N / p / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
          rw [Nat.div_div_eq_div_mul]
          calc ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) / (p : ℝ) ^ 2 := by push_cast; ring_nf
        calc Real.log p * |(∑ m ∈ Icc 1 (N / p), g (p * m)) - g p * partialSum g (N / p)|
            ≤ Real.log p * (2 * ((N / p / p : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hshift hlog
        _ ≤ Real.log p * (2 * ((N : ℝ) / (p : ℝ) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ hlog
              linarith
        _ = 2 * (N : ℝ) * (Real.log p / (p : ℝ) ^ 2) := by ring
  _ = 2 * (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2 :=
        (Finset.mul_sum _ _ _).symm
  _ ≤ 2 * (N : ℝ) * ∑ n ∈ Icc 2 N, Real.log n / (n : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦
          div_nonneg (Real.log_natCast_nonneg _) (by positivity)
        intro q hq
        simp only [mem_filter, mem_Icc] at hq
        exact mem_Icc.2 ⟨hq.2.two_le, hq.1.2⟩
  _ ≤ 4 * N := by
        have h := Mertens.sum_log_div_sq_le N
        nlinarith [Nat.cast_nonneg (α := ℝ) N]

/--
**The log-weighted functional relation for a bounded multiplicative `g`:**
$$S(N)\log N = \sum_{p \le N} \log p \cdot g(p) \cdot S(\lfloor N/p \rfloor) + O(N).$$
-/
@[category API, AMS 11]
theorem bdd_abs_partialSum_mul_log_sub_sum_prime_le (hg : IsBddMultiplicative g) (N : ℕ) :
    |partialSum g N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))|
      ≤ 9 * N := by
  classical
  have hAbel := abs_sum_mul_log_sub_partialSum_mul_log_le g (fun n hn ↦ hg.abs_le_one n hn) N
  have hid := sum_Icc_mul_log g N
  have hsplit : ∑ d ∈ Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m)
      = (∑ d ∈ (Icc 1 N).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : (∑ d ∈ (Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m))
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), g (p * m) :=
    Finset.sum_congr rfl fun d hd ↦ by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hd).2]
  have h1 := bdd_abs_sum_vonMangoldt_nonprime_le g hg N
  have h2 := bdd_abs_sum_vonMangoldt_prime_sub_le g hg N
  rw [hprime] at hsplit
  rw [hsplit] at hid
  have hdecomp : partialSum g N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))
      = -((∑ n ∈ Icc 1 N, g n * Real.log n) - partialSum g N * Real.log N)
        + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), g (p * m))
          - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p)))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m) := by
    rw [hid]; ring
  rw [hdecomp]
  calc |(-((∑ n ∈ Icc 1 N, g n * Real.log n) - partialSum g N * Real.log N)
          + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), g (p * m))
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m)|
      ≤ |(-((∑ n ∈ Icc 1 N, g n * Real.log n) - partialSum g N * Real.log N)
          + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), g (p * m))
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))))|
        + |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m)| := abs_add_le _ _
  _ ≤ ((N : ℝ) + 4 * N) + 4 * N := by
        refine add_le_add ?_ h1
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
        exact add_le_add hAbel h2
  _ ≤ 9 * N := by linarith [Nat.cast_nonneg (α := ℝ) N]

/--
**The functional relation in mean-value form, for a bounded multiplicative `g`:**
$$\sigma(N)\log N = \sum_{p \le N} \frac{\log p}{p} g(p)\, \sigma(\lfloor N/p \rfloor) + O(1).$$
By Mertens' first theorem the weights `\log p/p` have total mass `\log N + O(1)`, so this is an
averaging identity for `mean g`.  It is the engine for `Wirsing.DilationInvariant`.
-/
@[category API, AMS 11]
theorem bdd_abs_mean_mul_log_sub_sum_prime_le (hg : IsBddMultiplicative g) {N : ℕ}
    (hN : 1 ≤ N) :
    |mean g N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (g p * mean g (N / p))|
      ≤ 9 + Real.log 4 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmain := bdd_abs_partialSum_mul_log_sub_sum_prime_le g hg N
  have hswap : |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p)))
      - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (g p * mean g (N / p))| ≤ Real.log 4 * N := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          |Real.log p * (g p * partialSum g (N / p))
            - (N : ℝ) * (Real.log p / p * (g p * mean g (N / p)))|
        ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          have hpp : p.Prime := (mem_filter.1 hp).2
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
          have hfp : |g p| ≤ 1 := hg.abs_le_one _ hpp.one_lt.le
          have hmn : |mean g (N / p)| ≤ 1 := abs_mean_le_one_of_bdd hg _
          have hfl1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
          have hfl2 : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
            have hmod : N % p < p := Nat.mod_lt _ hpp.pos
            have hdm := Nat.div_add_mod N p
            have hlt : N < p * (N / p) + p := by omega
            have hltR : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) : ℝ) + p := by exact_mod_cast hlt
            rw [sub_le_iff_le_add, div_le_iff₀ hpR]
            nlinarith
          rw [partialSum_eq_mul_mean]
          have hrw : Real.log p * (g p * ((N / p : ℕ) * mean g (N / p)))
              - (N : ℝ) * (Real.log p / p * (g p * mean g (N / p)))
              = Real.log p * (g p * mean g (N / p)) * (((N / p : ℕ) : ℝ) - (N : ℝ) / p) := by
            field_simp
          rw [hrw, abs_mul, abs_mul, abs_mul]
          have habs : |((N / p : ℕ) : ℝ) - (N : ℝ) / p| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          have h1 : |g p| * |mean g (N / p)| ≤ 1 := mul_le_one₀ hfp (abs_nonneg _) hmn
          rw [abs_of_nonneg hlog, mul_assoc]
          calc Real.log p * ((|g p| * |mean g (N / p)|)
                * |((N / p : ℕ) : ℝ) - (N : ℝ) / p|)
              ≤ Real.log p * 1 :=
                mul_le_mul_of_nonneg_left (mul_le_one₀ h1 (abs_nonneg _) habs) hlog
          _ = Real.log p := mul_one _
    _ ≤ Real.log 4 * N := by
          have hthe := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hN0.le
          rw [Chebyshev.theta, Nat.floor_natCast] at hthe
          exact hthe
  have hcomb : |partialSum g N * Real.log N
      - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (g p * mean g (N / p))| ≤ 9 * N + Real.log 4 * N := by
    calc |partialSum g N * Real.log N
        - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * (g p * mean g (N / p))|
        ≤ |partialSum g N * Real.log N
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p))|
          + |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p)))
            - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                Real.log p / p * (g p * mean g (N / p))| := by
          have := abs_add_le
            (partialSum g N * Real.log N
              - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p)))
            ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (g p * partialSum g (N / p)))
              - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                  Real.log p / p * (g p * mean g (N / p)))
          simpa using this
    _ ≤ 9 * N + Real.log 4 * N := add_le_add hmain hswap
  rw [partialSum_eq_mul_mean, mul_assoc] at hcomb
  rw [← mul_sub, abs_mul, abs_of_nonneg hN0.le] at hcomb
  refine le_of_mul_le_mul_left ?_ hN0
  calc (N : ℝ) * |mean g N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (g p * mean g (N / p))|
      ≤ 9 * N + Real.log 4 * N := hcomb
  _ = (N : ℝ) * (9 + Real.log 4) := by ring

/-- `|S(M)| ≤ M` for a bounded multiplicative `g`. -/
@[category API, AMS 11]
theorem bdd_abs_partialSum_le (hg : IsBddMultiplicative g) (M : ℕ) :
    |partialSum g M| ≤ (M : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ Icc 1 M, |g n| ≤ ∑ _n ∈ Icc 1 M, (1 : ℝ) :=
        Finset.sum_le_sum fun n hn ↦ hg.abs_le_one n (mem_Icc.1 hn).1
  _ = M := by simp

/-- **The mean is log-Lipschitz**, for a bounded multiplicative `g`: for `1 ≤ M ≤ N`,
`|\sigma(N) - \sigma(M)| \le 2(N-M)/N`. -/
@[category API, AMS 11]
theorem bdd_abs_mean_sub_mean_le (hg : IsBddMultiplicative g) {M N : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) : |mean g N - mean g M| ≤ 2 * ((N : ℝ) - M) / N := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMNR : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hinc : |partialSum g N - partialSum g M| ≤ (N : ℝ) - M := by
    have hsplit : partialSum g N - partialSum g M = ∑ n ∈ Ioc M N, g n := by
      rw [partialSum, partialSum, (by rfl : Icc 1 N = Ioc 0 N), (by rfl : Icc 1 M = Ioc 0 M),
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]
      ring
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcard : ∑ n ∈ Ioc M N, |g n| ≤ ((N - M : ℕ) : ℝ) := by
      calc ∑ n ∈ Ioc M N, |g n| ≤ ∑ _n ∈ Ioc M N, (1 : ℝ) :=
            Finset.sum_le_sum fun n hn ↦ hg.abs_le_one n
              (by have := (Finset.mem_Ioc.1 hn).1; omega)
      _ = ((N - M : ℕ) : ℝ) := by simp [Nat.card_Ioc]
    have hcast : ((N - M : ℕ) : ℝ) = (N : ℝ) - M := by
      push_cast [Nat.cast_sub hMN]; ring
    linarith [hcast ▸ hcard]
  have hSM : |partialSum g M| ≤ (M : ℝ) := bdd_abs_partialSum_le g hg M
  have hrw : mean g N - mean g M
      = (partialSum g N - partialSum g M) / N - partialSum g M * (((N : ℝ) - M) / (N * M)) := by
    rw [mean_eq_partialSum_div, mean_eq_partialSum_div]
    field_simp
    ring
  rw [hrw]
  have h1 : |(partialSum g N - partialSum g M) / N| ≤ ((N : ℝ) - M) / N := by
    rw [abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hinc hNpos.le
  have h2 : |partialSum g M * (((N : ℝ) - M) / (N * M))| ≤ ((N : ℝ) - M) / N := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((N : ℝ) - M) / (N * M))]
    calc |partialSum g M| * (((N : ℝ) - M) / (N * M))
        ≤ (M : ℝ) * (((N : ℝ) - M) / (N * M)) :=
          mul_le_mul_of_nonneg_right hSM (by positivity)
      _ = ((N : ℝ) - M) / N := by field_simp
  have hgoal : 2 * ((N : ℝ) - M) / N = ((N : ℝ) - M) / N + ((N : ℝ) - M) / N := by ring
  rw [hgoal]
  linarith [abs_sub ((partialSum g N - partialSum g M) / N)
    (partialSum g M * (((N : ℝ) - M) / (N * M)))]

end Wirsing
