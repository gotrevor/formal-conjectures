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
public import FormalConjectures.ErdosProblems.Wirsing.Identity
public import FormalConjectures.ErdosProblems.Wirsing.OmegaE

/-!
# The log-weighted functional relation

Abel summation turns $\sum_{n \le N} f(n)\log n$ into $S(N)\log N$ up to $O(N)$, so the
von Mangoldt identity `Wirsing.sum_Icc_mul_log` becomes a relation between $S(N)\log N$ and
the weighted averages $\sum_{d \le N} \Lambda(d) S(N/d)$.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
-/

@[expose] public section

open Filter Finset

namespace Wirsing

variable (f : ℕ → ℝ)

/--
Abel summation: replacing `log n` by `log N` in $\sum_{n \le N} f(n) \log n$ costs at
most `N`, for any `f` bounded by `1` on the positive integers.
-/
@[category API, AMS 11]
theorem abs_sum_mul_log_sub_partialSum_mul_log_le (hf : ∀ n, 1 ≤ n → |f n| ≤ 1) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N| ≤ N := by
  have habs : ∀ M : ℕ, |partialSum f M| ≤ M := by
    intro M
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Icc 1 M, |f n| ≤ ∑ _n ∈ Icc 1 M, (1 : ℝ) :=
          sum_le_sum fun n hn ↦ hf n (mem_Icc.1 hn).1
    _ = M := by simp
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [partialSum]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hstep : (∑ n ∈ Icc 1 (N + 1), f n * Real.log n) - partialSum f (N + 1) * Real.log (N + 1)
        = ((∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N)
          - partialSum f N * (Real.log (N + 1) - Real.log N) := by
      have h1 : ∑ n ∈ Icc 1 (N + 1), f n * Real.log n
          = (∑ n ∈ Icc 1 N, f n * Real.log n) + f (N + 1) * Real.log (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        push_cast
        ring
      have h2 : partialSum f (N + 1) = partialSum f N + f (N + 1) := by
        rw [partialSum, partialSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [h1, h2]
      ring
    have hlog : Real.log (N + 1) - Real.log N ≤ 1 / N := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have he : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith [he ▸ h]
    have hlog0 : 0 ≤ Real.log (N + 1) - Real.log N :=
      sub_nonneg.2 (Real.log_le_log hN0 (by linarith))
    push_cast
    rw [hstep]
    have hbound : |partialSum f N * (Real.log (N + 1) - Real.log N)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlog0]
      calc |partialSum f N| * (Real.log (N + 1) - Real.log N) ≤ (N : ℝ) * (1 / N) := by
            exact mul_le_mul (habs N) hlog hlog0 (by positivity)
      _ = 1 := by field_simp
    calc |((∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N)
            - partialSum f N * (Real.log (N + 1) - Real.log N)|
        ≤ |(∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N|
          + |partialSum f N * (Real.log (N + 1) - Real.log N)| := abs_sub _ _
    _ ≤ (N : ℝ) + 1 := by linarith [ih, hbound]

/--
Shifting by a prime: $\sum_{m \le M} f(pm)$ differs from $f(p)\sum_{m \le M} f(m)$ only
through the multiples of `p`, of which there are $\lfloor M/p \rfloor$.
-/
@[category API, AMS 11]
theorem abs_sum_shift_prime_sub_le (hf : IsPMOneMultiplicative f) {p M : ℕ} (hp : p.Prime) :
    |(∑ m ∈ Icc 1 M, f (p * m)) - f p * partialSum f M| ≤ 2 * ((M / p : ℕ) : ℝ) := by
  classical
  have hdiff : (∑ m ∈ Icc 1 M, f (p * m)) - f p * partialSum f M
      = ∑ m ∈ Icc 1 M, (f (p * m) - f p * f m) := by
    rw [Finset.sum_sub_distrib, partialSum, Finset.mul_sum]
  have hvanish : ∀ m ∈ Icc 1 M, m ∉ {m ∈ Icc 1 M | p ∣ m} → f (p * m) - f p * f m = 0 := by
    intro m hm hm'
    simp only [Finset.mem_filter] at hm'
    have hnd : ¬ p ∣ m := fun h ↦ hm' ⟨hm, h⟩
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [hf.map_mul_of_coprime p m hcop, sub_self]
  rw [hdiff, ← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ {m ∈ Icc 1 M | p ∣ m}, |f (p * m) - f p * f m| ≤ 2 := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1.1
    have hpm : 1 ≤ p * m := Nat.mul_pos hp.pos hm1
    have h1 := abs_eq_one_of_one_le f hf hpm
    have h2 := abs_eq_one_of_one_le f hf hp.one_lt.le
    have h3 := abs_eq_one_of_one_le f hf hm1
    calc |f (p * m) - f p * f m| ≤ |f (p * m)| + |f p * f m| := abs_sub _ _
    _ = 2 := by rw [h1, abs_mul, h2, h3]; norm_num
  calc ∑ m ∈ {m ∈ Icc 1 M | p ∣ m}, |f (p * m) - f p * f m|
      ≤ ∑ _m ∈ {m ∈ Icc 1 M | p ∣ m}, (2 : ℝ) := Finset.sum_le_sum hterm
  _ = 2 * ((M / p : ℕ) : ℝ) := by
      rw [Finset.sum_const, card_filter_dvd_Icc, nsmul_eq_mul]
      ring

/-- The shifted partial sums are bounded by the length of the range. -/
@[category API, AMS 11]
theorem abs_sum_shift_le (hf : IsPMOneMultiplicative f) {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    |∑ m ∈ Icc 1 M, f (d * m)| ≤ M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ m ∈ Icc 1 M, |f (d * m)| = 1 := fun m hm ↦
    abs_eq_one_of_one_le f hf (Nat.mul_pos hd (mem_Icc.1 hm).1)
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- The proper prime powers contribute `O(N)` to the von Mangoldt identity. -/
@[category API, AMS 11]
theorem abs_sum_vonMangoldt_nonprime_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m)| ≤ 4 * N := by
  classical
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        |ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m)|
      ≤ ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by
        refine Finset.sum_le_sum fun d hd ↦ ?_
        have hd1 : 1 ≤ d := (mem_Icc.1 (mem_filter.1 hd).1).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc ArithmeticFunction.vonMangoldt d * |∑ m ∈ Icc 1 (N / d), f (d * m)|
            ≤ ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (abs_sum_shift_le f hf hd1 _)
                ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) :=
              mul_le_mul_of_nonneg_left (Nat.cast_div_le) ArithmeticFunction.vonMangoldt_nonneg
        _ = (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by ring
  _ = (N : ℝ) * ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        ArithmeticFunction.vonMangoldt d / d := (Finset.mul_sum _ _ _).symm
  _ ≤ (N : ℝ) * 4 := by
        exact mul_le_mul_of_nonneg_left (Mertens.sum_vonMangoldt_div_nonprime_le N)
          (Nat.cast_nonneg _)
  _ = 4 * N := by ring

/-- Replacing `f(pm)` by `f(p) f(m)` in the prime terms costs `O(N)`. -/
@[category API, AMS 11]
theorem abs_sum_vonMangoldt_prime_sub_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), f (p * m))
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))|
      ≤ 4 * N := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        |Real.log p * (∑ m ∈ Icc 1 (N / p), f (p * m)) - Real.log p * (f p * partialSum f (N / p))|
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, 2 * (N : ℝ) * (Real.log p / (p : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hpp : p.Prime := (mem_filter.1 hp).2
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
        rw [← mul_sub, abs_mul, abs_of_nonneg hlog]
        have hshift := abs_sum_shift_prime_sub_le f hf (p := p) (M := N / p) hpp
        have hcast : ((N / p / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
          rw [Nat.div_div_eq_div_mul]
          calc ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) / (p : ℝ) ^ 2 := by push_cast; ring_nf
        calc Real.log p * |(∑ m ∈ Icc 1 (N / p), f (p * m)) - f p * partialSum f (N / p)|
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

end Wirsing
