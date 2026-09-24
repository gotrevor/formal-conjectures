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

/--
The log-weighted functional relation: for a `±1`-valued multiplicative `f`,
$$S(N)\log N = \sum_{p \le N} \log p \cdot f(p) \cdot S(\lfloor N/p \rfloor) + O(N).$$
-/
@[category API, AMS 11]
theorem abs_partialSum_mul_log_sub_sum_prime_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |partialSum f N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))|
      ≤ 9 * N := by
  classical
  have hbound : ∀ n, 1 ≤ n → |f n| ≤ 1 := fun n hn ↦ (abs_eq_one_of_one_le f hf hn).le
  have hAbel := abs_sum_mul_log_sub_partialSum_mul_log_le f hbound N
  have hid := sum_Icc_mul_log f N
  have hsplit : ∑ d ∈ Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m)
      = (∑ d ∈ (Icc 1 N).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : (∑ d ∈ (Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m))
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), f (p * m) :=
    Finset.sum_congr rfl fun d hd ↦ by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hd).2]
  have h1 := abs_sum_vonMangoldt_nonprime_le f hf N
  have h2 := abs_sum_vonMangoldt_prime_sub_le f hf N
  rw [hprime] at hsplit
  rw [hsplit] at hid
  have hdecomp : partialSum f N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))
      = -((∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N)
        + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), f (p * m))
          - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p)))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m) := by
    rw [hid]; ring
  rw [hdecomp]
  calc |(-((∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N)
          + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), f (p * m))
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m)|
      ≤ |(-((∑ n ∈ Icc 1 N, f n * Real.log n) - partialSum f N * Real.log N)
          + ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * ∑ m ∈ Icc 1 (N / p), f (p * m))
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))))|
        + |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), f (d * m)| := abs_add_le _ _
  _ ≤ ((N : ℝ) + 4 * N) + 4 * N := by
        refine add_le_add ?_ h1
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
        exact add_le_add hAbel h2
  _ ≤ 9 * N := by linarith [Nat.cast_nonneg (α := ℝ) N]

/-- `S(M) = M · mean f M`, including for `M = 0`. -/
@[category API, AMS 11]
theorem partialSum_eq_mul_mean (M : ℕ) : partialSum f M = M * mean f M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [partialSum, mean]
  · have hM0 : (M : ℝ) ≠ 0 := by positivity
    rw [mean_eq_partialSum_div, mul_comm, div_mul_cancel₀ _ hM0]

/--
The log-weighted functional relation in mean-value form: for a `±1`-valued multiplicative `f`
and `N ≥ 1`,
$$\sigma(N)\log N = \sum_{p \le N} \frac{\log p}{p} f(p)\, \sigma(\lfloor N/p \rfloor) + O(1),$$
where $\sigma = $ `mean f`.  By Mertens' first theorem the weights $\log p / p$ have total
mass $\log N + O(1)$, so this is an averaging identity for `mean f`.
-/
@[category API, AMS 11]
theorem abs_mean_mul_log_sub_sum_prime_le (hf : IsPMOneMultiplicative f) {N : ℕ} (hN : 1 ≤ N) :
    |mean f N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (f p * mean f (N / p))|
      ≤ 9 + Real.log 4 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmain := abs_partialSum_mul_log_sub_sum_prime_le f hf N
  -- replace `S(N/p)` by `(N/p) · mean f (N/p)` and `⌊N/p⌋` by `N/p`
  have hswap : |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p)))
      - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (f p * mean f (N / p))| ≤ Real.log 4 * N := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          |Real.log p * (f p * partialSum f (N / p))
            - (N : ℝ) * (Real.log p / p * (f p * mean f (N / p)))|
        ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          have hpp : p.Prime := (mem_filter.1 hp).2
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
          have hfp : |f p| = 1 := abs_eq_one_of_one_le f hf hpp.one_lt.le
          have hmn : |mean f (N / p)| ≤ 1 := abs_mean_le_one f hf _
          have hfl1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
          have hfl2 : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
            have hmod : N % p < p := Nat.mod_lt _ hpp.pos
            have hdm := Nat.div_add_mod N p
            have hlt : N < p * (N / p) + p := by omega
            have hltR : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) : ℝ) + p := by exact_mod_cast hlt
            rw [sub_le_iff_le_add, div_le_iff₀ hpR]
            nlinarith
          rw [partialSum_eq_mul_mean]
          have hrw : Real.log p * (f p * ((N / p : ℕ) * mean f (N / p)))
              - (N : ℝ) * (Real.log p / p * (f p * mean f (N / p)))
              = Real.log p * (f p * mean f (N / p)) * (((N / p : ℕ) : ℝ) - (N : ℝ) / p) := by
            field_simp
          rw [hrw, abs_mul, abs_mul, abs_mul, hfp]
          have habs : |((N / p : ℕ) : ℝ) - (N : ℝ) / p| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          calc |Real.log p| * (1 * |mean f (N / p)|) * |((N / p : ℕ) : ℝ) - (N : ℝ) / p|
              ≤ Real.log p * (1 * 1) * 1 := by
                rw [abs_of_nonneg hlog]
                have hprod : |mean f (N / p)| * |((N / p : ℕ) : ℝ) - (N : ℝ) / p| ≤ 1 :=
                  mul_le_one₀ hmn (abs_nonneg _) habs
                nlinarith [hprod, hlog]
          _ = Real.log p := by ring
    _ ≤ Real.log 4 * N := by
          have hthe := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hN0.le
          rw [Chebyshev.theta, Nat.floor_natCast] at hthe
          exact hthe
  have hcomb : |partialSum f N * Real.log N
      - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (f p * mean f (N / p))| ≤ 9 * N + Real.log 4 * N := by
    calc |partialSum f N * Real.log N
        - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * (f p * mean f (N / p))|
        ≤ |partialSum f N * Real.log N
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p))|
          + |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p)))
            - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                Real.log p / p * (f p * mean f (N / p))| := by
          have := abs_add_le
            (partialSum f N * Real.log N
              - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p)))
            ((∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p * (f p * partialSum f (N / p)))
              - (N : ℝ) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                  Real.log p / p * (f p * mean f (N / p)))
          simpa using this
    _ ≤ 9 * N + Real.log 4 * N := add_le_add hmain hswap
  rw [partialSum_eq_mul_mean, mul_assoc] at hcomb
  rw [← mul_sub, abs_mul, abs_of_nonneg hN0.le] at hcomb
  refine le_of_mul_le_mul_left ?_ hN0
  calc (N : ℝ) * |mean f N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (f p * mean f (N / p))|
      ≤ 9 * N + Real.log 4 * N := hcomb
  _ = (N : ℝ) * (9 + Real.log 4) := by ring

/-- The logarithmic average `L(N) = ∑_{n ≤ N} f(n)/n`. -/
noncomputable def logMean (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, f n / n

/--
The von Mangoldt identity for the logarithmic average:
$$\sum_{n \le N} \frac{f(n)}{n}\log n
  = \sum_{d \le N} \frac{\Lambda(d)}{d} \sum_{m \le N/d} \frac{f(dm)}{m}.$$
-/
@[category API, AMS 11]
theorem sum_Icc_div_mul_log (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f n / n) * Real.log n
      = ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d / d)
          * ∑ m ∈ Icc 1 (N / d), f (d * m) / m := by
  rw [sum_Icc_mul_log (fun n ↦ f n / n) N]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
  have hdR : (0 : ℝ) ≠ d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    exact ne_of_lt this
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  field_simp

/--
Abel summation for the logarithmic average, as an exact identity:
$$\sum_{n \le N} \frac{f(n)}{n}\log n
  = L(N)\log N - \sum_{k < N} L(k)\bigl(\log(k+1) - \log k\bigr).$$
-/
@[category API, AMS 11]
theorem sum_div_mul_log_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f n / n) * Real.log n
      = logMean f N * Real.log N
        - ∑ k ∈ Ico 1 N, logMean f k * (Real.log (k + 1) - Real.log k) := by
  induction N with
  | zero => simp [logMean]
  | succ N ih =>
    have hL : logMean f (N + 1) = logMean f N + f (N + 1) / (N + 1) := by
      rw [logMean, logMean, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      ring
    have hsum : ∑ n ∈ Icc 1 (N + 1), (f n / n) * Real.log n
        = (∑ n ∈ Icc 1 N, (f n / n) * Real.log n)
          + (f (N + 1) / (N + 1)) * Real.log (N + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      ring
    have hIco : ∑ k ∈ Ico 1 (N + 1), logMean f k * (Real.log (k + 1) - Real.log k)
        = (∑ k ∈ Ico 1 N, logMean f k * (Real.log (k + 1) - Real.log k))
          + logMean f N * (Real.log (N + 1) - Real.log N) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [logMean]
      · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
    rw [hsum, ih, hL, hIco]
    push_cast
    ring

/-- The harmonic bound `∑_{n ≤ M} 1/n ≤ 1 + log M`. -/
@[category API, AMS 11]
theorem sum_one_div_le (M : ℕ) : ∑ n ∈ Icc 1 M, (1 : ℝ) / n ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- The multiples of `p` in `[1, M]` are exactly `p * j` for `j ≤ ⌊M/p⌋`. -/
@[category API, AMS 11]
theorem filter_dvd_eq_image {p M : ℕ} (hp : 0 < p) :
    {m ∈ Icc 1 M | p ∣ m} = (Icc 1 (M / p)).image (fun j ↦ p * j) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hm1, hmM⟩, j, rfl⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp at hm1
      · exact h
    exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hp).2 (by rw [Nat.mul_comm]; exact hmM)⟩, rfl⟩
  · rintro ⟨j, ⟨hj1, hjM⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hp] at hjM
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hp.ne' (by omega)), ?_⟩, ⟨j, rfl⟩⟩
    rw [Nat.mul_comm]; exact hjM

/--
Shifting by a prime in the logarithmic average:
$\sum_{m \le M} f(pm)/m$ differs from $f(p) L(M)$ by at most $(2/p)(1 + \log M)$.
-/
@[category API, AMS 11]
theorem abs_sum_div_shift_prime_sub_le (hf : IsPMOneMultiplicative f) {p M : ℕ}
    (hp : p.Prime) :
    |(∑ m ∈ Icc 1 M, f (p * m) / m) - f p * logMean f M| ≤ 2 / p * (1 + Real.log M) := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdiff : (∑ m ∈ Icc 1 M, f (p * m) / m) - f p * logMean f M
      = ∑ m ∈ Icc 1 M, (f (p * m) - f p * f m) / m := by
    rw [logMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  have hvanish : ∀ m ∈ Icc 1 M, m ∉ {m ∈ Icc 1 M | p ∣ m} → (f (p * m) - f p * f m) / m = 0 := by
    intro m hm hm'
    simp only [Finset.mem_filter] at hm'
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ hm' ⟨hm, h⟩
    rw [hf.map_mul_of_coprime p m hcop, sub_self, zero_div]
  rw [hdiff, ← Finset.sum_subset (Finset.filter_subset _ _) hvanish,
    filter_dvd_eq_image hp.pos,
    Finset.sum_image (fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Icc 1 (M / p), |(f (p * (p * j)) - f p * f (p * j)) / (p * j : ℕ)|
      ≤ ∑ j ∈ Icc 1 (M / p), (2 : ℝ) / p * (1 / j) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hj1 : 1 ≤ j := (mem_Icc.1 hj).1
        have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
        have h1 := abs_eq_one_of_one_le f hf (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hj1))
        have h2 := abs_eq_one_of_one_le f hf hp.one_lt.le
        have h3 := abs_eq_one_of_one_le f hf (Nat.mul_pos hp.pos hj1)
        rw [abs_div, Nat.cast_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (p : ℝ) * j)]
        have hnum : |f (p * (p * j)) - f p * f (p * j)| ≤ 2 := by
          calc |f (p * (p * j)) - f p * f (p * j)| ≤ |f (p * (p * j))| + |f p * f (p * j)| :=
                abs_sub _ _
          _ = 2 := by rw [h1, abs_mul, h2, h3]; norm_num
        have hprod : (2 : ℝ) / p * (1 / j) = 2 / ((p : ℝ) * j) := by field_simp
        rw [hprod]
        exact (div_le_div_iff_of_pos_right (by positivity)).2 hnum
  _ = (2 : ℝ) / p * ∑ j ∈ Icc 1 (M / p), (1 : ℝ) / j := (Finset.mul_sum _ _ _).symm
  _ ≤ 2 / p * (1 + Real.log M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (sum_one_div_le (M / p)).trans ?_
        have : ((M / p : ℕ) : ℝ) ≤ M := by
          exact_mod_cast Nat.div_le_self M p
        have hlog : Real.log ((M / p : ℕ) : ℝ) ≤ Real.log M := by
          rcases Nat.eq_zero_or_pos (M / p) with h | h
          · rw [h]
            simpa using Real.log_natCast_nonneg M
          · exact Real.log_le_log (by exact_mod_cast h) this
        linarith

/-- `log ⌊N/d⌋ ≤ log N`. -/
@[category API, AMS 11]
theorem log_natCast_div_le (N d : ℕ) : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos (N / d) with h | h
  · rw [h]
    simpa using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.div_le_self N d)

/-- The shifted logarithmic averages are bounded by `1 + log M`. -/
@[category API, AMS 11]
theorem abs_sum_div_shift_le (hf : IsPMOneMultiplicative f) {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    |∑ m ∈ Icc 1 M, f (d * m) / m| ≤ 1 + Real.log M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ Icc 1 M, |f (d * m) / m| = 1 / m := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    rw [abs_div, abs_eq_one_of_one_le f hf (Nat.mul_pos hd hm1), abs_of_nonneg hmR.le]
  rw [Finset.sum_congr rfl hterm]
  exact sum_one_div_le M

/--
The log-weighted relation for the logarithmic average:
$$\sum_{n \le N} \frac{f(n)}{n}\log n
  = \sum_{p \le N} \frac{\log p}{p} f(p)\, L(\lfloor N/p \rfloor) + O(\log N).$$
-/
@[category API, AMS 11]
theorem abs_sum_div_mul_log_sub_sum_prime_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, (f n / n) * Real.log n)
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (f p * logMean f (N / p))| ≤ 8 * (1 + Real.log N) := by
  classical
  have hlogN : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  have hsplit : ∑ d ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m
      = (∑ d ∈ (Icc 1 N).filter Nat.Prime,
          (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the proper prime powers
  have h1 : |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
      (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m|
      ≤ 4 * (1 + Real.log N) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          |(ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m|
        ≤ ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            (ArithmeticFunction.vonMangoldt d / d) * (1 + Real.log N) := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          have hd1 : 1 ≤ d := (mem_Icc.1 (mem_filter.1 hd).1).1
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
          have hnn : 0 ≤ ArithmeticFunction.vonMangoldt d / d :=
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg hdR.le
          rw [abs_mul, abs_of_nonneg hnn]
          refine mul_le_mul_of_nonneg_left ?_ hnn
          exact (abs_sum_div_shift_le f hf hd1 _).trans (by linarith [log_natCast_div_le N d])
    _ = (∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
          ArithmeticFunction.vonMangoldt d / d) * (1 + Real.log N) := (Finset.sum_mul _ _ _).symm
    _ ≤ 4 * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_right (Mertens.sum_vonMangoldt_div_nonprime_le N) hlogN
  -- the prime terms
  have hprime : (∑ d ∈ (Icc 1 N).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m :=
    Finset.sum_congr rfl fun d hd ↦ by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hd).2]
  have h2 : |(∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (f p * logMean f (N / p))| ≤ 4 * (1 + Real.log N) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          |Real.log p / p * (∑ m ∈ Icc 1 (N / p), f (p * m) / m)
            - Real.log p / p * (f p * logMean f (N / p))|
        ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
            2 * (1 + Real.log N) * (Real.log p / (p : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          have hpp : p.Prime := (mem_filter.1 hp).2
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
          have hnn : 0 ≤ Real.log p / p := div_nonneg hlog hpR.le
          rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
          have hshift := abs_sum_div_shift_prime_sub_le f hf (p := p) (M := N / p) hpp
          have hmono : 2 / (p : ℝ) * (1 + Real.log ((N / p : ℕ) : ℝ))
              ≤ 2 / (p : ℝ) * (1 + Real.log N) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith [log_natCast_div_le N p]
          calc Real.log p / p * |(∑ m ∈ Icc 1 (N / p), f (p * m) / m)
                - f p * logMean f (N / p)|
              ≤ Real.log p / p * (2 / (p : ℝ) * (1 + Real.log N)) :=
                mul_le_mul_of_nonneg_left (hshift.trans hmono) hnn
          _ = 2 * (1 + Real.log N) * (Real.log p / (p : ℝ) ^ 2) := by
                field_simp
    _ = 2 * (1 + Real.log N) * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / (p : ℝ) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (1 + Real.log N) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦
            div_nonneg (Real.log_natCast_nonneg _) (by positivity)).trans
            (Mertens.sum_log_div_sq_le N)
          intro q hq
          simp only [mem_filter, mem_Icc] at hq
          exact mem_Icc.2 ⟨hq.2.two_le, hq.1.2⟩
    _ = 4 * (1 + Real.log N) := by ring
  have hid := sum_Icc_div_mul_log f N
  rw [hsplit, hprime] at hid
  rw [hid]
  calc |(∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
      + (∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
        (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (f p * logMean f (N / p))|
      ≤ |(∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
          - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (f p * logMean f (N / p))|
        + |∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m| := by
        have := abs_add_le
          ((∑ p ∈ (Icc 1 N).filter Nat.Prime,
              Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (f p * logMean f (N / p)))
          (∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
            (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)
        calc |(∑ p ∈ (Icc 1 N).filter Nat.Prime,
              Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
            + (∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
              (ArithmeticFunction.vonMangoldt d / d) * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)
            - ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                Real.log p / p * (f p * logMean f (N / p))|
            = |((∑ p ∈ (Icc 1 N).filter Nat.Prime,
                  Real.log p / p * ∑ m ∈ Icc 1 (N / p), f (p * m) / m)
                - ∑ p ∈ (Icc 1 N).filter Nat.Prime,
                    Real.log p / p * (f p * logMean f (N / p)))
              + (∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime),
                  (ArithmeticFunction.vonMangoldt d / d)
                    * ∑ m ∈ Icc 1 (N / d), f (d * m) / m)| := by ring_nf
        _ ≤ _ := this
  _ ≤ 8 * (1 + Real.log N) := by linarith [h1, h2]

/-- The harmonic partial sum `∑_{n ≤ N} 1/n`. -/
noncomputable def harmonicSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (1 : ℝ) / n

@[category API, AMS 11]
theorem harmonicSum_sub (M N : ℕ) (h : M ≤ N) :
    harmonicSum N - harmonicSum M = ∑ n ∈ Ioc M N, (1 : ℝ) / n := by
  rw [harmonicSum, harmonicSum, (by rfl : Icc 1 N = Ioc 0 N), (by rfl : Icc 1 M = Ioc 0 M),
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]
  ring

/--
`L` is Lipschitz on the logarithmic scale: `|L(N) - L(M)| ≤ ∑_{M < n ≤ N} 1/n`.
This regularity is the reason route C works through the logarithmic average rather than
through `mean f`, which has no such control.
-/
@[category API, AMS 11]
theorem abs_logMean_sub_le (hf : IsPMOneMultiplicative f) {M N : ℕ} (h : M ≤ N) :
    |logMean f N - logMean f M| ≤ harmonicSum N - harmonicSum M := by
  have hsub : logMean f N - logMean f M = ∑ n ∈ Ioc M N, f n / n := by
    rw [logMean, logMean, (by rfl : Icc 1 N = Ioc 0 N), (by rfl : Icc 1 M = Ioc 0 M),
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]
    ring
  rw [hsub, harmonicSum_sub M N h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun n hn ↦ ?_)
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Ioc.1 hn).1
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [abs_div, abs_eq_one_of_one_le f hf hn1, abs_of_nonneg hnR.le]

/--
The total variation of `k ↦ L(⌊N/k⌋)` over `1 ≤ k < N` is at most `1 + log N`: the ranges
`(⌊N/(k+1)⌋, ⌊N/k⌋]` are consecutive, so the bound telescopes.
-/
@[category API, AMS 11]
theorem sum_abs_logMean_div_sub_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    ∑ k ∈ Ico 1 N, |logMean f (N / k) - logMean f (N / (k + 1))| ≤ 1 + Real.log N := by
  have hterm : ∀ k ∈ Ico 1 N, |logMean f (N / k) - logMean f (N / (k + 1))|
      ≤ harmonicSum (N / k) - harmonicSum (N / (k + 1)) := fun k hk ↦
    abs_logMean_sub_le f hf (Nat.div_le_div_left (Nat.le_succ k)
      (by have := (Finset.mem_Ico.1 hk).1; omega))
  calc ∑ k ∈ Ico 1 N, |logMean f (N / k) - logMean f (N / (k + 1))|
      ≤ ∑ k ∈ Ico 1 N, (harmonicSum (N / k) - harmonicSum (N / (k + 1))) :=
        Finset.sum_le_sum hterm
  _ = harmonicSum (N / 1) - harmonicSum (N / (1 + (N - 1))) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : ∀ i ∈ range (N - 1),
            harmonicSum (N / (1 + i)) - harmonicSum (N / (1 + i + 1))
              = (fun j ↦ harmonicSum (N / (1 + j))) i - (fun j ↦ harmonicSum (N / (1 + j))) (i + 1) := by
          intro i _
          simp only
          congr 2
        rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun j ↦ harmonicSum (N / (1 + j)))]
  _ ≤ 1 + Real.log N := by
        have h1 : harmonicSum (N / 1) ≤ 1 + Real.log N := by
          rw [Nat.div_one]
          exact sum_one_div_le N
        have h2 : 0 ≤ harmonicSum (N / (1 + (N - 1))) :=
          Finset.sum_nonneg fun n _ ↦ by positivity
        linarith

/--
The hyperbola region `{(d, m) : d m ≤ N}` is symmetric, so the two iterated sums agree.
-/
@[category API, AMS 11]
theorem sum_Icc_div_symm {M : Type*} [AddCommMonoid M] (G : ℕ → ℕ → M) (N : ℕ) :
    ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m
      = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G m d := by
  rw [← sum_Icc_divisorsAntidiagonal G N, ← sum_Icc_divisorsAntidiagonal (fun a b ↦ G b a) N]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  conv_rhs => rw [← Nat.map_swap_divisorsAntidiagonal]
  rw [Finset.sum_map]
  rfl

/--
The hyperbola identity for the logarithmic average:
$$\sum_{k \le N} \frac{1}{k} L(\lfloor N/k \rfloor)
  = \sum_{m \le N} \frac{f(m)}{m} H(\lfloor N/m \rfloor),$$
where `H` is the harmonic partial sum.  Both sides count the pairs `(k, m)` with `km ≤ N`
weighted by `f(m)/(km)`.
-/
@[category API, AMS 11]
theorem sum_one_div_mul_logMean_eq (N : ℕ) :
    ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k)
      = ∑ m ∈ Icc 1 N, f m / m * harmonicSum (N / m) := by
  have h := sum_Icc_div_symm (fun k m ↦ f m / (k * m : ℕ)) N
  calc ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k)
      = ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / k), f m / ((k : ℕ) * (m : ℕ) : ℕ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [logMean, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        push_cast
        ring
  _ = ∑ k ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / k), f k / ((m : ℕ) * (k : ℕ) : ℕ) := h
  _ = ∑ m ∈ Icc 1 N, f m / m * harmonicSum (N / m) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [harmonicSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        push_cast
        ring

/-- `log M ≤ ∑_{n ≤ M} 1/n`. -/
@[category API, AMS 11]
theorem log_le_harmonicSum (M : ℕ) : Real.log M ≤ harmonicSum M := by
  have h := log_add_one_le_harmonic M
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have hmono : Real.log M ≤ Real.log ((M : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · exact Real.log_le_log (by exact_mod_cast hM) (by linarith)
  refine hmono.trans (h.trans (le_of_eq ?_))
  exact Finset.sum_congr rfl fun n _ ↦ by rw [one_div]

/--
`H(⌊N/m⌋)` is `log N - log m` up to `1`, for `1 ≤ m ≤ N`.
-/
@[category API, AMS 11]
theorem abs_harmonicSum_div_sub_le {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    |harmonicSum (N / m) - (Real.log N - Real.log m)| ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hm hmN
  have hq : 1 ≤ N / m := (Nat.one_le_div_iff (by omega)).2 hmN
  have hqR : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
  have hlogdiff : Real.log N - Real.log m = Real.log ((N : ℝ) / m) :=
    (Real.log_div (ne_of_gt hNR) (ne_of_gt hmR)).symm
  have hupper : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hlower : (N : ℝ) / m < 2 * ((N / m : ℕ) : ℝ) := by
    have hmod : N % m < m := Nat.mod_lt _ (by omega)
    have hdm := Nat.div_add_mod N m
    have hlt : N < m * (2 * (N / m)) := by
      have : 1 ≤ N / m := hq
      nlinarith [hdm, hmod, this]
    have hltR : (N : ℝ) < (m : ℝ) * (2 * ((N / m : ℕ) : ℝ)) := by exact_mod_cast hlt
    rw [div_lt_iff₀ hmR]
    linarith
  have h1 : Real.log ((N / m : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / m) :=
    Real.log_le_log (by linarith) hupper
  have h2 : Real.log ((N : ℝ) / m) ≤ Real.log 2 + Real.log ((N / m : ℕ) : ℝ) := by
    have := Real.log_le_log (by positivity) hlower.le
    rwa [Real.log_mul (by norm_num) (by linarith)] at this
  have h3 : Real.log ((N / m : ℕ) : ℝ) ≤ harmonicSum (N / m) := log_le_harmonicSum _
  have h4 : harmonicSum (N / m) ≤ 1 + Real.log ((N / m : ℕ) : ℝ) := sum_one_div_le _
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  rw [hlogdiff, abs_le]
  constructor <;> linarith

/--
The hyperbola identity in usable form:
$$\sum_{k \le N} \frac{1}{k} L(\lfloor N/k \rfloor)
  = L(N)\log N - \sum_{n \le N}\frac{f(n)}{n}\log n + O(\log N).$$
-/
@[category API, AMS 11]
theorem abs_sum_one_div_mul_logMean_sub_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |(∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k))
      - (logMean f N * Real.log N - ∑ n ∈ Icc 1 N, (f n / n) * Real.log n)|
      ≤ 1 + Real.log N := by
  have hmain : logMean f N * Real.log N - ∑ n ∈ Icc 1 N, (f n / n) * Real.log n
      = ∑ m ∈ Icc 1 N, f m / m * (Real.log N - Real.log m) := by
    rw [logMean, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  rw [sum_one_div_mul_logMean_eq f N, hmain, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Icc 1 N, |f m / m * harmonicSum (N / m) - f m / m * (Real.log N - Real.log m)|
      ≤ ∑ m ∈ Icc 1 N, (1 : ℝ) / m := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
        have hmN : m ≤ N := (mem_Icc.1 hm).2
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
        rw [← mul_sub, abs_mul, abs_div, abs_eq_one_of_one_le f hf hm1,
          abs_of_nonneg hmR.le]
        calc 1 / (m : ℝ) * |harmonicSum (N / m) - (Real.log N - Real.log m)|
            ≤ 1 / (m : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (abs_harmonicSum_div_sub_le hm1 hmN) (by positivity)
        _ = 1 / (m : ℝ) := mul_one _
  _ ≤ 1 + Real.log N := sum_one_div_le N

section Abel

variable (w g : ℕ → ℝ)

/-- **Summation by parts** with partial sums taken over `Icc 1 n`. -/
@[category API, AMS 11]
theorem sum_Icc_by_parts (N : ℕ) :
    ∑ k ∈ Icc 1 N, w k * g k
      = (∑ k ∈ Icc 1 N, w k) * g N
        - ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w j) * (g (k + 1) - g k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hW : ∑ k ∈ Icc 1 (N + 1), w k = (∑ k ∈ Icc 1 N, w k) + w (N + 1) :=
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) _
    have hL : ∑ k ∈ Icc 1 (N + 1), w k * g k
        = (∑ k ∈ Icc 1 N, w k * g k) + w (N + 1) * g (N + 1) :=
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) _
    have hIco : ∑ k ∈ Ico 1 (N + 1), (∑ j ∈ Icc 1 k, w j) * (g (k + 1) - g k)
        = (∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w j) * (g (k + 1) - g k))
          + (∑ j ∈ Icc 1 N, w j) * (g (N + 1) - g N) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · exact Finset.sum_Ico_succ_top (by omega : 1 ≤ N) _
    rw [hL, ih, hW, hIco]
    ring

/--
Comparing two weight systems: if their partial sums agree up to `c`, the weighted sums of
`g` agree up to `c` times the size plus the total variation of `g`.
-/
@[category API, AMS 11]
theorem abs_sum_weight_sub_le (w' : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hc : ∀ n ≤ N, |(∑ k ∈ Icc 1 n, w k) - ∑ k ∈ Icc 1 n, w' k| ≤ c) :
    |(∑ k ∈ Icc 1 N, w k * g k) - ∑ k ∈ Icc 1 N, w' k * g k|
      ≤ c * |g N| + c * ∑ k ∈ Ico 1 N, |g (k + 1) - g k| := by
  rw [sum_Icc_by_parts w g N, sum_Icc_by_parts w' g N]
  have hrw : ((∑ k ∈ Icc 1 N, w k) * g N
        - ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w j) * (g (k + 1) - g k))
      - ((∑ k ∈ Icc 1 N, w' k) * g N
        - ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w' j) * (g (k + 1) - g k))
      = ((∑ k ∈ Icc 1 N, w k) - ∑ k ∈ Icc 1 N, w' k) * g N
        - ∑ k ∈ Ico 1 N,
            ((∑ j ∈ Icc 1 k, w j) - ∑ j ∈ Icc 1 k, w' j) * (g (k + 1) - g k) := by
    have hsum : (∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w j) * (g (k + 1) - g k))
        - ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, w' j) * (g (k + 1) - g k)
        = ∑ k ∈ Ico 1 N,
            ((∑ j ∈ Icc 1 k, w j) - ∑ j ∈ Icc 1 k, w' j) * (g (k + 1) - g k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [← hsum]
    ring
  rw [hrw]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc N le_rfl) (abs_nonneg _)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkN : k ≤ N := le_of_lt (mem_Ico.1 hk).2
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc k hkN) (abs_nonneg _)

end Abel

@[category API, AMS 11]
theorem abs_logMean_le (hf : IsPMOneMultiplicative f) (M : ℕ) :
    |logMean f M| ≤ 1 + Real.log M := by
  have h := abs_logMean_sub_le f hf (Nat.zero_le M)
  have h0 : logMean f 0 = 0 := by simp [logMean]
  have h0' : harmonicSum 0 = 0 := by simp [harmonicSum]
  rw [h0, h0', sub_zero, sub_zero] at h
  exact h.trans (sum_one_div_le M)

open scoped Classical in
/-- The prime weights `log p / p`, extended by zero to all of `ℕ`. -/
noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

open scoped Classical in
@[category API, AMS 11]
theorem sum_primeWeight_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, primeWeight k * g k
      = ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p / p * g p := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [primeWeight]; split_ifs <;> ring

open scoped Classical in
@[category API, AMS 11]
theorem abs_sum_primeWeight_sub_harmonicSum_le (n : ℕ) :
    |(∑ k ∈ Icc 1 n, primeWeight k) - harmonicSum n| ≤ Real.log 4 + 9 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [harmonicSum]
    norm_num
    linarith
  have hprime : ∑ k ∈ Icc 1 n, primeWeight k
      = ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p / p := by
    have := sum_primeWeight_mul (fun _ ↦ (1 : ℝ)) n
    simpa using this
  have h1 := Mertens.abs_sum_log_prime_div_sub_log_le (N := n) hn
  have h2 : Real.log n ≤ harmonicSum n := log_le_harmonicSum n
  have h3 : harmonicSum n ≤ 1 + Real.log n := sum_one_div_le n
  rw [hprime, abs_le] at *
  constructor <;> linarith [h1.1, h1.2]

/--
Replacing the prime weights `log p / p` by the harmonic weights `1/k` in
`∑ L(⌊N/k⌋)` costs `O(log N)`: by Mertens both weight systems have partial sums
`log n + O(1)`, and `k ↦ L(⌊N/k⌋)` has total variation at most `1 + log N`.
-/
@[category API, AMS 11]
theorem abs_sum_prime_sub_sum_one_div_logMean_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * logMean f (N / p))
      - ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k)|
      ≤ 2 * (Real.log 4 + 9) * (1 + Real.log N) := by
  classical
  set c := Real.log 4 + 9 with hc
  set g : ℕ → ℝ := fun k ↦ logMean f (N / k) with hg
  have hcnn : 0 ≤ c := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hc]; linarith
  have hkey := abs_sum_weight_sub_le primeWeight g (fun k ↦ (1 : ℝ) / k) N c
    (fun n _ ↦ abs_sum_primeWeight_sub_harmonicSum_le n)
  rw [sum_primeWeight_mul] at hkey
  have hvar : ∑ k ∈ Ico 1 N, |g (k + 1) - g k| ≤ 1 + Real.log N := by
    have h := sum_abs_logMean_div_sub_le f hf N
    calc ∑ k ∈ Ico 1 N, |g (k + 1) - g k|
        = ∑ k ∈ Ico 1 N, |logMean f (N / k) - logMean f (N / (k + 1))| :=
          Finset.sum_congr rfl fun k _ ↦ abs_sub_comm _ _
    _ ≤ 1 + Real.log N := h
  have hgN : |g N| ≤ 1 + Real.log N := (abs_logMean_le f hf (N / N)).trans (by
    have := log_natCast_div_le N N
    linarith)
  calc |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * logMean f (N / p))
      - ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k)|
      ≤ c * |g N| + c * ∑ k ∈ Ico 1 N, |g (k + 1) - g k| := hkey
  _ ≤ c * (1 + Real.log N) + c * (1 + Real.log N) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hgN hcnn)
          (mul_le_mul_of_nonneg_left hvar hcnn)
  _ = 2 * c * (1 + Real.log N) := by ring

/-- `∑_{k ≤ N} 1/(2k²) ≤ 1`, by telescoping `1/k² ≤ 1/(k-1) - 1/k`. -/
@[category API, AMS 11]
theorem sum_one_div_two_sq_le (N : ℕ) : ∑ k ∈ Icc 1 N, (1 : ℝ) / (2 * k ^ 2) ≤ 1 := by
  have key : ∀ M : ℕ, 1 ≤ M → ∑ k ∈ Icc 1 M, (1 : ℝ) / (2 * k ^ 2) ≤ 1 - 1 / (2 * (M : ℝ)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hstep : (1 : ℝ) / (2 * ((M : ℝ) + 1) ^ 2) ≤ 1 / (2 * (M : ℝ)) - 1 / (2 * ((M : ℝ) + 1)) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hMR]
      linarith [ih]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  linarith [key N hN]

/-- `(log (N+1))²/2 ≤ ∑_{k ≤ N} log k / k + ∑_{k ≤ N} 1/(2k²)`. -/
@[category API, AMS 11]
theorem sq_log_succ_le (N : ℕ) :
    Real.log (N + 1) ^ 2 / 2
      ≤ (∑ k ∈ Icc 1 N, Real.log k / k) + ∑ k ∈ Icc 1 N, (1 : ℝ) / (2 * k ^ 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hpos : (0 : ℝ) < N + 1 := by positivity
    have hpos2 : (0 : ℝ) < N + 2 := by positivity
    have hne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hpos
    have hdiv : Real.log ((N + 2) / (N + 1)) = Real.log (N + 2) - Real.log (N + 1) :=
      Real.log_div (ne_of_gt hpos2) hne
    have hstep : Real.log (N + 2) - Real.log (N + 1) ≤ 1 / (N + 1) := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (N + 2) / (N + 1) by positivity)
      rw [hdiv] at this
      have harith : ((N : ℝ) + 2) / (N + 1) - 1 = 1 / (N + 1) := by
        field_simp
        ring
      linarith [this, harith.le, harith.ge]
    have hnn1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hnn2 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hmono : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log hpos (by linarith)
    have hkey : Real.log ((N : ℝ) + 2) ^ 2 / 2 - Real.log ((N : ℝ) + 1) ^ 2 / 2
        ≤ Real.log ((N : ℝ) + 1) / (N + 1) + 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
      have hfac : Real.log ((N : ℝ) + 2) ^ 2 - Real.log ((N : ℝ) + 1) ^ 2
          = (Real.log (N + 2) - Real.log (N + 1)) * (Real.log (N + 2) + Real.log (N + 1)) := by
        ring
      have hbd : Real.log ((N : ℝ) + 2) + Real.log ((N : ℝ) + 1)
          ≤ 2 * Real.log ((N : ℝ) + 1) + 1 / (N + 1) := by linarith
      have hd0 : 0 ≤ Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) := by linarith
      have hprod : (Real.log ((N:ℝ) + 2) - Real.log (N + 1)) * (Real.log (N + 2) + Real.log (N + 1))
          ≤ (1 / ((N : ℝ) + 1)) * (2 * Real.log ((N : ℝ) + 1) + 1 / (N + 1)) := by
        refine mul_le_mul hstep hbd (by linarith) (by positivity)
      have hrw : (1 / ((N : ℝ) + 1)) * (2 * Real.log ((N : ℝ) + 1) + 1 / (N + 1))
          = 2 * (Real.log ((N : ℝ) + 1) / (N + 1) + 1 / (2 * ((N : ℝ) + 1) ^ 2)) := by
        field_simp
      nlinarith [hfac, hprod, hrw]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hcast1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast1]
    have hcast2 : Real.log ((N : ℝ) + 1 + 1) = Real.log ((N : ℝ) + 2) := by
      congr 1
      ring
    rw [hcast2]
    linarith [ih, hkey]

/-- `∑_{k ≤ N} 1/k² ≤ 2`. -/
@[category API, AMS 11]
theorem sum_one_div_sq_le (N : ℕ) : ∑ k ∈ Icc 1 N, (1 : ℝ) / k ^ 2 ≤ 2 := by
  have h := sum_one_div_two_sq_le N
  have hrw : ∑ k ∈ Icc 1 N, (1 : ℝ) / (2 * k ^ 2) = (∑ k ∈ Icc 1 N, (1 : ℝ) / k ^ 2) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hrw] at h
  linarith

/-- The matching upper bound `∑_{k ≤ N} log k / k ≤ (log N)²/2 + ∑_{k ≤ N} 1/k²`. -/
@[category API, AMS 11]
theorem sum_log_div_le_sq_log_aux (N : ℕ) :
    (∑ k ∈ Icc 1 N, Real.log k / k)
      ≤ Real.log N ^ 2 / 2 + ∑ k ∈ Icc 1 N, (1 : ℝ) / k ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hpos1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    set a := Real.log (N : ℝ) with ha
    set b := Real.log ((N : ℝ) + 1) with hb
    have hab : a ≤ b := Real.log_le_log hpos (by linarith)
    have hann : 0 ≤ a := Real.log_nonneg hNR
    -- `log(1 + 1/N) ≥ 1/(N+1)`
    have hlow : 1 / ((N : ℝ) + 1) ≤ b - a := by
      have hd : Real.log (((N : ℝ) + 1) / N) = b - a := Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos)
      have h1 : Real.log ((N : ℝ) / ((N : ℝ) + 1)) ≤ (N : ℝ) / ((N : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log ((N : ℝ) / ((N : ℝ) + 1)) = a - b :=
        Real.log_div (ne_of_gt hpos) (ne_of_gt hpos1)
      rw [h2] at h1
      have h3 : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by
        field_simp
        ring
      linarith [h1, h3.le, h3.ge]
    -- `log(1 + 1/N) ≤ 1/N`
    have hhigh : b - a ≤ 1 / (N : ℝ) := by
      have h1 : Real.log (((N : ℝ) + 1) / N) ≤ ((N : ℝ) + 1) / N - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (((N : ℝ) + 1) / N) = b - a :=
        Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos)
      have h3 : ((N : ℝ) + 1) / N - 1 = 1 / (N : ℝ) := by
        field_simp
        ring
      rw [h2] at h1
      linarith [h1, h3.le, h3.ge]
    have hkey : b / ((N : ℝ) + 1) ≤ (b ^ 2 - a ^ 2) / 2 + 1 / ((N : ℝ) + 1) ^ 2 := by
      have hfac : (b ^ 2 - a ^ 2) / 2 = (b - a) * (b + a) / 2 := by ring
      have hsum : 2 * b - 1 / (N : ℝ) ≤ b + a := by linarith
      have hb2 : Real.log 2 ≤ b := Real.log_le_log (by norm_num) (by linarith)
      have hb12 : (1 : ℝ) / 2 < b := by
        have := Real.log_two_gt_d9
        linarith
      have hinvN : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hpos]; linarith
      have hprod : (1 / ((N : ℝ) + 1)) * (2 * b - 1 / (N : ℝ)) ≤ (b - a) * (b + a) := by
        refine mul_le_mul hlow hsum (by linarith) (by linarith)
      have hexp : (1 / ((N : ℝ) + 1)) * (2 * b - 1 / (N : ℝ)) / 2
          = b / ((N : ℝ) + 1) - 1 / (2 * (N : ℝ) * ((N : ℝ) + 1)) := by
        field_simp
      have hslack : 1 / (2 * (N : ℝ) * ((N : ℝ) + 1)) ≤ 1 / ((N : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hNR]
      linarith [hprod, hexp.le, hexp.ge, hslack]
    linarith [ih, hkey]

/-- `∑_{k ≤ N} log k / k ≤ (log N)²/2 + 2`. -/
@[category API, AMS 11]
theorem sum_log_div_le_sq_log (N : ℕ) :
    (∑ k ∈ Icc 1 N, Real.log k / k) ≤ Real.log N ^ 2 / 2 + 2 := by
  linarith [sum_log_div_le_sq_log_aux N, sum_one_div_sq_le N]

/-- `(log N)²/2 ≤ ∑_{k ≤ N} log k / k + 1`: the lower bound for the log-weighted harmonic
sum, with no integral comparison. -/
@[category API, AMS 11]
theorem sq_log_le_sum_log_div (N : ℕ) :
    Real.log N ^ 2 / 2 ≤ (∑ k ∈ Icc 1 N, Real.log k / k) + 1 := by
  have h1 := sq_log_succ_le N
  have h2 := sum_one_div_two_sq_le N
  have h3 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have : (0 : ℝ) < N := by exact_mod_cast hN
      exact Real.log_le_log this (by linarith)
  have h4 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  nlinarith [h1, h2, h3, h4]

/-- The harmonic profile: `∑_{k ≤ N} (1/k)(1 + log N - log k) ≤ (log N)²/2 + 2 log N + 2`.

This is the value of the right-hand side of `abs_logMean_mul_log_le_of_forall` for the
profile `φ(M) = 1 + log M`, after the prime weights have been replaced by the harmonic
weights.  The gain of the Gronwall iteration is the difference between this and the trivial
`(1 + log N)·log N`. -/
@[category API, AMS 11]
theorem sum_one_div_mul_profile_le (N : ℕ) :
    ∑ k ∈ Icc 1 N, (1 : ℝ) / k * (1 + Real.log N - Real.log k)
      ≤ Real.log N ^ 2 / 2 + 2 * Real.log N + 2 := by
  have hsplit : ∑ k ∈ Icc 1 N, (1 : ℝ) / k * (1 + Real.log N - Real.log k)
      = (1 + Real.log N) * (∑ k ∈ Icc 1 N, (1 : ℝ) / k)
        - ∑ k ∈ Icc 1 N, Real.log k / k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    field_simp
  have h1 := sum_one_div_le (M := N)
  have h2 := sq_log_le_sum_log_div N
  have h3 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  rw [hsplit]
  nlinarith [h1, h2, h3]

/-- `log` is monotone along `ℕ` casts, including at `0`. -/
@[category API, AMS 11]
theorem log_natCast_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · have haR : (0 : ℝ) < a := by exact_mod_cast ha
    exact Real.log_le_log haR (by exact_mod_cast h)

/-- The total variation of `k ↦ 1 + log ⌊N/k⌋` on `[1, N]` is at most `log N`. -/
@[category API, AMS 11]
theorem sum_abs_log_div_sub_le (N : ℕ) :
    ∑ k ∈ Ico 1 N, |(1 + Real.log ((N / (k + 1) : ℕ) : ℝ)) - (1 + Real.log ((N / k : ℕ) : ℝ))|
      ≤ Real.log N := by
  have hterm : ∀ k ∈ Ico 1 N,
      |(1 + Real.log ((N / (k + 1) : ℕ) : ℝ)) - (1 + Real.log ((N / k : ℕ) : ℝ))|
        = Real.log ((N / k : ℕ) : ℝ) - Real.log ((N / (k + 1) : ℕ) : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
    have hmono : Real.log ((N / (k + 1) : ℕ) : ℝ) ≤ Real.log ((N / k : ℕ) : ℝ) :=
      log_natCast_mono (Nat.div_le_div_left (Nat.le_succ k) (by omega))
    rw [abs_of_nonpos (by linarith)]
    ring
  calc ∑ k ∈ Ico 1 N,
        |(1 + Real.log ((N / (k + 1) : ℕ) : ℝ)) - (1 + Real.log ((N / k : ℕ) : ℝ))|
      = ∑ k ∈ Ico 1 N, (Real.log ((N / k : ℕ) : ℝ) - Real.log ((N / (k + 1) : ℕ) : ℝ)) :=
        Finset.sum_congr rfl hterm
  _ = Real.log ((N / 1 : ℕ) : ℝ) - Real.log ((N / (1 + (N - 1)) : ℕ) : ℝ) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : ∀ i ∈ range (N - 1),
            Real.log ((N / (1 + i) : ℕ) : ℝ) - Real.log ((N / (1 + i + 1) : ℕ) : ℝ)
              = (fun j ↦ Real.log ((N / (1 + j) : ℕ) : ℝ)) i
                - (fun j ↦ Real.log ((N / (1 + j) : ℕ) : ℝ)) (i + 1) := by
          intro i _
          simp only
          congr 2
        rw [Finset.sum_congr rfl this,
          Finset.sum_range_sub' (fun j ↦ Real.log ((N / (1 + j) : ℕ) : ℝ))]
  _ ≤ Real.log N := by
        have h2 : 0 ≤ Real.log ((N / (1 + (N - 1)) : ℕ) : ℝ) := Real.log_natCast_nonneg _
        rw [Nat.div_one]
        linarith

/--
The prime-weighted profile sum: replacing the harmonic weights by the prime weights
`log p / p` in `Wirsing.sum_one_div_mul_profile_le` costs `O(log N)`.
$$\sum_{p \le N} \frac{\log p}{p}\bigl(1 + \log\lfloor N/p\rfloor\bigr)
  \le \tfrac12 (\log N)^2 + O(\log N).$$
-/
@[category API, AMS 11]
theorem sum_primeWeight_mul_profile_le (N : ℕ) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ)))
      ≤ Real.log N ^ 2 / 2 + (11 + Real.log 4) * (1 + Real.log N) := by
  classical
  set c := Real.log 4 + 9 with hc
  set g : ℕ → ℝ := fun k ↦ 1 + Real.log ((N / k : ℕ) : ℝ) with hg
  have hcnn : 0 ≤ c := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hc]; linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hkey := abs_sum_weight_sub_le primeWeight g (fun k ↦ (1 : ℝ) / k) N c
    (fun n _ ↦ abs_sum_primeWeight_sub_harmonicSum_le n)
  rw [sum_primeWeight_mul] at hkey
  have hgN : |g N| ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [hg]
    · rw [hg]
      simp only [Nat.div_self hN, Nat.cast_one, Real.log_one, add_zero, abs_one]
      exact le_rfl
  have hvar : ∑ k ∈ Ico 1 N, |g (k + 1) - g k| ≤ Real.log N := sum_abs_log_div_sub_le N
  -- the harmonic side
  have hharm : (∑ k ∈ Icc 1 N, (1 : ℝ) / k * g k)
      ≤ Real.log N ^ 2 / 2 + 2 * Real.log N + 2 := by
    refine le_trans (Finset.sum_le_sum fun k hk ↦ ?_) (sum_one_div_mul_profile_le N)
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hkN : k ≤ N := (mem_Icc.1 hk).2
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle : Real.log ((N / k : ℕ) : ℝ) ≤ Real.log N - Real.log k := by
      have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hk1 hkN
      have hNk : (0 : ℝ) < (N : ℝ) / k := by positivity
      have hdpos : 1 ≤ N / k := Nat.one_le_div_iff (by omega) |>.2 hkN
      have hdposR : (0 : ℝ) < ((N / k : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((N / k : ℕ) : ℝ) := by exact_mod_cast hdpos
        linarith
      have := Real.log_le_log hdposR hdiv
      rwa [Real.log_div (ne_of_gt hNpos) (ne_of_gt hkR)] at this
    rw [hg]
    linarith
  have hsum := abs_le.1 hkey
  have : (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * g p)
      ≤ (∑ k ∈ Icc 1 N, (1 : ℝ) / k * g k) + (c * |g N| + c * ∑ k ∈ Ico 1 N, |g (k + 1) - g k|) := by
    linarith [hsum.2]
  have hcbd : c * |g N| + c * ∑ k ∈ Ico 1 N, |g (k + 1) - g k| ≤ c * (1 + Real.log N) := by
    have h1 : c * |g N| ≤ c * 1 := mul_le_mul_of_nonneg_left hgN hcnn
    have h2 : c * ∑ k ∈ Ico 1 N, |g (k + 1) - g k| ≤ c * Real.log N :=
      mul_le_mul_of_nonneg_left hvar hcnn
    linarith
  have hfinal : (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * g p)
      ≤ Real.log N ^ 2 / 2 + 2 * Real.log N + 2 + c * (1 + Real.log N) := by linarith
  simp only [hg] at hfinal ⊢
  rw [hc] at hfinal
  linarith

/--
**The engine identity of route C.**  For every `±1`-valued multiplicative `f`,
$$L(N)\log N = \sum_{p \le N} \frac{\log p}{p}\,(1 + f(p))\,L(\lfloor N/p\rfloor) + O(\log N).$$

The defect weight `1 + f(p)` vanishes exactly on the primes with `f(p) = -1`, which are the
primes counted by the divergent series of Wirsing's hypothesis.  All three inputs
(`abs_sum_div_mul_log_sub_sum_prime_le`, `abs_sum_prime_sub_sum_one_div_logMean_le`,
`abs_sum_one_div_mul_logMean_sub_le`) compose so that the log-weighted sum
`∑_{n ≤ N} f(n)\log n / n` and the harmonic sum `∑_{k ≤ N} L(⌊N/k⌋)/k` both cancel.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_sub_defect_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |logMean f N * Real.log N
      - ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * ((1 + f p) * logMean f (N / p))|
      ≤ (27 + 2 * Real.log 4) * (1 + Real.log N) := by
  classical
  set P := ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * logMean f (N / p) with hP
  set B := ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k) with hB
  set S := ∑ n ∈ Icc 1 N, (f n / n) * Real.log n with hS
  set T := logMean f N * Real.log N with hT
  set D := ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    Real.log p / p * ((1 + f p) * logMean f (N / p)) with hD
  have hsign : (∑ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * (f p * logMean f (N / p))) = D - P := by
    rw [hD, hP, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  have e1 := abs_sum_div_mul_log_sub_sum_prime_le f hf N
  rw [hsign, ← hS] at e1
  have e2 := abs_sum_prime_sub_sum_one_div_logMean_le f hf N
  rw [← hP, ← hB] at e2
  have e3 := abs_sum_one_div_mul_logMean_sub_le f hf N
  rw [← hB, ← hS, ← hT] at e3
  have t1 := abs_sub ((S - (D - P)) - (P - B)) (B - (T - S))
  have t2 := abs_sub (S - (D - P)) (P - B)
  have hid : T - D = (S - (D - P)) - (P - B) - (B - (T - S)) := by ring
  have habs : |T - D| ≤ |S - (D - P)| + |P - B| + |B - (T - S)| := by
    rw [hid]; linarith [t1, t2]
  have hlogN : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  calc |T - D| ≤ |S - (D - P)| + |P - B| + |B - (T - S)| := habs
  _ ≤ 8 * (1 + Real.log N) + 2 * (Real.log 4 + 9) * (1 + Real.log N) + (1 + Real.log N) := by
        linarith [e1, e2, e3]
  _ = (27 + 2 * Real.log 4) * (1 + Real.log N) := by ring

/--
**The model case of route C.**  If `f(p) = -1` for every prime `p`, then
$L(N)\log N = O(\log N)$, so the logarithmic average $L(N) = \sum_{n \le N} f(n)/n$ stays
bounded.

This is the first genuine gain of the log-weighted route: the naive `limsup` argument
applied to `mean f` only ever gives `A ≤ A`, whereas here the defect weight `1 + f(p)` of
`abs_logMean_mul_log_sub_defect_le` vanishes identically and leaves a factor `log N` of room.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le (hf : IsPMOneMultiplicative f)
    (hneg : ∀ p : ℕ, p.Prime → f p = -1) (N : ℕ) :
    |logMean f N * Real.log N| ≤ (27 + 2 * Real.log 4) * (1 + Real.log N) := by
  classical
  have h := abs_logMean_mul_log_sub_defect_le f hf N
  have hzero : (∑ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 + f p) * logMean f (N / p))) = 0 := by
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    rw [hneg p (mem_filter.1 hp).2]
    ring
  rwa [hzero, sub_zero] at h

/--
**The induction step of route C.**  If `|L(M)| ≤ φ(M)` for every `M ≤ N`, the engine
identity turns that into a bound for `|L(N)| \log N` with the defect weights
`(\log p / p)(1 + f p)`, which are nonnegative and vanish on the primes with `f(p) = -1`.

This is the inequality that the Gronwall iteration for
`Wirsing.tendsto_logMean_div_log_atTop_zero` is applied to.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_of_forall (hf : IsPMOneMultiplicative f) {N : ℕ} (φ : ℕ → ℝ)
    (hφ : ∀ p ∈ (Icc 1 N).filter Nat.Prime, |logMean f (N / p)| ≤ φ (N / p)) :
    |logMean f N| * Real.log N
      ≤ (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * φ (N / p)))
        + (27 + 2 * Real.log 4) * (1 + Real.log N) := by
  classical
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hmain := abs_logMean_mul_log_sub_defect_le f hf N
  have hD : |∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 + f p) * logMean f (N / p))|
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * φ (N / p)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    have hpmem := mem_filter.1 hp
    have hpp : p.Prime := hpmem.2
    have hp1 : 1 ≤ p := hpp.one_lt.le.trans' (by norm_num)
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hwnn : 0 ≤ Real.log p / p :=
      div_nonneg (Real.log_nonneg hpR) (by positivity)
    have hfp := hf.pmOne p hp1
    have hsnn : 0 ≤ 1 + f p := by rcases hfp with h | h <;> rw [h] <;> norm_num
    have hle : |logMean f (N / p)| ≤ φ (N / p) := hφ p hp
    rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg hsnn]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hsnn) hwnn
  have habs : |logMean f N * Real.log N| ≤
      |∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * logMean f (N / p))|
        + (27 + 2 * Real.log 4) * (1 + Real.log N) := by
    have := abs_sub_abs_le_abs_sub (logMean f N * Real.log N)
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * logMean f (N / p)))
    linarith
  rw [abs_mul, abs_of_nonneg hlog] at habs
  linarith [hD]

/-- `abs_logMean_mul_log_le_of_forall` with the hypothesis in the form `∀ M ≤ N`. -/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_of_forall_le (hf : IsPMOneMultiplicative f) {N : ℕ} (φ : ℕ → ℝ)
    (hφ : ∀ M ≤ N, |logMean f M| ≤ φ M) :
    |logMean f N| * Real.log N
      ≤ (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * φ (N / p)))
        + (27 + 2 * Real.log 4) * (1 + Real.log N) :=
  abs_logMean_mul_log_le_of_forall f hf φ fun _ _ ↦ hφ _ (Nat.div_le_self _ _)

/-- `abs_logMean_mul_log_le_of_forall` with the hypothesis only for smaller arguments, the
form needed by a strong induction. -/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_of_forall_lt (hf : IsPMOneMultiplicative f) {N : ℕ} (hN : 1 ≤ N)
    (φ : ℕ → ℝ) (hφ : ∀ M < N, |logMean f M| ≤ φ M) :
    |logMean f N| * Real.log N
      ≤ (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * ((1 + f p) * φ (N / p)))
        + (27 + 2 * Real.log 4) * (1 + Real.log N) := by
  classical
  refine abs_logMean_mul_log_le_of_forall f hf φ fun p hp ↦ hφ _ ?_
  have hpp : p.Prime := (mem_filter.1 hp).2
  exact Nat.div_lt_self (by omega) hpp.one_lt

open scoped Classical in
/-- Mertens' first theorem with a negative error, in the form used here:
`∑_{p ≤ k} log p / p ≤ log k` for `k ≥ 10 ^ 10`. -/
@[category API, AMS 11]
theorem sum_primeWeight_le_log {k : ℕ} (hk : 10 ^ 10 ≤ k) :
    ∑ j ∈ Icc 1 k, primeWeight j ≤ Real.log k := by
  classical
  have hkR : ((10 : ℝ) ^ 10) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmain := Mertens.sum_log_prime_div_le_log hkR
  have hfloor : Ioc 0 ⌊(k : ℝ)⌋₊ = Icc 1 k := by
    rw [Nat.floor_natCast]
    rfl
  rw [hfloor] at hmain
  have hrw := sum_primeWeight_mul (fun _ ↦ (1 : ℝ)) k
  simp only [mul_one] at hrw
  rw [hrw]
  exact hmain

open scoped Classical in
/-- The uniform bound `∑_{p ≤ k} log p / p ≤ log k + (log 4 + 8) · 10 ^ 10 / k`, which is the
sharp bound for `k ≥ 10 ^ 10` and the crude one below it. -/
@[category API, AMS 11]
theorem sum_primeWeight_le_log_add {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Icc 1 k, primeWeight j ≤ Real.log k + (Real.log 4 + 8) * (10 ^ 10 / (k : ℝ)) := by
  classical
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hc : (0 : ℝ) ≤ Real.log 4 + 8 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  rcases Nat.lt_or_ge k (10 ^ 10) with hlt | hge
  · have hcrude := Mertens.abs_sum_log_prime_div_sub_log_le hk
    have hrw := sum_primeWeight_mul (fun _ ↦ (1 : ℝ)) k
    simp only [mul_one] at hrw
    have hratio : (1 : ℝ) ≤ 10 ^ 10 / (k : ℝ) := by
      rw [le_div_iff₀ (by linarith)]
      have : (k : ℝ) ≤ 10 ^ 10 := by exact_mod_cast hlt.le
      linarith
    rw [hrw]
    have := (abs_le.1 hcrude).2
    nlinarith [hc, hratio]
  · have hsharp := sum_primeWeight_le_log hge
    have hnn : (0 : ℝ) ≤ (Real.log 4 + 8) * (10 ^ 10 / (k : ℝ)) := by positivity
    linarith

open scoped Classical in
/--
**The sharp profile sum.**  With the negative-error form of Mertens' theorem,
$$\sum_{p \le N} \frac{\log p}{p}\log\lfloor N/p\rfloor \le \tfrac12 (\log N)^2 + O(1),$$
with **no** `log N` term.  That is what the marginal Gronwall induction needs: the two
`(log N)²` terms cancel identically, so any surviving multiple of `log N` would destroy it.

Abel summation turns the left side into `∑_{k < N} A(k)(\log(k+1) - \log k)` with
`A(k) = ∑_{p ≤ k} \log p/p`, where the term `A(N)\log N` cancels; `A(k) ≤ \log k` then
reduces it to `∑_k \log k / k ≤ (\log N)^2/2 + O(1)`.
-/
@[category API, AMS 11]
theorem sum_primeWeight_mul_log_div_le (N : ℕ) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * Real.log ((N / p : ℕ) : ℝ))
      ≤ Real.log N ^ 2 / 2 + 2 * 10 ^ 11 := by
  classical
  set c := Real.log 4 + 8 with hc
  have hcle : c ≤ (9.4 : ℝ) := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    rw [hc, h]
    linarith
  have hcnn : (0 : ℝ) ≤ c := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hc]; linarith
  -- pass to the `primeWeight` form and drop the floor
  have hstep1 : (∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * Real.log ((N / p : ℕ) : ℝ))
      ≤ ∑ k ∈ Icc 1 N, primeWeight k * (Real.log N - Real.log k) := by
    rw [← sum_primeWeight_mul (fun k ↦ Real.log ((N / k : ℕ) : ℝ)) N]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hkN : k ≤ N := (mem_Icc.1 hk).2
    have hwnn : 0 ≤ primeWeight k := by
      simp only [primeWeight]
      split_ifs with hp
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
        exact div_nonneg (Real.log_nonneg this) (by linarith)
      · exact le_rfl
    refine mul_le_mul_of_nonneg_left ?_ hwnn
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hk1 hkN
    have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
    have hdpos : 1 ≤ N / k := (Nat.one_le_div_iff (by omega)).2 hkN
    have hdposR : (0 : ℝ) < ((N / k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((N / k : ℕ) : ℝ) := by exact_mod_cast hdpos
      linarith
    have := Real.log_le_log hdposR hdiv
    rwa [Real.log_div (ne_of_gt hNpos) (ne_of_gt hkR)] at this
  -- Abel: the `A(N) log N` terms cancel
  have habel := sum_Icc_by_parts primeWeight (fun k ↦ Real.log k) N
  have hstep2 : (∑ k ∈ Icc 1 N, primeWeight k * (Real.log N - Real.log k))
      = ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, primeWeight j)
          * (Real.log ((k : ℕ) + 1 : ℕ) - Real.log k) := by
    have hsplit : (∑ k ∈ Icc 1 N, primeWeight k * (Real.log N - Real.log k))
        = (∑ k ∈ Icc 1 N, primeWeight k) * Real.log N
          - ∑ k ∈ Icc 1 N, primeWeight k * Real.log k := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hsplit, habel]
    push_cast
    ring
  -- bound each Abel term
  have hstep3 : (∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, primeWeight j)
        * (Real.log ((k : ℕ) + 1 : ℕ) - Real.log k))
      ≤ ∑ k ∈ Ico 1 N, (Real.log k / k + c * 10 ^ 10 / (k : ℝ) ^ 2) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hPbd := sum_primeWeight_le_log_add (k := k) hk1
    have hPnn : 0 ≤ ∑ j ∈ Icc 1 k, primeWeight j := by
      refine Finset.sum_nonneg fun j _ ↦ ?_
      simp only [primeWeight]
      split_ifs with hp
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hp.one_lt.le
        exact div_nonneg (Real.log_nonneg this) (by positivity)
      · exact le_rfl
    have hdelta_nn : 0 ≤ Real.log ((k : ℕ) + 1 : ℕ) - Real.log k := by
      have : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := log_natCast_mono (by omega)
      push_cast at this ⊢
      linarith
    have hdelta : Real.log ((k : ℕ) + 1 : ℕ) - Real.log k ≤ 1 / (k : ℝ) := by
      have h1 : Real.log (((k : ℝ) + 1) / k) ≤ ((k : ℝ) + 1) / k - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (((k : ℝ) + 1) / k) = Real.log ((k : ℝ) + 1) - Real.log k :=
        Real.log_div (by positivity) (by positivity)
      have h3 : ((k : ℝ) + 1) / k - 1 = 1 / (k : ℝ) := by
        field_simp
        ring
      rw [h2] at h1
      push_cast
      linarith [h1, h3.le, h3.ge]
    have hlognn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkR
    calc (∑ j ∈ Icc 1 k, primeWeight j) * (Real.log ((k : ℕ) + 1 : ℕ) - Real.log k)
        ≤ (Real.log k + c * (10 ^ 10 / (k : ℝ))) * (1 / (k : ℝ)) := by
          refine mul_le_mul hPbd hdelta hdelta_nn ?_
          have : (0 : ℝ) ≤ c * (10 ^ 10 / (k : ℝ)) := by positivity
          linarith
    _ = Real.log k / k + c * 10 ^ 10 / (k : ℝ) ^ 2 := by field_simp
  -- sum up
  have hsum1 : (∑ k ∈ Ico 1 N, Real.log k / k) ≤ Real.log N ^ 2 / 2 + 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_log_div_le_sq_log N)
    · exact Finset.Ico_subset_Icc_self
    · intro j hj _
      have hj1 : 1 ≤ j := (mem_Icc.1 hj).1
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hsum2 : (∑ k ∈ Ico 1 N, c * 10 ^ 10 / (k : ℝ) ^ 2) ≤ c * 10 ^ 10 * 2 := by
    have hrw : ∀ k : ℕ, c * 10 ^ 10 / (k : ℝ) ^ 2 = (c * 10 ^ 10) * (1 / (k : ℝ) ^ 2) :=
      fun k ↦ by ring
    rw [Finset.sum_congr rfl fun k _ ↦ hrw k, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_)
      (sum_one_div_sq_le N)
    intro j _ _
    positivity
  rw [Finset.sum_add_distrib] at hstep3
  have hfinal : c * 10 ^ 10 * 2 + 2 ≤ 2 * 10 ^ 11 := by nlinarith [hcle, hcnn]
  linarith [hstep1, hstep2.le, hstep2.ge, hstep3, hsum1, hsum2]

open scoped Classical in
/-- The bad-prime profile
$$\sum_{p \le N,\ f(p) = -1} \frac{\log p}{p}\bigl(1 + \log\lfloor N/p\rfloor\bigr),$$
the mass that the defect weight `1 + f(p)` of the engine identity removes. -/
noncomputable def badProfile (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter (fun p ↦ p.Prime ∧ f p = -1),
    Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ))

open scoped Classical in
@[category API, AMS 11]
theorem sum_one_sub_eq_two_mul_badProfile (hf : IsPMOneMultiplicative f) (N : ℕ) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 - f p) * (1 + Real.log ((N / p : ℕ) : ℝ))))
      = 2 * badProfile f N := by
  have hstep : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 - f p) * (1 + Real.log ((N / p : ℕ) : ℝ)))
        = if f p = -1 then 2 * (Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ))) else 0 := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    rcases hf.pmOne p hp1 with h | h
    · rw [h, if_neg (by norm_num)]
      ring
    · rw [h, if_pos rfl]
      ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, badProfile, Finset.filter_filter,
    Finset.mul_sum]

open scoped Classical in
/--
**The Gronwall step.**  If `|L(M)| ≤ α(1 + log M)` for every `M ≤ N`, then

    |L(N)| log N ≤ α (log N)² - 2α · badProfile f N + O((1 + α)(1 + log N)).

The `α (log N)²` term is exactly the trivial bound: the whole gain is the bad-prime profile
`badProfile f N`, which the hypothesis `∑_{f(p) = -1} 1/p = ∞` forces to grow.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_of_profile (hf : IsPMOneMultiplicative f) {N : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hbd : ∀ M ≤ N, |logMean f M| ≤ α * (1 + Real.log M)) :
    |logMean f N| * Real.log N
      ≤ α * Real.log N ^ 2 - 2 * α * badProfile f N
        + (2 * α * (11 + Real.log 4) + (27 + 2 * Real.log 4)) * (1 + Real.log N) := by
  classical
  have hmain := abs_logMean_mul_log_le_of_forall_le f hf (fun M ↦ α * (1 + Real.log M)) hbd
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 + f p) * (α * (1 + Real.log ((N / p : ℕ) : ℝ))))
        = 2 * α * (Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ)))
          - α * (Real.log p / p * ((1 - f p) * (1 + Real.log ((N / p : ℕ) : ℝ)))) :=
    fun p _ ↦ by ring
  have hsplit : (∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 + f p) * (α * (1 + Real.log ((N / p : ℕ) : ℝ)))))
      = 2 * α * (∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ)))
        - α * (∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * ((1 - f p) * (1 + Real.log ((N / p : ℕ) : ℝ)))) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit, sum_one_sub_eq_two_mul_badProfile f hf N] at hmain
  have hprof := sum_primeWeight_mul_profile_le N
  have hlogN : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg N
    linarith
  nlinarith [hmain, hprof, hα, hlogN]

/-- `log(N/p) ≤ 1 + log ⌊N/p⌋`: the floor costs at most `log 2 ≤ 1`. -/
@[category API, AMS 11]
theorem sub_log_le_one_add_log_div {N p : ℕ} (hp : 1 ≤ p) (hpN : p ≤ N) :
    Real.log N - Real.log p ≤ 1 + Real.log ((N / p : ℕ) : ℝ) := by
  have hq1 : 1 ≤ N / p := (Nat.one_le_div_iff (by omega)).2 hpN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans hp hpN
    exact_mod_cast this
  have hqR : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hq1
  have hlt : N < p * (2 * (N / p)) := by
    have h : N < (N / p + 1) * p :=
      (Nat.div_lt_iff_lt_mul (show 0 < p by omega)).1 (Nat.lt_succ_self _)
    calc N < (N / p + 1) * p := h
    _ ≤ (2 * (N / p)) * p := by
          have : N / p + 1 ≤ 2 * (N / p) := by omega
          exact Nat.mul_le_mul_right p this
    _ = p * (2 * (N / p)) := by ring
  have hltR : (N : ℝ) < (p : ℝ) * (2 * ((N / p : ℕ) : ℝ)) := by
    have : ((N : ℕ) : ℝ) < ((p * (2 * (N / p)) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this
    linarith
  have hlog := Real.log_lt_log hNpos hltR
  rw [Real.log_mul (ne_of_gt hpR) (by positivity), Real.log_mul (by norm_num) (by linarith)] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  linarith

open scoped Classical in
/-- `r(K) = ∑_{p ≤ K, f p = -1} log p / p`, the log-weighted bad prime sum. -/
noncomputable def badLogSum (f : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ p ∈ badPrimesLE f K, Real.log p / p

open scoped Classical in
/-- `r(K) ≥ log 2 · E(K)`, so the log-weighted bad prime sum also diverges. -/
@[category API, AMS 11]
theorem log_two_mul_badPrimeSum_le_badLogSum (K : ℕ) :
    Real.log 2 * badPrimeSum f K ≤ badLogSum f K := by
  rw [badLogSum, badPrimeSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hpp : p.Prime := by
    rw [badPrimesLE, Finset.mem_filter] at hp
    exact hp.2.1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hpR : (0 : ℝ) < p := by linarith
  rw [mul_one_div, div_le_div_iff₀ hpR hpR]
  exact mul_le_mul_of_nonneg_right (Real.log_le_log (by norm_num) hp2) hpR.le

open scoped Classical in
/--
The lower bound for the bad-prime profile: only the bad primes `p ≤ K` are kept, and each
contributes at least `log N - log K`.
-/
@[category API, AMS 11]
theorem mul_badLogSum_le_badProfile {K N : ℕ} (hKN : K ≤ N) : (Real.log N - Real.log K) * badLogSum f K ≤ badProfile f N := by
  have hsub : badPrimesLE f K ⊆ (Icc 1 N).filter (fun p ↦ p.Prime ∧ f p = -1) := by
    intro p hp
    rw [badPrimesLE, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_filter, mem_Icc]
    exact ⟨⟨hp.2.1.one_lt.le.trans' (by norm_num), by omega⟩, hp.2⟩
  have hnn : ∀ p ∈ (Icc 1 N).filter (fun p ↦ p.Prime ∧ f p = -1),
      p ∉ badPrimesLE f K → 0 ≤ Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ)) := by
    intro p hp _
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
    have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have h1 : 0 ≤ Real.log p / p := div_nonneg (Real.log_nonneg hp2) (by linarith)
    have h2 : 0 ≤ 1 + Real.log ((N / p : ℕ) : ℝ) := by
      have := Real.log_natCast_nonneg (N / p)
      linarith
    exact mul_nonneg h1 h2
  rw [badProfile]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
  rw [badLogSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  rw [badPrimesLE, Finset.mem_filter, Finset.mem_range] at hp
  have hpp : p.Prime := hp.2.1
  have hp1 : 1 ≤ p := hpp.one_lt.le.trans' (by norm_num)
  have hpK : p ≤ K := by omega
  have hpN : p ≤ N := le_trans hpK hKN
  have hwnn : 0 ≤ Real.log p / p := by
    have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    exact div_nonneg (Real.log_nonneg hp2) (by linarith)
  have hlogpK : Real.log p ≤ Real.log K := log_natCast_mono hpK
  have hstep : Real.log N - Real.log K ≤ 1 + Real.log ((N / p : ℕ) : ℝ) := by
    have := sub_log_le_one_add_log_div (N := N) (p := p) hp1 hpN
    linarith
  calc (Real.log N - Real.log K) * (Real.log p / p)
      = Real.log p / p * (Real.log N - Real.log K) := by ring
  _ ≤ Real.log p / p * (1 + Real.log ((N / p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hwnn

open scoped Classical in
@[category API, AMS 11]
theorem badLogSum_nonneg (K : ℕ) : 0 ≤ badLogSum f K := by
  refine Finset.sum_nonneg fun p hp ↦ ?_
  have hpp : p.Prime := by
    rw [badPrimesLE, Finset.mem_filter] at hp
    exact hp.2.1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  exact div_nonneg (Real.log_nonneg hp1) (by linarith)

open scoped Classical in
/--
**One scale of the iteration.**  Assume `|L(M)| ≤ α(1 + log M)` for all `M ≤ N`, and let
`K ≤ √N` (in the form `2 log K ≤ log N`).  Then

    |L(N)| ≤ α log N - α r(K) + 2 C(α),   r(K) = ∑_{p ≤ K, f p = -1} log p / p.

The deficit `α r(K)` can be made as large as one likes by choosing `K`, because the
hypothesis `∑_{f(p) = -1} 1/p = ∞` makes `r` unbounded
(`Wirsing.log_two_mul_badPrimeSum_le_badLogSum`).  It is a deficit against `α log N`, not
against `α`, so a single scale does not improve `α`; the iteration that turns these deficits
into `L(N) = o(log N)` is what remains of
`Wirsing.tendsto_logMean_div_log_atTop_zero`.
-/
@[category API, AMS 11]
theorem abs_logMean_le_of_profile (hf : IsPMOneMultiplicative f) {N K : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hKN : K ≤ N) (hlogK : 2 * Real.log K ≤ Real.log N)
    (hlogN : 1 ≤ Real.log N)
    (hbd : ∀ M ≤ N, |logMean f M| ≤ α * (1 + Real.log M)) :
    |logMean f N| ≤ α * Real.log N - α * badLogSum f K
      + 2 * (2 * α * (11 + Real.log 4) + (27 + 2 * Real.log 4)) := by
  classical
  have hstep := abs_logMean_mul_log_le_of_profile f hf hα hbd
  have hprof := mul_badLogSum_le_badProfile f (K := K) (N := N) hKN
  have hrnn := badLogSum_nonneg f K
  have hlogNpos : (0 : ℝ) < Real.log N := by linarith
  have hhalf : Real.log N / 2 ≤ Real.log N - Real.log K := by linarith
  have hlow : Real.log N / 2 * badLogSum f K ≤ badProfile f N :=
    le_trans (mul_le_mul_of_nonneg_right hhalf hrnn) hprof
  have hC : 0 ≤ 2 * α * (11 + Real.log 4) + (27 + 2 * Real.log 4) := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hkey : |logMean f N| * Real.log N
      ≤ (α * Real.log N - α * badLogSum f K
          + 2 * (2 * α * (11 + Real.log 4) + (27 + 2 * Real.log 4))) * Real.log N := by
    nlinarith [hstep, hlow, hα, hrnn, hlogNpos, hC]
  exact le_of_mul_le_mul_right (by linarith [hkey]) hlogNpos

open scoped Classical in
/--
**The recursive profile.**  `logProfile f N` is defined by strong recursion so that it
satisfies the induction step of route C with equality:
`ψ(N) log N = ∑_{p ≤ N} (log p/p)(1 + f p) ψ(⌊N/p⌋) + (27 + 2 log 4)(1 + log N)`.

By `Wirsing.abs_logMean_le_logProfile` it dominates `|L(N)|`, so
`Wirsing.tendsto_logMean_div_log_atTop_zero` reduces to the purely analytic statement
`ψ(N) = o(log N)`.
-/
noncomputable def logProfile (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  if hN : N ≤ 1 then 1
  else ((∑ p ∈ ((Icc 1 N).filter Nat.Prime).attach,
        Real.log (p : ℕ) / ((p : ℕ) : ℝ) * ((1 + f (p : ℕ)) * logProfile f (N / (p : ℕ))))
      + (27 + 2 * Real.log 4) * (1 + Real.log N)) / Real.log N
  decreasing_by
    have hpp : ((p : ℕ)).Prime := (Finset.mem_filter.1 p.2).2
    exact Nat.div_lt_self (by omega) hpp.one_lt

open scoped Classical in
@[category API, AMS 11]
theorem logProfile_of_one_lt {N : ℕ} (hN : 1 < N) :
    logProfile f N = ((∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 + f p) * logProfile f (N / p)))
      + (27 + 2 * Real.log 4) * (1 + Real.log N)) / Real.log N := by
  rw [logProfile, dif_neg (by omega)]
  congr 2
  exact Finset.sum_attach ((Icc 1 N).filter Nat.Prime)
    (fun p ↦ Real.log p / p * ((1 + f p) * logProfile f (N / p)))

open scoped Classical in
/-- The recursive profile dominates the logarithmic average. -/
@[category API, AMS 11]
theorem abs_logMean_le_logProfile (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |logMean f N| ≤ logProfile f N := by
  classical
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · rw [logProfile, dif_pos (by omega)]
      interval_cases N
      · simp [logMean]
      · simp [logMean, hf.map_one]
    · have hN1 : 1 < N := by omega
      have hlogpos : 0 < Real.log (N : ℝ) := by
        have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have := Real.log_le_log (show (0:ℝ) < 2 by norm_num) h2
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        linarith
      have hstep := abs_logMean_mul_log_le_of_forall_lt f hf (by omega : 1 ≤ N)
        (logProfile f) (fun M hM ↦ ih M hM)
      rw [logProfile_of_one_lt f hN1, le_div_iff₀ hlogpos]
      exact hstep

open scoped Classical in
/-- The bad-prime deficit for the profile `α log M + β`. -/
noncomputable def badDefect (f : ℕ → ℝ) (α β : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter (fun p ↦ p.Prime ∧ f p = -1),
    Real.log p / p * (α * Real.log ((N / p : ℕ) : ℝ) + β)

open scoped Classical in
@[category API, AMS 11]
theorem sum_one_sub_eq_two_mul_badDefect (hf : IsPMOneMultiplicative f) (α β : ℝ) (N : ℕ) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 - f p) * (α * Real.log ((N / p : ℕ) : ℝ) + β)))
      = 2 * badDefect f α β N := by
  have hstep : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 - f p) * (α * Real.log ((N / p : ℕ) : ℝ) + β))
        = if f p = -1 then
            2 * (Real.log p / p * (α * Real.log ((N / p : ℕ) : ℝ) + β)) else 0 := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    rcases hf.pmOne p hp1 with h | h
    · rw [h, if_neg (by norm_num)]; ring
    · rw [h, if_pos rfl]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, badDefect, Finset.filter_filter,
    Finset.mul_sum]

open scoped Classical in
/--
**The sharp Gronwall step.**  If `|L(M)| ≤ α log M + β` for every `M ≤ N` then

    |L(N)| log N ≤ α (log N)² + 2β log N - 2 · badDefect f α β N + O(1 + α + β).

Compared with `Wirsing.abs_logMean_mul_log_le_of_profile` the `(log N)²` coefficient is now
**exact**: `sum_primeWeight_mul_log_div_le` contributes no `log N` term, so the only
`log N` terms left are `2β log N` (from the constant part of the profile) and the `O(log N)`
error of the engine identity.  The deficit is the entire gain.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_of_profile_sharp (hf : IsPMOneMultiplicative f) {N : ℕ}
    (hN : 1 ≤ N) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hbd : ∀ M ≤ N, |logMean f M| ≤ α * Real.log M + β) :
    |logMean f N| * Real.log N
      ≤ α * Real.log N ^ 2 + 2 * β * Real.log N - 2 * badDefect f α β N
        + (2 * α * (2 * 10 ^ 11) + 2 * β * (Real.log 4 + 8)
            + (27 + 2 * Real.log 4) * (1 + Real.log N)) := by
  classical
  have hmain := abs_logMean_mul_log_le_of_forall_le f hf
    (fun M ↦ α * Real.log M + β) hbd
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 + f p) * (α * Real.log ((N / p : ℕ) : ℝ) + β))
        = 2 * (Real.log p / p * (α * Real.log ((N / p : ℕ) : ℝ) + β))
          - Real.log p / p * ((1 - f p) * (α * Real.log ((N / p : ℕ) : ℝ) + β)) :=
    fun p _ ↦ by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_one_sub_eq_two_mul_badDefect f hf α β N] at hmain
  -- the two pieces of the good-prime sum
  have hsplit : (∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * (α * Real.log ((N / p : ℕ) : ℝ) + β))
      = α * (∑ p ∈ (Icc 1 N).filter Nat.Prime,
            Real.log p / p * Real.log ((N / p : ℕ) : ℝ))
        + β * ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  have h1 := sum_primeWeight_mul_log_div_le (N := N)
  have h2 := (abs_le.1 (Mertens.abs_sum_log_prime_div_sub_log_le hN)).2
  rw [hsplit] at hmain
  nlinarith [hmain, h1, h2, hα, hβ]

open scoped Classical in
/--
**The sharp weight comparison for an arbitrary profile.**  If `g` is nonincreasing,
nonnegative, and `log`-Lipschitz with constant `α`, then the prime weights `log p / p` are
dominated by the `log`-increments `log k - log (k-1)`, with an error of size `O(α + g N)`
and **no `log N` term**.

This is the general form of `Wirsing.sum_primeWeight_mul_log_div_le`, and it is what lets the
Gronwall iteration be run with a decaying profile rather than only a linear one.  The proof
is Abel summation plus `A(k) ≤ log k` (`Wirsing.sum_primeWeight_le_log_add`); the Lipschitz
hypothesis is what keeps the crude regime `k < 10 ^ 10` contributing only `O(α)`.
-/
@[category API, AMS 11]
theorem sum_primeWeight_mul_le_of_antitone (g : ℕ → ℝ) (α : ℝ) (hα : 0 ≤ α) (N : ℕ)
    (hgnn : ∀ k, 0 ≤ g k)
    (hganti : ∀ k, g (k + 1) ≤ g k)
    (hglip : ∀ k, 1 ≤ k → g k - g (k + 1) ≤ α * (Real.log (k + 1) - Real.log k)) :
    ∑ k ∈ Icc 1 N, primeWeight k * g k
      ≤ (Real.log N * g N + ∑ k ∈ Ico 1 N, Real.log k * (g k - g (k + 1)))
        + (Real.log 4 + 8) * 10 ^ 10 * (g N + 2 * α) := by
  classical
  set c := Real.log 4 + 8 with hc
  have hcnn : (0 : ℝ) ≤ c := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hc]; linarith
  have habel := sum_Icc_by_parts primeWeight g N
  have hrw : ∑ k ∈ Icc 1 N, primeWeight k * g k
      = (∑ k ∈ Icc 1 N, primeWeight k) * g N
        + ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, primeWeight j) * (g k - g (k + 1)) := by
    rw [habel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hrw]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (0 : ℝ) ≤ c * 10 ^ 10 * (g 0 + 2 * α) := by
      have := hgnn 0
      positivity
    simp only [Nat.cast_zero, Real.log_zero, zero_mul, zero_add,
      show Icc 1 0 = (∅ : Finset ℕ) from rfl, show Ico 1 0 = (∅ : Finset ℕ) from rfl,
      Finset.sum_empty]
    linarith [h0]
  -- the boundary term
  have hbd : (∑ k ∈ Icc 1 N, primeWeight k) * g N
      ≤ Real.log N * g N + c * 10 ^ 10 * g N := by
    have h := sum_primeWeight_le_log_add (k := N) hN
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hratio : (10 : ℝ) ^ 10 / (N : ℝ) ≤ 10 ^ 10 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hNR]
    have hg := hgnn N
    have h1 : (∑ k ∈ Icc 1 N, primeWeight k) * g N
        ≤ (Real.log N + c * (10 ^ 10 / (N : ℝ))) * g N := mul_le_mul_of_nonneg_right h hg
    have h2 : (Real.log N + c * (10 ^ 10 / (N : ℝ))) * g N
        ≤ (Real.log N + c * 10 ^ 10) * g N := by
      refine mul_le_mul_of_nonneg_right ?_ hg
      nlinarith [hratio, hcnn]
    calc (∑ k ∈ Icc 1 N, primeWeight k) * g N ≤ (Real.log N + c * 10 ^ 10) * g N := by
          linarith
    _ = Real.log N * g N + c * 10 ^ 10 * g N := by ring
  -- the Abel terms
  have hterms : ∑ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, primeWeight j) * (g k - g (k + 1))
      ≤ (∑ k ∈ Ico 1 N, Real.log k * (g k - g (k + 1))) + c * 10 ^ 10 * (2 * α) := by
    have hpoint : ∀ k ∈ Ico 1 N, (∑ j ∈ Icc 1 k, primeWeight j) * (g k - g (k + 1))
        ≤ Real.log k * (g k - g (k + 1)) + c * 10 ^ 10 * (α / (k : ℝ) ^ 2) := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hdnn : 0 ≤ g k - g (k + 1) := by linarith [hganti k]
      have hPbd := sum_primeWeight_le_log_add (k := k) hk1
      have hlip := hglip k hk1
      have hdlt : Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / (k : ℝ) := by
        have h1 : Real.log (((k : ℝ) + 1) / k) ≤ ((k : ℝ) + 1) / k - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have h2 : Real.log (((k : ℝ) + 1) / k) = Real.log ((k : ℝ) + 1) - Real.log k :=
          Real.log_div (by positivity) (by positivity)
        have h3 : ((k : ℝ) + 1) / k - 1 = 1 / (k : ℝ) := by
          field_simp
          ring
        rw [h2] at h1
        linarith [h1, h3.le, h3.ge]
      have hlip' : g k - g (k + 1) ≤ α * (1 / (k : ℝ)) := by
        nlinarith [hlip, hdlt, hα]
      have hmul : (∑ j ∈ Icc 1 k, primeWeight j) * (g k - g (k + 1))
          ≤ (Real.log k + c * (10 ^ 10 / (k : ℝ))) * (g k - g (k + 1)) :=
        mul_le_mul_of_nonneg_right hPbd hdnn
      have hsecond : c * (10 ^ 10 / (k : ℝ)) * (g k - g (k + 1))
          ≤ c * 10 ^ 10 * (α / (k : ℝ) ^ 2) := by
        have hx : (0 : ℝ) ≤ c * (10 ^ 10 / (k : ℝ)) := by positivity
        have := mul_le_mul_of_nonneg_left hlip' hx
        calc c * (10 ^ 10 / (k : ℝ)) * (g k - g (k + 1))
            ≤ c * (10 ^ 10 / (k : ℝ)) * (α * (1 / (k : ℝ))) := this
        _ = c * 10 ^ 10 * (α / (k : ℝ) ^ 2) := by field_simp
      nlinarith [hmul, hsecond]
    refine le_trans (Finset.sum_le_sum hpoint) ?_
    rw [Finset.sum_add_distrib]
    have hrest : ∑ k ∈ Ico 1 N, c * 10 ^ 10 * (α / (k : ℝ) ^ 2) ≤ c * 10 ^ 10 * (2 * α) := by
      have hrw2 : ∀ k : ℕ, c * 10 ^ 10 * (α / (k : ℝ) ^ 2)
          = (c * 10 ^ 10 * α) * (1 / (k : ℝ) ^ 2) := fun k ↦ by ring
      rw [Finset.sum_congr rfl fun k _ ↦ hrw2 k, ← Finset.mul_sum]
      have hsum : ∑ k ∈ Ico 1 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
          (fun j _ _ ↦ by positivity)) (sum_one_div_sq_le N)
      have hfac : (0 : ℝ) ≤ c * 10 ^ 10 * α := by positivity
      nlinarith [hsum, hfac]
    linarith
  linarith [hbd, hterms]

end Wirsing
