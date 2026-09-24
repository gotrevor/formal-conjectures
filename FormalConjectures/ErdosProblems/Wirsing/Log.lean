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

/--
**The model case of route C.**  If `f(p) = -1` for every prime `p`, then
$L(N)\log N = O(\log N)$, so the logarithmic average $L(N) = \sum_{n \le N} f(n)/n$ stays
bounded.

This is the first genuine gain of the log-weighted route: the naive `limsup` argument
applied to `mean f` only ever gives `A ≤ A`, whereas here the two sides of the identity
cancel exactly and leave a factor `log N` of room.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le (hf : IsPMOneMultiplicative f)
    (hneg : ∀ p : ℕ, p.Prime → f p = -1) (N : ℕ) :
    |logMean f N * Real.log N| ≤ (27 + 2 * Real.log 4) * (1 + Real.log N) := by
  classical
  set P := ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * logMean f (N / p) with hP
  set B := ∑ k ∈ Icc 1 N, (1 : ℝ) / k * logMean f (N / k) with hB
  set S := ∑ n ∈ Icc 1 N, (f n / n) * Real.log n with hS
  set T := logMean f N * Real.log N with hT
  have hsign : (∑ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * (f p * logMean f (N / p))) = -P := by
    rw [hP, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [hneg p (mem_filter.1 hp).2]
    ring
  have e1 := abs_sum_div_mul_log_sub_sum_prime_le f hf N
  rw [hsign, ← hS] at e1
  have e2 := abs_sum_prime_sub_sum_one_div_logMean_le f hf N
  rw [← hP, ← hB] at e2
  have e3 := abs_sum_one_div_mul_logMean_sub_le f hf N
  rw [← hB, ← hS, ← hT] at e3
  have t1 := abs_sub ((S - -P) - (P - B)) (B - (T - S))
  have t2 := abs_sub (S - -P) (P - B)
  have hid : T = (S - -P) - (P - B) - (B - (T - S)) := by ring
  have habs : |T| ≤ |S - -P| + |P - B| + |B - (T - S)| := by
    have heq : |T| = |(S - -P) - (P - B) - (B - (T - S))| := by rw [← hid]
    rw [heq]
    linarith [t1, t2]
  have hlogN : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  calc |T| ≤ |S - -P| + |P - B| + |B - (T - S)| := habs
  _ ≤ 8 * (1 + Real.log N) + 2 * (Real.log 4 + 9) * (1 + Real.log N) + (1 + Real.log N) := by
        linarith [e1, e2, e3]
  _ = (27 + 2 * Real.log 4) * (1 + Real.log N) := by ring

end Wirsing
