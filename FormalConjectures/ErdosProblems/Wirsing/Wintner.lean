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
public import FormalConjectures.ErdosProblems.Wirsing.Mean

/-!
# Wintner's mean value theorem

The convergent case of Wirsing's theorem is elementary.  Write `g = f * μ` for the Dirichlet
convolution, so that `f = 1 * g`, that is `f(n) = ∑_{d ∣ n} g(d)`.  Then

$$S(N) = \sum_{n \le N} f(n) = \sum_{d \le N} g(d) \lfloor N/d \rfloor,$$

so `σ(N) = ∑_{d ≤ N} g(d)/d + O\big(\tfrac1N \sum_{d \le N} |g(d)|\big)`.  If
`∑_d |g(d)|/d < ∞` both error and main term converge, and the mean value is `∑_d g(d)/d`.

This file develops the identity and the error bound.  The two limits and the summability of
`∑_d |g(d)|/d` (an Euler product estimate, which is where `∑_{f(p) = -1} 1/p < ∞` enters) are
separate.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
-/

@[expose] public section

open Filter Finset ArithmeticFunction

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The Möbius transform `g = f * μ` of `f`, so that `f(n) = ∑_{d ∣ n} g(d)`. -/
noncomputable def wintnerCoeff (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * f x.2

/-- `f = 1 * g`: the defining property of the Möbius transform. -/
@[category API, AMS 11]
theorem sum_divisors_wintnerCoeff {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, wintnerCoeff f d = f n :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := wintnerCoeff f) (g := f)).2
    (fun _ _ ↦ by rw [wintnerCoeff]) n hn

/-- The divisor swap: `∑_{n ≤ N} ∑_{d ∣ n} h(d) = ∑_{d ≤ N} h(d) ⌊N/d⌋`. -/
@[category API, AMS 11]
theorem sum_sum_divisors_eq (N : ℕ) (h : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, h d)
      = ∑ d ∈ Icc 1 N, h d * ((N / d : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_comm' (s := Icc 1 N) (t := fun n ↦ n.divisors) (t' := Icc 1 N)
    (s' := fun d ↦ {n ∈ Icc 1 N | d ∣ n})
    (by
      intro n d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdn, hn0⟩
        have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by
          rintro rfl
          exact hn0 (Nat.eq_zero_of_zero_dvd hdn))
        exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, le_trans (Nat.le_of_dvd (by omega) hdn) hnN⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, hdN⟩
        exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_const, card_filter_dvd_Icc, nsmul_eq_mul]
  ring

/-- **Wintner's identity.**  `S(N) = ∑_{d ≤ N} g(d) ⌊N/d⌋`. -/
@[category API, AMS 11]
theorem partialSum_eq_sum_wintnerCoeff (N : ℕ) :
    partialSum f N = ∑ d ∈ Icc 1 N, wintnerCoeff f d * ((N / d : ℕ) : ℝ) := by
  rw [← sum_sum_divisors_eq N (wintnerCoeff f), partialSum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
  exact (sum_divisors_wintnerCoeff f (by omega : 0 < n)).symm

/--
**Wintner's error bound.**
`|σ(N) - ∑_{d ≤ N} g(d)/d| ≤ (1/N) ∑_{d ≤ N} |g(d)|`.
-/
@[category API, AMS 11]
theorem abs_mean_sub_sum_wintnerCoeff_div_le {N : ℕ} (hN : 1 ≤ N) :
    |mean f N - ∑ d ∈ Icc 1 N, wintnerCoeff f d / d|
      ≤ (1 / (N : ℝ)) * ∑ d ∈ Icc 1 N, |wintnerCoeff f d| := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hexp : mean f N - ∑ d ∈ Icc 1 N, wintnerCoeff f d / d
      = ∑ d ∈ Icc 1 N, wintnerCoeff f d * (((N / d : ℕ) : ℝ) / N - 1 / d) := by
    rw [mean_eq_partialSum_div, partialSum_eq_sum_wintnerCoeff, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  rw [hexp, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d hd ↦ ?_)
  have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hfl : |((N / d : ℕ) : ℝ) / N - 1 / d| ≤ 1 / (N : ℝ) := by
    have hkey : ((N / d : ℕ) : ℝ) / N - 1 / d
        = (((N / d : ℕ) : ℝ) - (N : ℝ) / d) / N := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hNpos]
    rw [div_le_div_iff₀ hNpos hNpos]
    nlinarith [abs_natDiv_sub_div_le_one (N := N) hd1, hNpos]
  rw [abs_mul]
  calc |wintnerCoeff f d| * |((N / d : ℕ) : ℝ) / N - 1 / d|
      ≤ |wintnerCoeff f d| * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hfl (abs_nonneg _)
    _ = 1 / (N : ℝ) * |wintnerCoeff f d| := by ring

end Wirsing
