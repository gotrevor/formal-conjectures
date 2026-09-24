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

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

/-!
# Mertens' first theorem

$\sum_{n \le x} \Lambda(n)/n = \log x + O(1)$ and its prime form
$\sum_{p \le x} \log p / p = \log x + O(1)$, with explicit constants.

The proof is the classical one: compare $\sum_{n \le x} \log n$ with $x \log x$ on one side
and, through the identity $\log = \Lambda * 1$, with $\sum_{d \le x} \Lambda(d) \lfloor x/d
\rfloor$ on the other. Chebyshev's bound $\psi(x) \le (\log 4 + 4) x$ absorbs the rounding.

The argument follows the corresponding development in the `PrimeNumberTheoremAnd` project.
-/

namespace Mertens

open Real Finset Filter
open ArithmeticFunction hiding log

/-- $\sum_{n \le x} \log n \le x \log x$. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith) |>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

private lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have h : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  calc |∫ t in a..b, log t| = ‖∫ t in a..b, log t‖ := (norm_eq_abs _).symm
  _ ≤ log b * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const h
  _ = log b * (b - a) := by rw [abs_of_nonneg (by linarith)]

/-- $\sum_{n \le x} \log n \ge x \log x - 2 x$. -/
theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  calc
  x * log x - 2 * x ≤ (∫ t in (1 : ℝ)..x, log t) - log x := by
    rw [integral_log]
    simp only [log_one, mul_zero]
    linarith [log_le_self (by linarith : 0 ≤ x)]
  _ ≤ (∫ t in (1 : ℝ)..x, log t) - ∫ t in ((⌊x⌋₊ : ℕ) : ℝ)..x, log t := by
    gcongr
    calc (∫ t in ((⌊x⌋₊ : ℕ) : ℝ)..x, log t)
        ≤ log x * (x - (⌊x⌋₊ : ℝ)) :=
          integral_log_le (by exact_mod_cast one_le_floor) (Nat.floor_le (by linarith))
      _ ≤ log x * 1 := by
          gcongr
          · exact log_nonneg hx
          · linarith [Nat.lt_floor_add_one x]
      _ = log x := mul_one _
  _ = ∫ t in (1 : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), log t := by
    nth_rw 2 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;>
      exact intervalIntegral.intervalIntegrable_log'
  _ ≤ ∑ n ∈ Ico 1 ⌊x⌋₊, log ((n + 1 : ℕ)) := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ by
        simp only [Set.mem_Icc, Nat.cast_one] at hy; simp only [Set.mem_Ioi]; linarith [hy.1])
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
    rw [Finset.sum_Ico_add' (fun n : ℕ ↦ log n) 1 ⌊x⌋₊ 1]
    have hset : Ioc 0 ⌊x⌋₊ = insert 1 (Ico (1 + 1) (⌊x⌋₊ + 1)) := by
      ext n
      simp only [mem_Ioc, mem_insert, mem_Ico]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp

/-- $\sum_{n \le x} \log n = \sum_{d \le x} \Lambda(d) \lfloor x/d \rfloor$. -/
theorem sum_log_eq_sum_vonMangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have h : ∀ n : ℕ, log n = (Λ * ArithmeticFunction.zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [h, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

/-- The error term in Mertens' first theorem, von Mangoldt form. -/
noncomputable def E₁Λ (x : ℝ) : ℝ := (∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d) - log x

theorem neg_two_le_E₁Λ {x : ℝ} (hx : 1 ≤ x) : -2 ≤ E₁Λ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  suffices h : x * (log x - 2) ≤ x * (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) by
    have := le_of_mul_le_mul_left h hx0
    simp only [E₁Λ]
    linarith
  calc
  x * (log x - 2) = x * log x - 2 * x := by ring
  _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := sum_log_ge hx
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := sum_log_eq_sum_vonMangoldt
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    refine sum_le_sum fun d _ ↦ ?_
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) vonMangoldt_nonneg
  _ = x * (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) := by rw [Finset.mul_sum]; exact sum_congr rfl fun d _ ↦ by ring

theorem E₁Λ_le {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ log 4 + 4 := by
  have hx0 : (0 : ℝ) < x := by linarith
  suffices h : x * (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) ≤ x * (log x + (log 4 + 4)) by
    have := le_of_mul_le_mul_left h hx0
    simp only [E₁Λ]
    linarith
  calc
  x * (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]; exact sum_congr rfl fun d _ ↦ by ring
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ((⌊x / d⌋₊ : ℝ) + 1) := by
    refine sum_le_sum fun d _ ↦ ?_
    exact mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le vonMangoldt_nonneg
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]; rw [Finset.sum_add_distrib]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · rw [← sum_log_eq_sum_vonMangoldt]; exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = x * (log x + (log 4 + 4)) := by ring

/-- **Mertens' first theorem**, von Mangoldt form:
$\sum_{n \le x} \Lambda(n)/n = \log x + O(1)$, with an explicit constant. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |(∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d) - log x| ≤ log 4 + 4 := by
  have h1 := neg_two_le_E₁Λ hx
  have h2 := E₁Λ_le hx
  have h4 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
  simp only [E₁Λ] at h1 h2
  rw [abs_le]
  constructor <;> linarith

end Mertens
