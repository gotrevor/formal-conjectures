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

/-- The sharp Stirling-type upper bound $\sum_{n \le x} \log n \le x\log x - x + \log x + 1$. -/
theorem sum_log_le_sharp {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hfx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hf1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hsplit : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = (∑ n ∈ Ico 1 ⌊x⌋₊, log n) + log (⌊x⌋₊ : ℝ) := by
    have hset : Ioc 0 ⌊x⌋₊ = insert ⌊x⌋₊ (Ico 1 ⌊x⌋₊) := by
      ext n
      simp only [mem_Ioc, mem_insert, mem_Ico]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  have hint : ∑ n ∈ Ico 1 ⌊x⌋₊, log (n : ℝ)
      ≤ ∫ t in (1 : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), log t := by
    convert MonotoneOn.sum_le_integral_Ico hfloor ?_
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ by
        simp only [Set.mem_Icc, Nat.cast_one] at hy; simp only [Set.mem_Ioi]; linarith [hy.1])
  rw [integral_log] at hint
  simp only [log_one, mul_zero] at hint
  have hmono : ((⌊x⌋₊ : ℕ) : ℝ) * log (⌊x⌋₊ : ℝ) - ((⌊x⌋₊ : ℕ) : ℝ) ≤ x * log x - x := by
    have hnn : 0 ≤ ∫ t in ((⌊x⌋₊ : ℕ) : ℝ)..x, log t :=
      intervalIntegral.integral_nonneg hfx fun t ht ↦ log_nonneg (by linarith [ht.1])
    rw [integral_log] at hnn
    linarith
  have hlogle : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log (by linarith) hfx
  rw [hsplit]
  linarith

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

/-- The sharp Stirling-type lower bound $\sum_{n \le x} \log n \ge x\log x - x + 1 - \log x$. -/
theorem sum_log_ge_sharp {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x + 1 - log x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  calc
  x * log x - x + 1 - log x = (∫ t in (1 : ℝ)..x, log t) - log x := by
    rw [integral_log]
    simp only [log_one, mul_zero]
    ring
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

/-- The telescoping step behind `sum_log_div_sq_le`: with $a(x) = (\log x + 2)/x$ one has
$\log(x+1)/(x+1)^2 \le a(x) - a(x+1)$. -/
private lemma log_div_sq_le_telescope {x : ℝ} (hx : 1 ≤ x) :
    log (x + 1) / (x + 1) ^ 2 ≤ (log x + 2) / x - (log (x + 1) + 2) / (x + 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hL : 0 ≤ log x := log_nonneg hx
  have hLM : log x ≤ log (x + 1) := log_le_log hx0 (by linarith)
  have hstep : log (x + 1) - log x ≤ 1 / x := by
    have h := log_le_sub_one_of_pos (show (0 : ℝ) < (x + 1) / x by positivity)
    rw [log_div (by linarith) (by linarith)] at h
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rw [he] at h
    exact h
  rw [div_sub_div _ _ (ne_of_gt hx0) (ne_of_gt hx1), div_le_div_iff₀ (by positivity) (by positivity)]
  have hx2 : x * (log (x + 1) - log x) ≤ 1 := by
    rw [mul_comm]
    calc (log (x + 1) - log x) * x ≤ (1 / x) * x := by nlinarith
    _ = 1 := by field_simp
  nlinarith [sq_nonneg (x + 1), mul_nonneg hL hx0.le, mul_nonneg hL (sq_nonneg (x + 1))]

/-- $\sum_{2 \le n \le N} \log n / n^2 \le 2$. -/
theorem sum_log_div_sq_le (N : ℕ) : ∑ n ∈ Icc 2 N, log n / (n : ℝ) ^ 2 ≤ 2 := by
  set A : ℕ → ℝ := fun i ↦ (log (i + 1) + 2) / (i + 1) with hA
  have hAnn : ∀ i : ℕ, 0 ≤ A i := by
    intro i
    have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hlog : 0 ≤ log ((i : ℝ) + 1) := log_nonneg (by linarith)
    positivity
  have key : ∀ i : ℕ, log ((i : ℝ) + 2) / ((i : ℝ) + 2) ^ 2 ≤ A i - A (i + 1) := by
    intro i
    have h := log_div_sq_le_telescope (x := (i : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) i])
    simp only [hA]
    push_cast
    convert h using 3 <;> ring
  rw [(by rfl : Icc 2 N = Ico 2 (N + 1)), Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (N + 1 - 2), log ((2 + i : ℕ) : ℝ) / (((2 + i : ℕ) : ℕ) : ℝ) ^ 2
      ≤ ∑ i ∈ range (N + 1 - 2), (A i - A (i + 1)) := by
        refine sum_le_sum fun i _ ↦ ?_
        have h := key i
        have hc : ((2 + i : ℕ) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
        rw [hc]
        exact h
  _ = A 0 - A (N + 1 - 2) := Finset.sum_range_sub' A _
  _ ≤ 2 := by
        have h0 : A 0 = 2 := by simp [hA]
        linarith [hAnn (N + 1 - 2), h0]

private lemma geom_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Icc 2 N, x ^ k ≤ 2 * x ^ 2 := by
  have hx1 : x ≠ 1 := by intro h; rw [h] at hx; norm_num at hx
  have hgeom : ∑ i ∈ range (N + 1 - 2), x ^ i ≤ 2 := by
    rw [geom_sum_eq hx1]
    have hp : (0 : ℝ) ≤ x ^ (N + 1 - 2) := pow_nonneg hx0 _
    rw [div_le_iff_of_neg (by linarith : x - 1 < 0)]
    linarith
  calc ∑ k ∈ Icc 2 N, x ^ k = ∑ i ∈ range (N + 1 - 2), x ^ (2 + i) := by
        rw [(by rfl : Icc 2 N = Ico 2 (N + 1)), Finset.sum_Ico_eq_sum_range]
  _ = x ^ 2 * ∑ i ∈ range (N + 1 - 2), x ^ i := by
        rw [Finset.mul_sum]; exact sum_congr rfl fun i _ ↦ by rw [pow_add]
  _ ≤ x ^ 2 * 2 := by have := sq_nonneg x; nlinarith
  _ = 2 * x ^ 2 := by ring

/-- The contribution of the proper prime powers to $\sum_{d \le N} \Lambda(d)/d$ is bounded:
$\sum_{p^k \le N,\ k \ge 2} \log p / p^k \le 4$. -/
theorem sum_vonMangoldt_div_nonprime_le (N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime), Λ d / d ≤ 4 := by
  classical
  set T := (Icc 1 N).filter (fun d ↦ ¬ d.Prime) with hT
  set T₀ := T.filter (fun d ↦ Λ d ≠ 0) with hT₀
  set P := (range (N + 1)).filter Nat.Prime with hP
  set F : ℕ × ℕ → ℝ := fun x ↦ Real.log x.1 / (x.1 : ℝ) ^ x.2 with hF
  have hFnn : ∀ x ∈ P ×ˢ Icc 2 N, 0 ≤ F x := by
    rintro ⟨p, k⟩ hx
    simp only [hP, mem_product, mem_filter, mem_range] at hx
    have hp := hx.1.2
    exact div_nonneg (log_natCast_nonneg _) (by positivity)
  -- structure of the elements of `T₀`
  have hstruct : ∀ d ∈ T₀, ∃ p k, p.Prime ∧ 2 ≤ k ∧ p ^ k = d ∧ p ≤ N ∧ k ≤ N := by
    intro d hd
    simp only [hT₀, hT, mem_filter, mem_Icc] at hd
    obtain ⟨⟨⟨hd1, hdN⟩, hdnp⟩, hΛ⟩ := hd
    obtain ⟨p, k, hp, hk, rfl⟩ := (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    have hp' : p.Prime := hp.nat_prime
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have hk1 : k = 1 := by omega
        subst hk1
        exact absurd (by simpa using hp') hdnp
      · exact h
    have hple : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hklt : k ≤ p ^ k := Nat.le_of_lt (Nat.lt_pow_self hp'.one_lt)
    exact ⟨p, k, hp', hk2, rfl, le_trans hple hdN, le_trans hklt hdN⟩
  -- the reindexing map
  set i : ℕ → ℕ × ℕ := fun d ↦ (d.minFac, d.factorization d.minFac) with hi
  have hival : ∀ d ∈ T₀, i d ∈ P ×ˢ Icc 2 N ∧ F (i d) = Λ d / d := by
    intro d hd
    obtain ⟨p, k, hp, hk2, rfl, hpN, hkN⟩ := hstruct d hd
    have hmf : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp (by omega)
    have hfac : (p ^ k).factorization p = k := by
      rw [Nat.Prime.factorization_pow hp]; simp
    constructor
    · simp only [hi, hmf, hfac, hP, mem_product, mem_filter, mem_range, mem_Icc]
      exact ⟨⟨Nat.lt_succ_of_le hpN, hp⟩, hk2, hkN⟩
    · simp only [hi, hmf, hfac, hF]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      push_cast
      ring
  have hinj : Set.InjOn i T₀ := by
    intro a ha b hb hab
    obtain ⟨p, k, hp, hk2, rfl, _, _⟩ := hstruct a ha
    obtain ⟨q, l, hq, hl2, rfl, _, _⟩ := hstruct b hb
    have hmfa : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp (by omega)
    have hmfb : (q ^ l).minFac = q := Nat.Prime.pow_minFac hq (by omega)
    have hfa : (p ^ k).factorization p = k := by rw [Nat.Prime.factorization_pow hp]; simp
    have hfb : (q ^ l).factorization q = l := by rw [Nat.Prime.factorization_pow hq]; simp
    simp only [hi, hmfa, hmfb, Prod.mk.injEq] at hab
    obtain ⟨rfl, h2⟩ := hab
    rw [hfa, hfb] at h2
    rw [h2]
  calc ∑ d ∈ T, Λ d / d = ∑ d ∈ T₀, Λ d / d := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro d hdT hd
        simp only [mem_filter, not_and, not_not] at hd
        rw [hd hdT, zero_div]
  _ = ∑ d ∈ T₀, F (i d) := sum_congr rfl fun d hd ↦ ((hival d hd).2).symm
  _ = ∑ x ∈ T₀.image i, F x := (Finset.sum_image (fun a ha b hb h ↦ hinj ha hb h)).symm
  _ ≤ ∑ x ∈ P ×ˢ Icc 2 N, F x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ ↦ hFnn x hx)
        intro x hx
        simp only [mem_image] at hx
        obtain ⟨d, hd, rfl⟩ := hx
        exact (hival d hd).1
  _ = ∑ p ∈ P, ∑ k ∈ Icc 2 N, Real.log p / (p : ℝ) ^ k := by rw [Finset.sum_product]
  _ ≤ ∑ p ∈ P, 2 * (Real.log p / (p : ℝ) ^ 2) := by
        refine sum_le_sum fun p hp ↦ ?_
        simp only [hP, mem_filter, mem_range] at hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
        have hlog : 0 ≤ Real.log p := log_natCast_nonneg _
        have hgt := geom_tail_le (x := 1 / (p : ℝ)) (by positivity)
          (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith) N
        calc ∑ k ∈ Icc 2 N, Real.log p / (p : ℝ) ^ k
            = Real.log p * ∑ k ∈ Icc 2 N, (1 / (p : ℝ)) ^ k := by
              rw [Finset.mul_sum]
              exact sum_congr rfl fun k _ ↦ by rw [div_pow, one_pow]; ring
        _ ≤ Real.log p * (2 * (1 / (p : ℝ)) ^ 2) := by exact mul_le_mul_of_nonneg_left hgt hlog
        _ = 2 * (Real.log p / (p : ℝ) ^ 2) := by rw [div_pow, one_pow]; ring
  _ ≤ 2 * ∑ n ∈ Icc 2 N, Real.log n / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ ↦ ?_)
        · intro p hp
          simp only [hP, mem_filter, mem_range] at hp
          simp only [mem_Icc]
          exact ⟨hp.2.two_le, by omega⟩
        · exact mul_nonneg (by norm_num) (div_nonneg (log_natCast_nonneg _) (by positivity))
  _ ≤ 4 := by linarith [sum_log_div_sq_le N]

/-- **Mertens' first theorem**, prime form:
$\sum_{p \le N} \log p / p = \log N + O(1)$, with an explicit constant. -/
theorem abs_sum_log_prime_div_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p) - Real.log N| ≤ log 4 + 8 := by
  classical
  have hfloor : Ioc 0 ⌊(N : ℝ)⌋₊ = Icc 1 N := by
    rw [Nat.floor_natCast]
    rfl
  have hmain := abs_sum_vonMangoldt_div_sub_log_le (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [hfloor] at hmain
  have hsplit : ∑ d ∈ Icc 1 N, Λ d / (d : ℝ)
      = (∑ d ∈ (Icc 1 N).filter Nat.Prime, Λ d / (d : ℝ))
        + ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime), Λ d / (d : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : ∑ d ∈ (Icc 1 N).filter Nat.Prime, Λ d / (d : ℝ)
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p := by
    refine sum_congr rfl fun d hd ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hd).2]
  have htail := sum_vonMangoldt_div_nonprime_le N
  have htail0 : 0 ≤ ∑ d ∈ (Icc 1 N).filter (fun d ↦ ¬ d.Prime), Λ d / (d : ℝ) :=
    Finset.sum_nonneg fun d _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rw [abs_le] at hmain ⊢
  rw [hprime] at hsplit
  constructor <;> [linarith [hmain.1, hmain.2]; linarith [hmain.1, hmain.2]]

end Mertens
