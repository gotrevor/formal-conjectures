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

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

/-!
# The arithmetic identity behind Selberg's symmetry formula

$$\Lambda(n)\log n + (\Lambda * \Lambda)(n) = (\mu * \log^2)(n).$$

Summing this over `n ≤ x` and estimating the right-hand side is Selberg's symmetry formula
$\sum_{n \le x}\Lambda(n)\log n + \sum_{mn \le x}\Lambda(m)\Lambda(n) = 2x\log x + O(x)$,
the second-order relation that makes the Erdős–Selberg argument contractive.  This file
proves the identity itself; the summation is separate.

The proof is the standard one: pointwise multiplication by `log` is a derivation for
Dirichlet convolution, because `\log` is additive on the divisor pairs of `n`.  Applying it
to `\log = \zeta * \Lambda` gives `\log^2 = \zeta * (\Lambda*\Lambda + \Lambda\cdot\log)`,
and Möbius inversion finishes.
-/

namespace Selberg

open ArithmeticFunction

open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/--
**Pointwise multiplication by `log` is a derivation for Dirichlet convolution.**
`(f * g)·\log = (f·\log) * g + f * (g·\log)`.
-/
theorem pmul_log_mul (f g : ArithmeticFunction ℝ) :
    (f * g).pmul log = (f.pmul log) * g + f * (g.pmul log) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [pmul_apply, mul_apply, ArithmeticFunction.add_apply, mul_apply, mul_apply,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hx1 : x.1 ≠ 0 := (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne'
    have hx2 : x.2 ≠ 0 := (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne'
    have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.1 hx).1
    have hlog : Real.log n = Real.log x.1 + Real.log x.2 := by
      rw [← hprod]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
    simp only [pmul_apply, log_apply]
    rw [hlog]
    ring

/-- `log·log = ζ * (Λ * Λ + Λ·log)`. -/
theorem log_pmul_log :
    log.pmul log
      = (ζ : ArithmeticFunction ℝ) * (vonMangoldt * vonMangoldt + vonMangoldt.pmul log) := by
  have hz : (ζ : ArithmeticFunction ℝ).pmul log = log := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [pmul_apply, natCoe_apply, zeta_apply, if_neg (by omega), Nat.cast_one, one_mul]
  have hlog : (ζ : ArithmeticFunction ℝ) * vonMangoldt = log := zeta_mul_vonMangoldt
  calc log.pmul log = ((ζ : ArithmeticFunction ℝ) * vonMangoldt).pmul log := by rw [hlog]
    _ = ((ζ : ArithmeticFunction ℝ).pmul log) * vonMangoldt
          + (ζ : ArithmeticFunction ℝ) * (vonMangoldt.pmul log) := pmul_log_mul _ _
    _ = log * vonMangoldt + (ζ : ArithmeticFunction ℝ) * (vonMangoldt.pmul log) := by rw [hz]
    _ = (ζ : ArithmeticFunction ℝ) * (vonMangoldt * vonMangoldt + vonMangoldt.pmul log) := by
        rw [mul_add, ← hlog, mul_assoc]


open Finset in
/--
**Dirichlet convolution summed over an initial segment** (the hyperbola identity in its
one-sided form):
$$\sum_{n \le N} (f * g)(n) = \sum_{d \le N} f(d) \sum_{m \le N/d} g(m).$$
-/
theorem sum_Icc_mul_apply (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ d ∈ Icc 1 N, f d * ∑ m ∈ Icc 1 (N / d), g m := by
  classical
  have hstep : ∀ n ∈ Icc 1 N, (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := by
    intro n _
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun a b ↦ f a * g b)]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_comm' (s := Icc 1 N) (t := fun n ↦ n.divisors) (t' := Icc 1 N)
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
  have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
  have himg : {n ∈ Icc 1 N | d ∣ n} = (Icc 1 (N / d)).image (fun m ↦ d * m) := by
    ext n
    simp only [mem_filter, mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, m, rfl⟩
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · omega
        · omega
      exact ⟨m, ⟨hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by rw [Nat.mul_comm]; omega)⟩, rfl⟩
    · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm] at hmN
      exact ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), hmN⟩, Dvd.intro m rfl⟩
  rw [himg, Finset.sum_image (by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab), Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [Nat.mul_div_cancel_left m (by omega : 0 < d)]

/--
**The Selberg identity.**
$$\Lambda(n)\log n + (\Lambda * \Lambda)(n) = (\mu * \log^2)(n).$$
-/
theorem vonMangoldt_pmul_log_add_mul :
    vonMangoldt.pmul log + vonMangoldt * vonMangoldt
      = (μ : ArithmeticFunction ℝ) * (log.pmul log) := by
  rw [log_pmul_log, ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul, add_comm]


open Finset in
/--
**Selberg's symmetry formula, in the form that still has the Möbius sum in it:**
$$\sum_{n \le N}\Lambda(n)\log n + \sum_{mn \le N}\Lambda(m)\Lambda(n)
  = \sum_{d \le N}\mu(d)\sum_{m \le N/d}\log^2 m.$$

What remains for the symmetry formula proper is the evaluation of the right-hand side as
`2N\log N + O(N)`, via `∑_{m ≤ y}\log^2 m = y\log^2 y - 2y\log y + 2y + O(\log^2 y)` and the
elementary Möbius sum bounds.
-/
theorem sum_vonMangoldt_pmul_log_add_sum_mul (N : ℕ) :
    ∑ n ∈ Icc 1 N, (vonMangoldt.pmul log) n + ∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ∑ m ∈ Icc 1 (N / d), Real.log m ^ 2 := by
  have hid : ∑ n ∈ Icc 1 N, (vonMangoldt.pmul log) n
      + ∑ n ∈ Icc 1 N, (vonMangoldt * vonMangoldt) n
      = ∑ n ∈ Icc 1 N, ((μ : ArithmeticFunction ℝ) * (log.pmul log)) n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have := congrArg (fun F : ArithmeticFunction ℝ ↦ F n) vonMangoldt_pmul_log_add_mul
    simpa using this
  rw [hid, sum_Icc_mul_apply]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [intCoe_apply]
  refine congrArg _ (Finset.sum_congr rfl fun m _ ↦ ?_)
  rw [pmul_apply, log_apply, sq]


open Finset in
/-- **The classical Möbius identity** `∑_{d ≤ N} μ(d) ⌊N/d⌋ = 1` for `N ≥ 1`. -/
theorem sum_moebius_mul_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) = 1 := by
  have h := sum_Icc_mul_apply (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) N
  rw [coe_moebius_mul_coe_zeta] at h
  have hleft : ∑ n ∈ Icc 1 N, (1 : ArithmeticFunction ℝ) n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb
      rw [ArithmeticFunction.one_apply, if_neg hb]
    · intro h1
      exact absurd (mem_Icc.2 ⟨le_rfl, hN⟩) h1
  rw [hleft] at h
  rw [h]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [intCoe_apply]
  refine congrArg _ ?_
  rw [Finset.sum_congr rfl (fun m hm ↦ ?_), Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    mul_one]
  · simp
  · rw [natCoe_apply, zeta_apply, if_neg (by have := (mem_Icc.1 hm).1; omega), Nat.cast_one]

open Finset in
/-- **`|∑_{d ≤ N} μ(d)/d| ≤ 1`**, the elementary Möbius sum bound. -/
theorem abs_sum_moebius_div_le (N : ℕ) :
    |∑ d ∈ Icc 1 N, (μ d : ℝ) / d| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set S : ℝ := ∑ d ∈ Icc 1 N, (μ d : ℝ) / d with hS
  have hsplit : (N : ℝ) * S - 1
      = ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    rw [hS, Finset.mul_sum, ← sum_moebius_mul_div N hN, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    field_simp
  have hterm : ∀ d ∈ Icc 1 N,
      |(μ d : ℝ) * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| ≤ if d = 1 then 0 else 1 := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hlow : 0 ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
      rw [sub_nonneg, le_div_iff₀ hdR]
      have : (N / d) * d ≤ N := Nat.div_mul_le_self N d
      exact_mod_cast this
    have hhigh : (N : ℝ) / d - ((N / d : ℕ) : ℝ) < 1 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hdR]
      have h1 := Nat.div_add_mod N d
      have h2 : N % d < d := Nat.mod_lt _ (by omega)
      have : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by
        have hnat : N < (N / d) * d + d := by
          rw [Nat.mul_comm]
          omega
        exact_mod_cast hnat
      linarith
    rcases eq_or_ne d 1 with rfl | hd1'
    · simp
    · rw [if_neg hd1', abs_mul]
      have hμ : |(μ d : ℝ)| ≤ 1 := by
        have : |μ d| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        have hcast : |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; ring_nf
        rw [hcast]
        exact_mod_cast this
      have habs : |(N : ℝ) / d - ((N / d : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hlow]
        linarith
      calc |(μ d : ℝ)| * |(N : ℝ) / d - ((N / d : ℕ) : ℝ)| ≤ 1 * 1 :=
            mul_le_mul hμ habs (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
  have hcard : ∑ d ∈ Icc 1 N, (if d = 1 then (0 : ℝ) else 1) = (N : ℝ) - 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.filter_ne', Finset.card_erase_of_mem (mem_Icc.2 ⟨le_rfl, hN⟩),
      Nat.card_Icc]
    have : (N + 1 - 1 - 1 : ℕ) = N - 1 := by omega
    rw [this, Nat.cast_sub hN, Nat.cast_one]
  have hbound : |(N : ℝ) * S - 1| ≤ (N : ℝ) - 1 := by
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← hcard]
    exact Finset.sum_le_sum hterm
  have hle := abs_le.1 hbound
  rw [abs_le]
  constructor
  · nlinarith [hle.1]
  · nlinarith [hle.2]

end Selberg
