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

/--
**The Selberg identity.**
$$\Lambda(n)\log n + (\Lambda * \Lambda)(n) = (\mu * \log^2)(n).$$
-/
theorem vonMangoldt_pmul_log_add_mul :
    vonMangoldt.pmul log + vonMangoldt * vonMangoldt
      = (μ : ArithmeticFunction ℝ) * (log.pmul log) := by
  rw [log_pmul_log, ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul, add_comm]

end Selberg
