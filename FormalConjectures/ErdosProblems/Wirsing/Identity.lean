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
public import FormalConjectures.ErdosProblems.Wirsing.Basic

/-!
# The hyperbola identity for Dirichlet convolutions

The engine of the elementary proof of Wirsing's theorem is the identity
$$\sum_{n \le N} (b * c)(n) = \sum_{d \le N} b(d) \sum_{m \le N/d} c(m),$$
where `*` is Dirichlet convolution.
-/

@[expose] public section

open Finset

namespace Wirsing

/--
Hyperbola summation over divisor pairs: summing a function of a factorisation `n = d * m` over
all `n ≤ N` is the same as summing over all pairs `(d, m)` with `d * m ≤ N`.
-/
@[category API, AMS 11]
theorem sum_Icc_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (G : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, G x.1 x.2
      = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x ↦ ⟨x.2.1, x.2.2⟩) (j := fun y ↦ ⟨y.1 * y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hn1, hnN⟩, hdm, hn0⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hdm; omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hdm; omega)
    refine ⟨⟨hd0, ?_⟩, hm0, ?_⟩
    · calc d ≤ d * m := Nat.le_mul_of_pos_right _ hm0
        _ = n := hdm
        _ ≤ N := hnN
    · rw [Nat.le_div_iff_mul_le hd0, mul_comm m d]
      omega
  · rintro ⟨d, m⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
    obtain ⟨⟨hd1, hdN⟩, hm1, hmN⟩ := hy
    rw [Nat.le_div_iff_mul_le hd1] at hmN
    have hpos : 1 ≤ d * m := by simpa using Nat.mul_le_mul hd1 hm1
    have hle : d * m ≤ N := by rwa [mul_comm]
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨hpos, hle⟩, trivial, by omega⟩
  · rintro ⟨n, d, m⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp [hx.2.1]
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨n, d, m⟩ _
    rfl

/--
Hyperbola summation: the summatory function of a Dirichlet convolution `b * c` is obtained by
summing `b(d)` against the partial sums of `c`.
-/
@[category API, AMS 11]
theorem sum_Icc_dirichlet_mul {R : Type*} [CommSemiring R]
    (b c : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (b * c) n = ∑ d ∈ Icc 1 N, b d * ∑ m ∈ Icc 1 (N / d), c m := by
  simp_rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
  exact sum_Icc_divisorsAntidiagonal (fun d m ↦ b d * c m) N

/--
The fundamental identity of the elementary theory of mean values: writing `Λ` for the von
Mangoldt function,
$$\sum_{n \le N} f(n)\log n = \sum_{d \le N} \Lambda(d) \sum_{m \le N/d} f(dm).$$
-/
@[category API, AMS 11]
theorem sum_Icc_mul_log (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, g n * Real.log n
      = ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ∑ m ∈ Icc 1 (N / d), g (d * m) := by
  have key : ∀ n ∈ Icc 1 N, g n * Real.log n
      = ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.1 * g (x.1 * x.2) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have : ∀ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 * g (x.1 * x.2)
          = ArithmeticFunction.vonMangoldt x.1 * g n := by
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.1 hx).1]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
      Nat.sum_divisorsAntidiagonal (f := fun d _ ↦ ArithmeticFunction.vonMangoldt d),
      ArithmeticFunction.vonMangoldt_sum, mul_comm]
  rw [Finset.sum_congr rfl key,
    sum_Icc_divisorsAntidiagonal (fun d m ↦ ArithmeticFunction.vonMangoldt d * g (d * m)) N]
  exact Finset.sum_congr rfl fun d _ ↦ (Finset.mul_sum _ _ _).symm

end Wirsing
