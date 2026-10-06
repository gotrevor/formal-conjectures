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

/-!
# Markov uniqueness conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Markov_number)
- [Fr13] G. Frobenius, *Über die Markoffschen Zahlen*, S. B. Preuss. Akad. Wiss. (1913),
  pp. 458-487.
- [Ai13] M. Aigner, *Markov's Theorem and 100 Years of the Uniqueness Conjecture*, Springer (2013).
-/

@[expose] public section

namespace MarkovUniqueness

/-- A Markov triple is a triple of positive integers $(x, y, z)$ with
$x^2 + y^2 + z^2 = 3xyz$. -/
def IsMarkovTriple (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

instance (x y z : ℕ) : Decidable (IsMarkovTriple x y z) := by
  unfold IsMarkovTriple
  infer_instance

/-- A Markov number is a number that appears in some Markov triple. The equation is symmetric,
so it suffices to look at the last entry. -/
def IsMarkovNumber (c : ℕ) : Prop :=
  ∃ x y, IsMarkovTriple x y c

@[category test, AMS 11]
theorem isMarkovTriple_small : IsMarkovTriple 1 1 1 ∧ IsMarkovTriple 1 1 2 ∧
    IsMarkovTriple 1 2 5 ∧ IsMarkovTriple 1 5 13 ∧ IsMarkovTriple 2 5 29 ∧
    IsMarkovTriple 5 13 194 := by
  decide

@[category test, AMS 11]
theorem not_isMarkovNumber_zero : ¬ IsMarkovNumber 0 := by
  simp [IsMarkovNumber, IsMarkovTriple]

@[category test, AMS 11]
theorem not_isMarkovTriple_1_2_3 : ¬ IsMarkovTriple 1 2 3 := by
  decide

/-- $(1, 1, 1)$ is the only normalized Markov triple with largest entry $1$. -/
@[category test, AMS 11]
theorem existsUnique_one : ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧ IsMarkovTriple p.1 p.2 1 := by
  refine ⟨(1, 1), by decide, fun ⟨x, y⟩ ⟨hxy, hy, h⟩ ↦ ?_⟩
  have key : ∀ y ≤ 1, ∀ x ≤ y, IsMarkovTriple x y 1 → (x, y) = (1, 1) := by decide
  exact key y hy x hxy h

/-- $(2, 5, 29)$ is the only normalized Markov triple with largest entry $29$. -/
@[category test, AMS 11]
theorem existsUnique_29 : ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.2 ≤ 29 ∧ IsMarkovTriple p.1 p.2 29 := by
  refine ⟨(2, 5), by decide, fun ⟨x, y⟩ ⟨hxy, hy, h⟩ ↦ ?_⟩
  have key : ∀ y ≤ 29, ∀ x ≤ y, IsMarkovTriple x y 29 → (x, y) = (2, 5) := by decide
  exact key y hy x hxy h

/--
**Markov uniqueness conjecture** (Frobenius [Fr13]): for every Markov number $c$ there is exactly
one normalized Markov triple $(a, b, c)$, with $a \le b \le c$, that has $c$ as its largest entry.
-/
@[category research open, AMS 11]
theorem markov_uniqueness (c : ℕ) (hc : IsMarkovNumber c) :
    ∃! p : ℕ × ℕ, p.1 ≤ p.2 ∧ p.2 ≤ c ∧ IsMarkovTriple p.1 p.2 c := by
  sorry

end MarkovUniqueness
