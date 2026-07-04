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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 403

*References:*
- [erdosproblems.com/403](https://www.erdosproblems.com/403)
- [ErGr80] Erdős, P. and Graham, R. L., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique (1980), p. 79.
- [Li76] Lin, S., _On two problems of Erdős concerning sums of distinct factorials_. Bell
  Laboratories internal memorandum (1960).
-/

open scoped Nat

namespace Erdos403

/-- The sum of the distinct factorials indexed by a finite set $S \subseteq \mathbb{N}$, namely
$\sum_{a \in S} a!$. A "sum of distinct factorials" is exactly `factSum S` for some `S : Finset ℕ`
(distinctness of the summands is automatic, the indices being a set). Note $0! = 1! = 1$. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-- The extremal solution: $2! + 3! + 5! = 2 + 6 + 120 = 128 = 2^7$. -/
@[category test, AMS 11]
theorem factSum_two_three_five : factSum {2, 3, 5} = 2 ^ 7 := by
  rw [factSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  decide

/-- **Erdős Problem 403** (Burr–Erdős): Does the equation
$$2^m = a_1! + \cdots + a_k!$$
with $a_1 < a_2 < \cdots < a_k$ have only finitely many solutions?

The answer is **yes**, proved independently by Frankl and by Lin [Li76]; the largest solution is
$2^7 = 2! + 3! + 5!$. A sum of distinct factorials is `factSum S` for `S : Finset ℕ`, so the
solutions are the sets `S` with `factSum S` a power of two, and the claim is that there are finitely
many such `S`. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos403/Statement.lean"]
theorem erdos_403 : answer(True) ↔ {S : Finset ℕ | ∃ m, factSum S = 2 ^ m}.Finite := by
  sorry

/-- The sharp form of the answer: the largest power of two that is a sum of distinct factorials is
$2^7$, i.e. any solution has $m \le 7$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos403/Statement.lean"]
theorem erdos_403.variants.sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  sorry

end Erdos403
