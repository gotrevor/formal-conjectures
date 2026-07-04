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
# Erdős Problem 880

*References:*
- [erdosproblems.com/880](https://www.erdosproblems.com/880)
- [Er98] Erdős, P., _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [HHP07] Hegyvári, N. and Hennecart, F. and Plagne, A., _Answer to a question by Burr and Erdős on
  restricted addition, and related results_. Combin. Probab. Comput. (2007), 747-756.
-/

namespace Erdos880

/-- Integers that are a sum of **exactly `h` pairwise distinct** elements of `A` (the restricted
`h`-fold sumset, written $h \times A$ in the paper). -/
def restrictedSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ T : Finset ℕ, (↑T ⊆ A) ∧ T.card = h ∧ ∑ a ∈ T, a = n}

/-- Integers that are a sum of **at most `k` (not necessarily distinct)** elements of `A` — the
ordinary "$\le k$-fold" sumset, used for the basis condition. -/
def sumsetLE (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ (m : ℕ) (f : Fin m → ℕ), m ≤ k ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- The set $B$ of Problem 880: integers that are a sum of `k` or fewer pairwise distinct elements
of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  ⋃ h ∈ Finset.Icc 1 k, restrictedSumset A h

/-- `A` is an additive basis of order `k`: all but finitely many naturals lie in `sumsetLE A k`. -/
def IsBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  {n : ℕ | n ∉ sumsetLE A k}.Finite

/-- `S` has **gaps eventually bounded by `C`**: beyond some `N`, every integer has a member of `S`
within `C` above it (so consecutive members are $\le C$ apart, i.e. $b_{n+1} - b_n = O(1)$). -/
def BoundedGapsBy (S : Set ℕ) (C : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x → ∃ y ∈ S, x ≤ y ∧ y ≤ x + C

/-- **Erdős Problem 880** (Burr–Erdős): Let $A \subseteq \mathbb{N}$ be an additive basis of order
$k$, and let $B = \{b_1 < b_2 < \cdots\}$ be the set of integers that are a sum of $k$ or fewer
distinct elements of $A$. Is it true that $b_{n+1} - b_n = O(1)$ (where the implied constant may
depend on both $A$ and $k$)?

The answer is **no** in general: Hegyvári, Hennecart, and Plagne [HHP07] showed it holds for
$k = 2$ (in fact $b_{n+1} - b_n \le 2$ for large $n$) but fails for $k \ge 3$. So the claim below,
that *every* additive basis has $O(1)$ gaps in its restricted-sum set, is false — refuted by the
$k \ge 3$ construction. The full dichotomy (the positive $k = 2$ bound and the $k \ge 3$
counterexamples) is developed in the linked repository. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/Combinatorics/Erdos880/Statement.lean"]
theorem erdos_880 : answer(False) ↔
    ∀ (A : Set ℕ) (k : ℕ), IsBasisOfOrder A k →
      ∃ C : ℕ, BoundedGapsBy (restrictedSums A k) C := by
  sorry

end Erdos880
