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

*Reference:* [erdosproblems.com/880](https://www.erdosproblems.com/880)

Let `A ⊆ ℕ` be an additive basis of order `k`, and let `B` be the set of integers that are a sum of
`k` or fewer **pairwise distinct** elements of `A` (Burr–Erdős "restricted addition"). Are the gaps
`b_{n+1} − b_n` between consecutive elements of `B` bounded?

This was resolved by N. Hegyvári, F. Hennecart and A. Plagne, *Answer to a question by Burr and Erdős
on restricted addition, and related results*, Combin. Probab. Comput. **16** (2007) 747-756 (DOI
10.1017/S0963548306008224):

* **`k = 2`: YES** — the gaps are eventually at most `2`.
* **`k ≥ 3`: NO** — there is an explicit basis of order `k` whose restricted-sum set has arbitrarily
  long gaps.

A formal Lean proof of both parts is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code and Harmonic's Aristotle.
-/

namespace Erdos880

/-- Integers that are a sum of **exactly `h` pairwise distinct** elements of `A` (the restricted
`h`-fold sumset, written `h × A` in the paper). -/
def restrictedSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ T : Finset ℕ, (↑T ⊆ A) ∧ T.card = h ∧ ∑ a ∈ T, a = n}

/-- Integers that are a sum of **at most `k` (not necessarily distinct)** elements of `A` — the
ordinary "≤ k-fold" sumset, used for the basis condition. -/
def sumsetLE (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ (m : ℕ) (f : Fin m → ℕ), m ≤ k ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- The set `B` of Problem 880: integers that are a sum of `k` or fewer pairwise distinct elements
of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  ⋃ h ∈ Finset.Icc 1 k, restrictedSumset A h

/-- `A` is an additive basis of order `k`: all but finitely many naturals lie in `sumsetLE A k`. -/
def IsBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  {n : ℕ | n ∉ sumsetLE A k}.Finite

/-- `S` has **unbounded gaps**: arbitrarily long runs of consecutive integers are missing from `S`. -/
def UnboundedGaps (S : Set ℕ) : Prop :=
  ∀ G : ℕ, ∃ m : ℕ, ∀ x : ℕ, m ≤ x → x ≤ m + G → x ∉ S

/-- `S` has **gaps eventually bounded by `C`**: beyond some `N`, every integer has a member of `S`
within `C` above it (so consecutive members are `≤ C` apart). -/
def BoundedGapsBy (S : Set ℕ) (C : ℕ) : Prop :=
  ∃ N : ℕ, ∀ x : ℕ, N ≤ x → ∃ y ∈ S, x ≤ y ∧ y ≤ x + C

/-- **Erdős Problem 880 (the resolution, `k ≥ 3`).** For every order `h ≥ 3` there is an additive
basis `A` of order `h` whose set of restricted sums has arbitrarily long gaps. So the Burr–Erdős
gap-boundedness fails for `k ≥ 3`. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/Combinatorics/Erdos880/Statement.lean"]
theorem erdos_880 (h : ℕ) (hh : 3 ≤ h) :
    ∃ A : Set ℕ, IsBasisOfOrder A h ∧ UnboundedGaps (restrictedSums A h) := by
  sorry

/-- **Erdős Problem 880 (the `k = 2` case).** For a basis `A` of order `2`, the restricted-sum set
has gaps eventually bounded by `2`. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/Combinatorics/Erdos880/Statement.lean"]
theorem erdos_880_order_two (A : Set ℕ) (hbasis : IsBasisOfOrder A 2) :
    BoundedGapsBy (restrictedSums A 2) 2 := by
  sorry

end Erdos880
