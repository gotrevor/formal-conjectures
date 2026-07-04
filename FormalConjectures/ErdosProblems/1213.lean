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
# Erdős Problem 1213

*References:*
- [erdosproblems.com/1213](https://www.erdosproblems.com/1213)
- [He86] Hegyvári, N., _On consecutive sums in sequences_. Acta Math. Hungar. 48 (1986), 193-200.
-/

namespace Erdos1213

/-- The "consecutive sum" of `a` over the index block $[u, v]$ (1-based, $u \le v$):
$a_u + \cdots + a_v$. -/
def csum (a : ℕ → ℕ) (u v : ℕ) : ℕ := ∑ i ∈ Finset.Icc u v, a i

/-- All consecutive-block sums of `a` on blocks inside $[1, s]$ are pairwise distinct (as a function
of the block $(u, v)$); equivalently, no two distinct intervals have equal sums. -/
def AllCSumsDistinct (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂, 1 ≤ u₁ → u₁ ≤ v₁ → v₁ ≤ s → 1 ≤ u₂ → u₂ ≤ v₂ → v₂ ≤ s →
    csum a u₁ v₁ = csum a u₂ v₂ → u₁ = u₂ ∧ v₁ = v₂

/-- **Erdős Problem 1213** (Hegyvári): Let $a, K \ge 1$. Does there exist $f(a, K)$ such that if
$$a = a_1 < \cdots < a_s$$
is a sequence of integers with $a_s > f(a, K)$ and bounded gaps $a_{i+1} - a_i \le K$, then there are
two distinct intervals $I$ and $J$ with $\sum_{i \in I} a_i = \sum_{j \in J} a_j$?

The answer is **yes** [He86], with an explicit bound of the shape $f(a, K) \ll a \, e^{O(K)}$ (recorded
as `variants.explicit_bound` below). Two distinct intervals with equal sums is the negation of
`AllCSumsDistinct`. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/Combinatorics/Erdos1213/Statement.lean"]
theorem erdos_1213 : answer(True) ↔
    ∀ (a₁ K : ℕ), 1 ≤ a₁ → 1 ≤ K →
      ∃ f : ℝ, ∀ (a : ℕ → ℕ) (s : ℕ), a 1 = a₁ → 1 ≤ s →
        (∀ i, 1 ≤ i → i < s → a i < a (i + 1)) →
        (∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K) →
        f < (a s : ℝ) →
          ¬ AllCSumsDistinct a s := by
  sorry

/-- Hegyvári's explicit bound [He86]: any strictly increasing positive sequence with gaps at most `K`
whose consecutive-block sums are all distinct has last term bounded by
$$a_s < \left(a_1 + \tfrac{K}{2}\right) e^{K+1} + K \, e^{2K+2}.$$
This gives an admissible witness $f$ for the existence question above. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/Combinatorics/Erdos1213/Statement.lean"]
theorem erdos_1213.variants.explicit_bound (a : ℕ → ℕ) (s K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (ha1 : 1 ≤ a 1)
    (hmono : ∀ i, 1 ≤ i → i < s → a i < a (i + 1))
    (hgap : ∀ i, 1 ≤ i → i < s → a (i + 1) ≤ a i + K)
    (hdist : AllCSumsDistinct a s) :
    (a s : ℝ) <
      ((a 1 : ℝ) + (K : ℝ) / 2) * Real.exp ((K : ℝ) + 1)
        + (K : ℝ) * Real.exp (2 * (K : ℝ) + 2) := by
  sorry

end Erdos1213
