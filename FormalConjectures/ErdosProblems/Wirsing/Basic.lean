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
# Wirsing's mean value theorem for `±1`-valued multiplicative functions

This file sets up the statement of Wirsing's theorem in the special case needed for
Erdős problem 239: every multiplicative `f : ℕ → ℝ` taking only the values `±1` has a
mean value.

The proof splits on whether the *pretentious distance* series $\sum_p (1 - f(p))/p$
converges.

* If it diverges, the mean value is $0$.
* If it converges, the mean value is the Euler product
  $\prod_p (1 - 1/p)\left(1 + f(p)/p + f(p^2)/p^2 + \cdots\right)$.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter

open scoped Topology

namespace Wirsing

/-- The hypotheses of Erdős problem 239: `f` is multiplicative and takes only the values `±1`
on positive integers. -/
structure IsPMOneMultiplicative (f : ℕ → ℝ) : Prop where
  /-- `f` takes the values `±1` on positive integers. -/
  pmOne : ∀ n ≥ 1, f n = 1 ∨ f n = -1
  /-- `f` is multiplicative on coprime arguments. -/
  map_mul_of_coprime : ∀ m n, m.Coprime n → f (m * n) = f m * f n
  /-- `f 1 = 1`. -/
  map_one : f 1 = 1

/-- The Cesàro average $\frac{1}{N}\sum_{n \le N} f(n)$. -/
noncomputable def mean (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ Finset.Icc 1 N, f n) / N

/-- `f` has mean value `L`. -/
def HasMeanValue (f : ℕ → ℝ) (L : ℝ) : Prop := Tendsto (mean f) atTop (𝓝 L)

/-- The terms of the pretentious distance series $\sum_p (1 - f(p))/p$. -/
noncomputable def pretentiousSeries (f : ℕ → ℝ) (p : Nat.Primes) : ℝ := (1 - f p) / (p : ℕ)

end Wirsing
