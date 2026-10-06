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
# Kolakoski sequence

The Kolakoski sequence $1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, \dots$ consists only of $1$s and
$2$s, starts with $a(1) = 1$, and $a(n)$ is the length of its $n$-th run. Its runs alternate
between $1$s and $2$s, starting with $1$s.

*References:*
- [A000002](https://oeis.org/A000002)
- [Ko65] W. Kolakoski, *Problem 5304*, Amer. Math. Monthly **72** (1965), p. 674.
- [Ke91] M. S. Keane, *Ergodic theory and subshifts of finite type*, in T. Bedford, M. Keane and
  C. Series (eds.), *Ergodic Theory, Symbolic Dynamics and Hyperbolic Spaces*, Oxford University
  Press (1991), pp. 35-70, esp. p. 50.
- [Ch93] V. Chvátal, *Notes on the Kolakoski sequence*, DIMACS Technical Report 93-84 (1993).
-/

@[expose] public section

namespace OeisA2

/-- The terms in the first $k + 2$ runs of the sequence. Run $i$ (counting from $0$) has
length $a(i + 1)$ and consists of $1$s for even $i$ and of $2$s for odd $i$. The first two runs
are $1$ and $2, 2$. -/
def kolakoskiPrefix : ℕ → List ℕ
  | 0 => [1, 2, 2]
  | k + 1 =>
    let l := kolakoskiPrefix k
    l ++ List.replicate (l.getD (k + 2) 0) (if k % 2 = 0 then 1 else 2)

/-- The Kolakoski sequence, with $a(0) = 0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (kolakoskiPrefix n).getD n 0

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 2 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = 1 := by decide

@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by decide

@[category test, AMS 11]
theorem a_9 : a 9 = 2 := by decide

@[category test, AMS 11]
theorem a_10 : a 10 = 1 := by decide

/-- The first $40$ terms agree with the OEIS data. -/
@[category test, AMS 11]
theorem take_forty : (List.range 40).map (fun n ↦ a (n + 1)) =
    [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2,
      1, 1, 2, 1, 2, 2, 1, 2, 2, 1] := by
  decide

/--
"It is an unsolved problem to show that the density of 1's is equal to 1/2."
- [A000002]

Keane asked whether the density of $1$s exists and equals $1/2$ [Ke91].
-/
@[category research open, AMS 11 68]
theorem hasDensity_one_half : {n | a n = 1}.HasDensity (1 / 2) := by
  sorry

/-- Chvátal proved that the upper density of $1$s is less than $0.50084$ [Ch93]. -/
@[category research solved, AMS 11 68]
theorem hasDensity_one_half.variants.upperDensity_lt :
    {n | a n = 1}.upperDensity < 0.50084 := by
  sorry

end OeisA2
