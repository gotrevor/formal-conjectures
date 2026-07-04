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
# Erdős Problem 482

*References:*
- [erdosproblems.com/482](https://www.erdosproblems.com/482)
- [ErGr80] Erdős, P. and Graham, R. L., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique (1980), p. 96.
- [GrPo70] Graham, R. L. and Pollak, H. O., _Note on a nonlinear recurrence related to $\sqrt{2}$_.
  Math. Mag. (1970), 143-145.
- [St05] Stoll, Th., _On families of nonlinear recurrences related to digits_. J. Integer Seq.
  (2005), Article 05.3.2.
- [St06] Stoll, Th., _On a problem of Erdős and Graham concerning digits_. Acta Arith. (2006),
  89-100.
-/

namespace Erdos482

/-- The Graham–Pollak sequence, indexed from `0`: `u 0 = 1` and
$u_{n+1} = \lfloor \sqrt{2}\,(u_n + 1/2) \rfloor$. This is the sequence $a$ of the problem shifted by
one, `u n` $= a_{n+1}$. -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- The `n`-th (fractional) binary digit of `t` via the floor formula:
$\lfloor t\,2^n \rfloor - 2 \lfloor t\,2^{n-1} \rfloor \in \{0, 1\}$. -/
noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

/-- **Erdős Problem 482** (Graham–Pollak): Define a sequence by $a_1 = 1$ and
$$a_{n+1} = \lfloor \sqrt{2}\,(a_n + 1/2) \rfloor$$
for $n \ge 1$. Then the difference $a_{2n+1} - 2a_{2n-1}$ is the $n$-th digit in the binary expansion
of $\sqrt{2}$. (Erdős also asks for analogous results for $\theta = \sqrt{m}$ and other algebraic
numbers.)

The answer is **yes** [GrPo70]; wide-ranging generalisations are due to Stoll [St05], [St06].

Encoded with the `0`-indexed sequence `u` above (`u n` $= a_{n+1}$), the claim reads
`u (2*n+1) - 2 * u (2*n-1) = binDigit (√2) n`, where `binDigit` extracts the `n`-th fractional
base-2 digit of $\sqrt{2}$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos482/Statement.lean"]
theorem erdos_482 : answer(True) ↔
    ∀ n : ℕ, 1 ≤ n →
      (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  sorry

end Erdos482
