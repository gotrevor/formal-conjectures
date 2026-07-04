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

*Reference:* [erdosproblems.com/482](https://www.erdosproblems.com/482)

Consider the Graham–Pollak sequence `u 0 = 1`, `u (n+1) = ⌊√2·(u n + 1/2)⌋`. Is it true that
`u(2n+1) − 2·u(2n−1)` is the `n`-th binary digit of `√2`?

The answer is **yes** (Graham & Pollak, Math. Mag. **43** (1970) 143-145); the clean modern
treatment and generalisations are in T. Stoll, *A fancy way to obtain the binary digits of
759250125·√2*, arXiv:0902.4168. Here `binDigit t n = ⌊t·2ⁿ⌋ − 2⌊t·2ⁿ⁻¹⌋ ∈ {0,1}` is the standard
floor-formula `n`-th base-2 digit.

A formal Lean proof — and the resolution in full generality (every real `w > 0`, every base
`g ≥ 2`, after Stoll) — is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code and Harmonic's Aristotle.
-/

namespace Erdos482

/-- The Graham–Pollak sequence `u 0 = 1`, `u (n+1) = ⌊√2·(u n + 1/2)⌋`. -/
noncomputable def u : ℕ → ℕ
  | 0     => 1
  | n + 1 => ⌊Real.sqrt 2 * ((u n : ℝ) + 1 / 2)⌋₊

/-- The `n`-th binary digit of `t` (Graham–Pollak / Stoll floor formula): `⌊t·2ⁿ⌋ − 2⌊t·2ⁿ⁻¹⌋`. -/
noncomputable def binDigit (t : ℝ) (n : ℕ) : ℤ := ⌊t * 2 ^ n⌋ - 2 * ⌊t * 2 ^ (n - 1)⌋

/-- **Erdős Problem 482 (Graham–Pollak).** For the sequence `u 0 = 1`, `u (n+1) = ⌊√2·(u n + 1/2)⌋`,
the quantity `u(2n+1) − 2·u(2n−1)` equals the `n`-th binary digit of `√2`. So the Graham–Pollak
sequence reads off the binary expansion of `√2`. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos482/Statement.lean"]
theorem erdos_482 (n : ℕ) (hn : 1 ≤ n) :
    (u (2 * n + 1) : ℤ) - 2 * (u (2 * n - 1) : ℤ) = binDigit (Real.sqrt 2) n := by
  sorry

end Erdos482
