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
# Karamata's Tauberian theorem for Dirichlet series

If `a n ≥ 0` and the Dirichlet series `S(x) = ∑_n a_n n^{-x}` satisfies `x S(x) → c` as
`x → 0⁺`, then `∑_{n ≤ e^V} a_n ∼ cV`.

This is Karamata's Tauberian theorem in the form needed for Erdős 239.  Applied to
`a_n = (Λ(n)/n)(1 - \cos(t\log n))`, whose transform is `1/x + O_t(1)` by
`Wirsing.exists_abs_tsum_vonMangoldt_twisted_sub_le`, it gives
$$\sum_{p \le N} \frac{\log p}{p}\cos(t\log p) = o(\log N) \qquad (t \ne 0),$$
the estimate that the resonance step of the crux needs.

The proof is the classical one and uses no measure theory.  Write
`Λ_x(g) = x ∑_n a_n n^{-x} g(n^{-x})`, a positive linear functional on `C[0,1]` (the points
`n^{-x}` lie in `(0,1]`).  On the monomial `u^k` it is `((k+1)x S((k+1)x))/(k+1)`, which tends
to `c/(k+1) = c∫_0^1 u^k du`; by Weierstrass approximation and positivity, `Λ_x(g) → c∫_0^1 g`
for every continuous `g`.  Taking `g` to be a continuous approximation of
`u \mapsto u^{-1}\mathbf 1_{[e^{-1},1]}(u)` — whose value under `Λ_x` is exactly
`x\sum_{n \le e^{1/x}} a_n` — gives the conclusion.

*References:*
- [Ka31] Karamata, J., Neuer Beweis und Verallgemeinerung der Tauberschen Sätze.
  Math. Z. 33 (1931), 294-299.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Karamata

variable (a : ℕ → ℝ)

/-- The Karamata functional `Λ_x(g) = x ∑_n a_n n^{-x} g(n^{-x})`. -/
noncomputable def functional (x : ℝ) (g : ℝ → ℝ) : ℝ :=
  x * ∑' n : ℕ, a n * (n : ℝ) ^ (-x) * g ((n : ℝ) ^ (-x))

/-- The Dirichlet series `S(x) = ∑_n a_n n^{-x}`. -/
noncomputable def series (x : ℝ) : ℝ := ∑' n : ℕ, a n * (n : ℝ) ^ (-x)

variable {a}

/-- The points `n^{-x}` of the Karamata functional lie in `[0,1]` for `x > 0`. -/
@[category API, AMS 11]
theorem rpow_neg_mem_Icc {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (n : ℝ) ^ (-x) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg n) _, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [show (-x) = -x from rfl]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

/-- On the monomial `u ^ k` the Karamata functional is an explicit rescaling of the series. -/
@[category API, AMS 11]
theorem functional_pow (ha0 : a 0 = 0) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    functional a x (fun u ↦ u ^ k)
      = (((k : ℝ) + 1) * x * series a (((k : ℝ) + 1) * x)) / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcongr : ∀ n : ℕ, a n * (n : ℝ) ^ (-x) * ((n : ℝ) ^ (-x)) ^ k
      = a n * (n : ℝ) ^ (-(((k : ℝ) + 1) * x)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-x)) k, ← Real.rpow_mul hn0.le, mul_assoc,
        ← Real.rpow_add hn0]
      congr 2
      ring
  rw [functional, series]
  simp only [hcongr]
  field_simp

end Karamata
