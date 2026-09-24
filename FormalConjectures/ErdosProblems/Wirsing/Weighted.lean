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
public import FormalConjectures.ErdosProblems.Wirsing.Pretentious

/-!
# Non-pretentiousness in the Mertens weight

`Wirsing/Pretentious.lean` proves the *unweighted* divergence
$\sum_p (1 - f(p)\cos(t\log p))/p = \infty$.  The functional relation of route C,
$$\sigma(N)\log N = \sum_{p \le N}\frac{\log p}{p} f(p)\,\sigma(\lfloor N/p\rfloor) + O(1),$$
consumes the same quantity in the **Mertens weight** `\log p / p`, and at the rate
`\gg \log N`: that is exactly the statement that the symbol `1 + \hat\nu(\tau)` of the
averaging operator is bounded away from `0`, which is what makes the relation contractive
instead of stalling at `A \le A`.

The unweighted divergence is strictly weaker (a set of primes can have divergent
`\sum 1/p` and yet `\sum \log p/p = o(\log N)`), so this file is not a corollary of the
previous one.  The route is through the *logarithmic derivative* rather than the logarithm:
mathlib's `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁` says that
$$\sum_n \Lambda(n) n^{-s} - \frac{1}{s-1}$$
extends continuously to `re s ≥ 1` (using `riemannZeta_ne_zero_of_one_le_re`), whence
`\sum_n \Lambda(n)n^{-1-x}(1 - \cos(t\log n)) = 1/x + O_t(1)`; Mertens' first theorem then
converts this to the partial sum over `p \le N`.

*References:*
- [GS] Granville, A. and Soundararajan, K., *Multiplicative Number Theory I*.
-/

@[expose] public section

open Filter Finset Complex

open scoped Topology

namespace Wirsing

/--
**The twisted von Mangoldt sum on the `1`-line.**  For `t ≠ 0`,
$$\sum_n \frac{\Lambda(n)}{n^{1+x}}\bigl(1 - \cos(t\log n)\bigr) \ge \frac{1}{x} - C_t
  \qquad (0 < x \le 1).$$

The `1/x` comes from the pole of `ζ` at `1`; the constant `C_t` absorbs both
`-ζ'/ζ(1+x) - 1/x` (continuous at `1` by
`DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁` for the trivial character
mod `1`) and `\mathrm{Re}\,(-ζ'/ζ)(1+x+it)`, which is bounded because
`riemannZeta_ne_zero_of_one_le_re` gives `ζ(1+it) ≠ 0`.

This is the first place in the development where the **non-vanishing** of `ζ` on `re s = 1` is
genuinely needed; `Wirsing.not_summable_one_sub_cos` needed only continuity.
-/
@[category API, AMS 11]
theorem exists_tsum_vonMangoldt_twisted_ge {t : ℝ} (ht : t ≠ 0) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      1 / x - C ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + x) *
        (1 - Real.cos (t * Real.log n)) := by
  sorry

/--
**The Mertens-weighted deficit.**  For `t ≠ 0`,
$$\sum_{p \le N} \frac{\log p}{p}\bigl(1 - \cos(t\log p)\bigr) \ge \frac{\log N}{4} - C_t.$$

Obtained from `Wirsing.exists_tsum_vonMangoldt_twisted_ge` at `x = 1/\log N`: the tail
`\sum_{n > N}\Lambda(n)n^{-1-x}` is `e^{-1}\log N + O(1)` by Mertens' first theorem
(`Mertens.abs_sum_vonMangoldt_div_sub_log_le`), so at most `2e^{-1}\log N + O(1)` of the total
`1/x = \log N` is lost, leaving `(1 - 2/e)\log N > \log N/4`.  The proper prime powers are
dropped with `Mertens.sum_vonMangoldt_div_nonprime_le`.
-/
@[category API, AMS 11]
theorem exists_sum_primeWeight_one_sub_cos_ge {t : ℝ} (ht : t ≠ 0) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Real.log N / 4 - C ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * (1 - Real.cos (t * Real.log p)) := by
  sorry

/--
**The symbol of the averaging operator is bounded away from `1`.**  For a `{±1}`-valued
multiplicative `f` and `t ≠ 0`,
$$\sum_{p \le N} \frac{\log p}{p}\bigl(1 - f(p)\cos(t\log p)\bigr) \ge \frac{\log N}{16} - C_t.$$

This is the weighted form of `Wirsing.not_summable_one_sub_mul_cos`, and it is the
quantitative statement that kills the Halász obstruction `σ(e^u) = A\cos(tu + φ)` in the
route-C relation.  As there, the transfer is `|f(p)^2 - (p^{it})^2| ≤ 2|f(p) - p^{it}|`, valid
because `f(p)` is a sign.
-/
@[category API, AMS 11]
theorem exists_sum_primeWeight_one_sub_mul_cos_ge (f : ℕ → ℝ) (hf : IsPMOneMultiplicative f)
    {t : ℝ} (ht : t ≠ 0) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Real.log N / 16 - C ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * (1 - f p * Real.cos (t * Real.log p)) := by
  obtain ⟨C, hC⟩ := exists_sum_primeWeight_one_sub_cos_ge (t := 2 * t) (by simpa using ht)
  refine ⟨C / 4, fun N hN ↦ ?_⟩
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * (1 - Real.cos (2 * t * Real.log p)) / 4
        ≤ Real.log p / p * (1 - f p * Real.cos (t * Real.log p)) := by
    intro p hp
    obtain ⟨hp1, hpp⟩ := mem_filter.1 hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hw : 0 ≤ Real.log p / p := by
      have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      positivity
    have hkey := one_sub_cos_two_mul_le (θ := t * Real.log (p : ℝ)) (ε := f p)
      (hf.pmOne p (by linarith [(mem_Icc.1 hp1).1] ))
    rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring] at hkey
    nlinarith [hw, hkey]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_div] at hsum
  have := hC N hN
  linarith

end Wirsing
