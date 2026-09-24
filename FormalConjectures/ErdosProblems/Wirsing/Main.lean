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
public import FormalConjectures.ErdosProblems.Wirsing.General
public import FormalConjectures.ErdosProblems.Wirsing.Log
public import FormalConjectures.ErdosProblems.Wirsing.Decay
public import FormalConjectures.ErdosProblems.Wirsing.Wintner

/-!
# Wirsing's mean value theorem: assembly

The two halves of Wirsing's theorem for `±1`-valued multiplicative functions, and their
combination.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/--
**Halász in logarithmic form.**  If the bad primes have divergent reciprocal sum then the
logarithmic average is `o(log N)`:
$$L(N) = \sum_{n \le N} \frac{f(n)}{n} = o(\log N).$$
-/
@[category API, AMS 11]
theorem tendsto_logMean_div_log_atTop_zero (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (fun N : ℕ ↦ logMean f N / Real.log N) atTop (𝓝 0) := by
  have h := tendsto_abs_logMean_div_log_atTop_zero f hf hdiv
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  simp only [Function.comp_apply, abs_div, abs_of_nonneg hlog, le_refl]

/--
**The Tauberian step.**  The remaining crux of the divergent case: the logarithmic average
being `o(\log N)` forces the mean value to vanish.

Both facts of the divergent case are kept as hypotheses, because `L(N) = o(\log N)` alone is
not enough by any route that stays inside the `O(1)`-error functional relations of this
development.  Two obstructions were identified:

* `L(N) = o(\log N)` plus `|σ| ≤ 1` plus the log-Lipschitz bound `|σ(N) - σ(M)| ≤ 2(N-M)/N`
  is satisfied by `σ(N) = \cos(θ \log N)`, which does not tend to `0`; the counterexample is
  the Halász obstruction `f(n) = n^{iθ}` and is excluded only by `f` being real.
* the mean-side analogue of `Wirsing.abs_logMean_mul_log_sub_defect_le` is vacuous.  Every
  error term in the chain (the functional relation `Wirsing.abs_mean_mul_log_sub_sum_prime_le`,
  the prime-to-harmonic weight comparison, the hyperbola identity) is `O(\log N)`, while the
  main term `σ(N)\log N` is itself at most `\log N`.  On the logarithmic side the same errors
  were affordable because `L(N)` may be as large as `\log N`.

So the gain must come from a second moment.  [Hi86] proves the quantitative form
`|σ(x)| ≤ γ(1 + ∑_{p ≤ x}(1 - f(p))/p)^{-1/2}`; the square root is the signature of the
Cauchy-Schwarz step, and `Wirsing.tendsto_logMean_div_log_atTop_zero` enters through the
relation `S(x)\log x \sim x L(x)`, valid for real `f`.  See `PENDING_WORK.md`.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_logMean (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop)
    (h : Tendsto (fun N : ℕ ↦ logMean f N / Real.log N) atTop (𝓝 0)) :
    Tendsto (mean f) atTop (𝓝 0) := by
  sorry

/--
The analytic core of the divergent case: `E(N) → ∞` forces `mean f N → 0`.

It is now the composition of the logarithmic Halász bound and the Tauberian step.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_badPrimeSum_atTop (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (mean f) atTop (𝓝 0) :=
  tendsto_mean_atTop_zero_of_logMean f hf hdiv (tendsto_logMean_div_log_atTop_zero f hf hdiv)

/--
The divergent case of Wirsing's theorem: if $\sum_p (1 - f(p))/p = \infty$ then the mean
value of `f` is `0`.

This is the hard half of the theorem; it is the content of [Wi67], with an elementary proof
in [Hi86].
-/
@[category API, AMS 11]
theorem hasMeanValue_zero_of_not_summable (hf : IsPMOneMultiplicative f)
    (h : ¬ Summable (pretentiousSeries f)) : HasMeanValue f 0 :=
  tendsto_mean_atTop_zero_of_badPrimeSum_atTop f hf
    (tendsto_badPrimeSum_atTop_of_not_summable f hf h)

/--
The convergent case of Wirsing's theorem: if $\sum_p (1 - f(p))/p < \infty$ then `f` has a
mean value.

For a `±1`-valued `f` this case is elementary: the convolution `g = f * μ` satisfies
$\sum_n |g(n)|/n < \infty$, so Wintner's mean value theorem applies.  Wintner's theorem itself
is proved in `Wirsing/Wintner.lean`; what remains is the summability, which is the Euler
product estimate `Wirsing.summable_abs_wintnerCoeff_div`.
-/
@[category API, AMS 11]
theorem exists_hasMeanValue_of_summable (hf : IsPMOneMultiplicative f)
    (h : Summable (pretentiousSeries f)) : ∃ L, HasMeanValue f L :=
  exists_hasMeanValue_of_summable' f hf h

/-- Wirsing's mean value theorem for `±1`-valued multiplicative functions. -/
@[category API, AMS 11]
theorem exists_hasMeanValue (hf : IsPMOneMultiplicative f) :
    ∃ L, HasMeanValue f L := by
  by_cases h : Summable (pretentiousSeries f)
  · exact exists_hasMeanValue_of_summable f hf h
  · exact ⟨0, hasMeanValue_zero_of_not_summable f hf h⟩

end Wirsing
