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
public import FormalConjectures.ErdosProblems.Wirsing.Rigidity
public import FormalConjectures.ErdosProblems.Wirsing.Pretentious

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
**The Hildebrand asymptotic**, the whole of the remaining crux:
$$\sum_{n \le x} f(n) \sim \frac{x}{\log x}\sum_{n \le x}\frac{f(n)}{n},
  \qquad\text{that is}\qquad \sigma(N) - \frac{L(N)}{\log N} \to 0.$$

Equivalently, the mean value is asymptotically equal to its own logarithmic average.  This is
the displayed relation of [Hi86] (with `τ = 1`, as the case `f = 1` shows), and it is the
only statement still missing: combined with
`Wirsing.tendsto_logMean_div_log_atTop_zero` it gives the divergent case at once.

It is **false for complex `f`**: for `f(n) = n^{iθ}` one has `L(N) = O(1)` while
`σ(N) \approx N^{iθ}/(1 + iθ)` does not tend to `0`.  So `f` real-valued must be used, and it
is a hypothesis here even though it is not needed for either of the two relations that the
proof starts from.  No divergence hypothesis is needed.

The state of the attack is in `PENDING_WORK.md`.  In outline: with `A = \limsup|σ| > 0` and
`N` near-extremal, `Wirsing.sum_deficit_le` forces the functional relation at `N` to be an
equality term by term, whence `σ(\lfloor N/n\rfloor) \approx sAf(n)` along the quotients
(`Wirsing.mean_quotient_near_extremal`, `Wirsing.sum_bad_weight_le_step`); the log-Lipschitz
bound `Wirsing.abs_mean_sub_mean_le` then makes `f` constant on multiplicative windows
(`Wirsing.eq_of_mean_quotient_close`).  What is missing is a pair of good elements in one
window with different values of `f`.
-/
@[category API, AMS 11]
theorem tendsto_mean_sub_logMean_div_log_atTop_zero (hf : IsPMOneMultiplicative f) :
    Tendsto (fun N : ℕ ↦ mean f N - logMean f N / Real.log N) atTop (𝓝 0) := by
  sorry

/--
**The Tauberian step.**  The logarithmic average being `o(\log N)` forces the mean value to
vanish.  It is now a one-line consequence of the Hildebrand asymptotic, and no longer needs
the divergence hypothesis: that is used only to produce `h`.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_logMean (hf : IsPMOneMultiplicative f)
    (h : Tendsto (fun N : ℕ ↦ logMean f N / Real.log N) atTop (𝓝 0)) :
    Tendsto (mean f) atTop (𝓝 0) := by
  have hsum := (tendsto_mean_sub_logMean_div_log_atTop_zero f hf).add h
  rw [add_zero] at hsum
  exact hsum.congr fun N ↦ by ring

/--
The analytic core of the divergent case: `E(N) → ∞` forces `mean f N → 0`.

It is now the composition of the logarithmic Halász bound and the Tauberian step.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_badPrimeSum_atTop (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (mean f) atTop (𝓝 0) :=
  tendsto_mean_atTop_zero_of_logMean f hf (tendsto_logMean_div_log_atTop_zero f hf hdiv)

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
