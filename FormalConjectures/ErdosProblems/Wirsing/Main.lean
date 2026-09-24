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
public import FormalConjectures.ErdosProblems.Wirsing.Weighted
public import FormalConjectures.ErdosProblems.Wirsing.Extremal
public import FormalConjectures.ErdosProblems.Wirsing.Sharp

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
**The divergent case, as a single statement.**  If the bad primes have divergent reciprocal
sum then the mean value is `0`.

This is the whole of the remaining crux.  Earlier laps stated it as the unconditional
Hildebrand asymptotic `\sigma(N) - L(N)/\log N \to 0`; that statement is strictly stronger
than the headline needs, and lap 10's deficit-budget argument refuted the only route to it
that the repository had.  The divergence hypothesis is put back where Wirsing and Halász use
it.

**What the crux says, in the log variable.**  Partial summation gives
`L(N) = \int_1^N \sigma(t)\,dt/t + \sigma(N)`, so with `u = \log N` and `F(u) = \sigma(e^u)`
the Hildebrand asymptotic is exactly
$$F(u) - \frac1u\int_0^u F(v)\,dv \to 0 :$$
a bounded function agrees with its own logarithmic average.  That is false for a general
bounded `F` — take `F(u) = \cos u` — and the counterexample is precisely `f(n) = n^{i\theta}`,
which is why real-valuedness has to enter.  So the crux is a non-oscillation statement at
every frequency `\theta`, and `Wirsing.tendsto_logMean_div_log_atTop_zero` supplies the
logarithmic average: under `hdiv` it is `o(\log N)`, i.e. the average side already tends to
`0` and only `F(u) \to 0` is left.

**The two inputs that are now proved.**  Non-pretentiousness at frequency `\theta = 0` is the
hypothesis `hdiv` itself.  At `\theta \ne 0` it is
`Wirsing.eventually_sum_primeWeight_one_sub_mul_cos_ge`
(`\sum_{p \le N}(\log p/p)(1 - f(p)\cos(\theta\log p)) \ge \log N/8`), made uniform on compact
ranges of `\theta` by `Wirsing.exists_forall_primeDefect_ge`.  The quantitative prime input
that every such argument needs — a multiplicative window of fixed ratio carries prime weight
bounded away from `0` — is `Newman.tendsto_sum_log_prime_div_window`, proved from the
prime number theorem in `Wirsing/Newman.lean`.

The state of the attack is in `PENDING_WORK.md`.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_badPrimeSum_atTop (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (mean f) atTop (𝓝 0) := by
  sorry

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
