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
public import FormalConjectures.ErdosProblems.Wirsing.GoodPrime
public import FormalConjectures.ErdosProblems.Wirsing.TuranDeficit

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
**The Tauberian bridge: if `L` converges at all, then `\sigma(N) \to 0`.**

The exact Abel identity `Wirsing.mean_eq_logMean_sub_sum` gives
`\sigma(N) = L(N) - \frac1N\sum_{M<N}L(M)` with no error term, and the second term is a Cesàro
average of `L`.  If `L(N) \to c` then the Cesàro average tends to the *same* `c`, whatever `c`
is, so the difference tends to `0`.

The value of the limit is therefore irrelevant: the crux reduces to the mere **convergence** of
`\sum_{n \le N} f(n)/n`.  In the continuous variable this is the elementary Tauberian fact that
`W' + W \to c` forces `W \to c` and hence `W' \to 0`, with `W(u) = \int_0^u \sigma(e^v)\,dv`.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_tendsto_logMean {c : ℝ}
    (h : Tendsto (logMean f) atTop (𝓝 c)) : Tendsto (mean f) atTop (𝓝 0) := by
  have hL0 : logMean f 0 = 0 := by simp [logMean]
  have hces := h.cesaro
  have hsub : Tendsto (fun N : ℕ ↦ logMean f N - (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, logMean f i)
      atTop (𝓝 0) := by
    simpa using h.sub hces
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hset : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit : ∑ i ∈ Finset.range N, logMean f i = ∑ i ∈ Finset.Ico 1 N, logMean f i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp [hL0]
  rw [mean_eq_logMean_sub_sum f hN, hset, hsplit, div_eq_inv_mul]

/-- `Wirsing.tendsto_mean_atTop_zero_of_tendsto_logMean` with the limit left unnamed: the
convergence of `\sum_{n\le N}f(n)/n` alone gives the mean value `0`. -/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_exists_tendsto_logMean
    (h : ∃ c : ℝ, Tendsto (logMean f) atTop (𝓝 c)) : Tendsto (mean f) atTop (𝓝 0) :=
  h.elim fun _ hc ↦ tendsto_mean_atTop_zero_of_tendsto_logMean f hc

/--
**THE CRUX, in logarithmic form.**  If the bad primes have divergent reciprocal sum then the
logarithmic average *converges*:
$$L(N) = \sum_{n \le N}\frac{f(n)}{n} \longrightarrow c \quad\text{for some } c .$$

The value of `c` does not matter (`Wirsing.tendsto_mean_atTop_zero_of_tendsto_logMean`), so this
is strictly weaker than `L(N) \to 0`; it is the classical statement that the Dirichlet series
of `f` converges at `s = 1`.

`Wirsing.tendsto_mean_atTop_zero_of_tendsto_logMean` reduces the headline to this, and it is
the form to attack: everything about `L` has a factor `\log N` of room that `\sigma` has not.

**This is an overshoot, deliberately.**  The exactly equivalent form of the headline is
`L(N) - \frac1N\sum_{M<N}L(M) \to 0`, which is weaker than convergence of `L`: `\sigma(N) \to 0`
allows `L` to drift, as `\sigma(t) = 1/\log t` shows.  Convergence is nevertheless the form to
prove, because it is the classical statement (the Dirichlet series of `f` converges at `s = 1`,
with limit `0`, the size being `\exp(-\sum_{p \le N}(1 - f(p))/p)` heuristically) and the form
that `Wirsing/Decay.lean`'s machinery is shaped for.

**What is already proved.**  `Wirsing.tendsto_abs_logMean_div_log_atTop_zero` (lap 5, from the
envelope machinery of `Wirsing/Decay.lean`) gives `L(N) = o(\log N)`.  The gap is therefore
`o(\log N) \Rightarrow o(1)`, two whole factors of `\log N`, and the mechanism that must supply
them is the defect weight `1 + f(p)` of `Wirsing.abs_logMean_mul_log_sub_defect_le`, which
vanishes exactly on the primes counted by `hdiv`.

**Why the mean cannot be attacked directly** (lap 13).  The sharp weight comparison
`Wirsing.exists_abs_sum_primeWeight_comp_sub_sum_div_le` gives
`|\sigma(N)|\log N \le \sum_{n\le N}|\sigma(n)|/n + \varepsilon\log N + C`
(`Wirsing.exists_abs_mean_mul_log_le`), whose main term `A\log N` is the *same size* as the
error, so no iteration contracts; and the bad-prime deficit it leaves,
`2\sum_{f(p)=-1}(\log p/p)|\sigma(\lfloor N/p\rfloor)| \approx 2A\beta(N)`, is beaten by that
`\varepsilon\log N` whenever the bad primes are sparse (`\beta(N) = o(\log N)`).  In the
logarithmic variable the main term is `\alpha(\log N)^2/2`, against which an `O(\log N)` error
*is* negligible: that is the whole reason route C works.
-/
@[category API, AMS 11]
theorem exists_tendsto_logMean_of_badPrimeSum_atTop (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    ∃ c : ℝ, Tendsto (logMean f) atTop (𝓝 c) := by
  sorry

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
    Tendsto (mean f) atTop (𝓝 0) :=
  tendsto_mean_atTop_zero_of_exists_tendsto_logMean f
    (exists_tendsto_logMean_of_badPrimeSum_atTop f hf hdiv)

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
