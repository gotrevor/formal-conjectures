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
public import FormalConjectures.ErdosProblems.Wirsing.Contract
public import FormalConjectures.ErdosProblems.Wirsing.Dilation

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

/-!
### The logarithmic crux is FALSE (lap 14)

An earlier lap took as the crux

    exists_tendsto_logMean_of_badPrimeSum_atTop :
      Tendsto (badPrimeSum f) atTop atTop → ∃ c, Tendsto (logMean f) atTop (𝓝 c),

the convergence of the Dirichlet series of `f` at `s = 1`, and reduced the headline to it
through `Wirsing.tendsto_mean_atTop_zero_of_exists_tendsto_logMean`.  **That statement is
false**, so the reduction is a dead end and the lemma has been deleted.

*Counterexample.*  Let `f` be completely multiplicative with `f p = -1` exactly for
`p ≡ 3 (mod 8)`.  Then `badPrimeSum f N = ∑_{p ≡ 3 (8), p ≤ N} 1/p → ∞`, so `hdiv` holds,
while for real `s > 1`
$$F(s) = \sum_n \frac{f(n)}{n^s}
       = \zeta(s)\prod_{p \equiv 3 (8)}\frac{1 - p^{-s}}{1 + p^{-s}}
       \ge \frac{c}{s-1}\exp\Big(-2\sum_{p \equiv 3 (8)}p^{-s}\Big)
       \ge c'(s-1)^{-1/2} ,$$
using `∑_{p ≡ 3 (8)} p^{-s} = \tfrac14\log\frac1{s-1} + O(1)`.  If `logMean f N → c` then
`logMean f` is bounded, and `F(s) = (s-1)\int_1^\infty (\text{logMean } f\ \lfloor t\rfloor)
t^{-s}\,dt` would be bounded as `s \to 1^+`.  It is not.  In fact `logMean f N ≍ √(log N)`
for this `f`; a direct computation to `N = 4·10^6` gives `logMean f N / √(log N) = 1.073`
to three places at every scale from `10^3` up, with `logMean f N` itself rising from `2.86`
to `4.18`.

So `logMean f` may diverge, at rate `√(log N)`, while `mean f N ≍ 1/√(log N) → 0`.  The
identity `logMean f N = ∫_1^N (\text{mean } f\ t)\,dt/t + \text{mean } f\ N` shows why: the
headline only needs the *integrand* to vanish, and the integral of a positive `o(1)` function
need not converge.  `Wirsing.tendsto_mean_atTop_zero_of_tendsto_logMean` above is true but
**unusable**: its hypothesis never holds in the divergent case.
-/

/--
**Elliott's Lipschitz estimate at a prime** — the single remaining open obligation of
Wirsing's theorem.

For every real multiplicative `g` with `|g| \le 1` and every prime `p`,
$$\frac1N\sum_{n \le N} g(n) - \frac{1}{\lfloor N/p\rfloor}\sum_{n \le N/p} g(n)
   \longrightarrow 0 .$$

A composite dilation splits as `D_{ab}(N) = D_a(N) + D_b(\lfloor N/a\rfloor)`, so the prime case
is all that is needed (`Wirsing.dilationInvariant_of_prime`).

Everything else in the divergent case is reduced to this by `Wirsing/Split.lean` and
`Wirsing/Contract.lean`: the coprime splitting identity is exact, the Euler factor of a bad
prime is at most `1 - 1/(2p)`, and `\sum_{p \text{ bad}} 1/p = \infty` then drives the mean to
`0`.  The statement is strictly weaker than the headline — it asserts only that the mean moves
slowly, not that it converges — and it is false for complex `g` (take `g(n) = n^{i\theta}`),
so any proof must use that `g` is real.

*Status.*  Open here.  It is [El79, Ch. 6]; Granville–Harper–Soundararajan derive Halász's
theorem from it in [GHS19].
-/
@[category research open, AMS 11]
theorem dilationInvariant_prime : ∀ g : ℕ → ℝ, IsBddMultiplicative g → ∀ p : ℕ, p.Prime →
    Tendsto (fun N : ℕ ↦ mean g N - mean g (N / p)) atTop (𝓝 0) := by sorry

/-- Elliott's Lipschitz estimate for a general dilation, from the prime case
(`Wirsing.dilationInvariant_of_prime`). -/
@[category API, AMS 11]
theorem dilationInvariant : DilationInvariant :=
  dilationInvariant_of_prime dilationInvariant_prime

/--
**THE CRUX.**  If the bad primes have divergent reciprocal sum then the mean value is `0`:
$$\sum_{p : f(p) = -1}\frac1p = \infty \quad\Longrightarrow\quad
  \frac1N\sum_{n\le N}f(n) \longrightarrow 0 .$$

This is the whole of the remaining content of Wirsing's theorem.  It is stated on `mean`
directly: the logarithmic reformulation is refuted above, and the sharp `\log`-weighted
reformulation is refuted in `PENDING_WORK.md` (lap 13).

**The decomposition that is being built** (`Wirsing/Split.lean`, lap 14).  Split `f` along a
single bad prime `p`: every `n` is uniquely `p^k m` with `p \nmid m`, so with
`v = f \cdot 1_{p \nmid \cdot}`
$$\frac1N\sum_{n\le N}f(n)
   = \sum_{k \ge 0}\frac{f(p^k)}{p^k}\cdot\frac{1}{N/p^k}\sum_{m \le N/p^k}v(m) + O(1/N),$$
an *exact* identity.  If the mean of `v` is asymptotically invariant under dilation by a fixed
integer — `Wirsing.DilationInvariant`, Elliott's Lipschitz estimate — the right-hand side
collapses to `\big(\sum_k f(p^k)p^{-k}\big)\cdot\text{mean } v\ N + o(1)`, and
$$\Big|\sum_{k\ge0}\frac{f(p^k)}{p^k}\Big| \le 1 - \frac1p + \frac1{p(p-1)}
   \le \exp\Big(-\frac{3}{4p}\Big) \qquad (p \ge 5)$$
because `f(p) = -1`.  Iterating over a finite set `T` of bad primes gives
`\limsup_N |\text{mean } f\ N| \le \exp(-\tfrac34\sum_{p \in T}1/p)`, which `hdiv` drives to
`0`.  So the crux reduces to `Wirsing.DilationInvariant`, and *only* to it.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_badPrimeSum_atTop (hf : IsPMOneMultiplicative f)
    (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (mean f) atTop (𝓝 0) :=
  tendsto_mean_atTop_zero_of_dilationInvariant dilationInvariant f hf hdiv

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
