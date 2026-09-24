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
public import FormalConjectures.ErdosProblems.Wirsing.Weighted

/-!
# Newman's Tauberian theorem and the Prime Number Theorem

Lap 6 established that `Erdos239.erdos_239` is PNT-strength (the Liouville function is an
instance), so a PNT-strength ingredient cannot be avoided.  Lap 9 located exactly where it
enters the elementary route: the window step `Wirsing.eq_of_mean_quotient_close` needs a good
prime in a multiplicative window of ratio `1/(1 - A)`, whose Mertens weight is a *constant*
`\approx A`.  Mertens' first theorem has an `O(1)` error
(`Mertens.abs_sum_log_prime_div_sub_log_le`, constant `\log 4 + 8`), so it cannot certify that
such a window contains any prime at all.  What is needed is the sharp form
$$\sum_{p \le N} \frac{\log p}{p} = \log N - E + o(1),$$
which is equivalent to the Prime Number Theorem.

Mathlib v4.33.1 has no Wiener–Ikehara theorem, no Newman Tauberian theorem and no PNT
(checked this lap), but it does have every analytic input: the analytic continuation of `ζ`,
its simple pole at `1` (`riemannZeta_residue_one`), its non-vanishing on `re s = 1`
(`riemannZeta_ne_zero_of_one_le_re`) and `L(Λ, s) = -ζ'/ζ`.  This file is the decomposition of
that last gap.

The route is Newman's contour-integral proof:

1. `Newman.tendsto_integral_of_analyticOn` — the analytic theorem.  If `F` is bounded and
   locally integrable on `[0,∞)` and its Laplace transform, a priori analytic on `re z > 0`,
   extends analytically to `re z ≥ 0`, then `∫_0^T F → G(0)`.  Proved by integrating
   `G(z)e^{zT}(1 + z^2/R^2)/z` over a contour made of the arc `|z| = R`, `re z > 0` and a
   segment to the left of it; the kernel is `O(1/R)` on the whole contour.
2. `Newman.tendsto_chebyshevPsi_div_atTop_one` — PNT in the form `ψ(x)/x → 1`, applying (1)
   to `F(t) = ψ(e^t)e^{-t} - 1`, whose transform is
   `-ζ'/ζ(z+1)/(z+1) - 1/z`; the non-vanishing of `ζ` on `re s = 1` is exactly what makes it
   analytic on `re z ≥ 0`.
3. `Newman.exists_tendsto_sum_log_prime_div_sub_log` — sharp Mertens, by partial summation
   from (2).  This is the statement the window step consumes.

*References:*
- [Ne80] Newman, D. J., Simple analytic proof of the prime number theorem.
  Amer. Math. Monthly 87 (1980), 693-696.
- [Za97] Zagier, D., Newman's short proof of the prime number theorem.
  Amer. Math. Monthly 104 (1997), 705-708.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Newman

/--
**Newman's analytic theorem.**  A bounded, locally integrable `F : [0,∞) → ℝ` whose Laplace
transform continues analytically to the closed half plane has a convergent improper integral,
with the value given by the continuation at `0`.

Newman's contour argument: for `R > 0` let `Γ` be the boundary of
`\{|z| \le R\} \cap \{re z > -δ\}` and integrate `G(z)e^{zT}(1 + z^2/R^2)/z`.  On `|z| = R`
the kernel has modulus `2|re z|/R^2`, which balances the `e^{(re z)T}` factor on both sides;
the contribution of each piece is `O(1/R)`, uniformly in `T`.

This is the only genuinely new analytic content in the PNT step; everything else is
bookkeeping.  It is stated here rather than in `FormalConjecturesForMathlib/` because that
directory must stay `sorry`-free.
-/
@[category API, AMS 11 30]
theorem tendsto_integral_of_analyticOn {F : ℝ → ℝ} {C : ℝ}
    (hFb : ∀ t, |F t| ≤ C) (hFi : MeasureTheory.LocallyIntegrable F)
    {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G {z : ℂ | 0 ≤ z.re})
    (hGeq : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0 : ℝ), (F t : ℂ) * Complex.exp (-z * (t : ℂ))) :
    Tendsto (fun T : ℝ ↦ ∫ t in Set.Ioc (0 : ℝ) T, F t) atTop (𝓝 (G 0).re) := by
  sorry

/--
**The Prime Number Theorem**, Chebyshev form: `ψ(x) \sim x`.

Apply `Newman.tendsto_integral_of_analyticOn` to `F(t) = ψ(e^t)e^{-t} - 1`, which is bounded
by `Chebyshev.psi_le_const_mul_self`.  Its Laplace transform on `re z > 0` is
`-\frac{ζ'}{ζ}(z+1)/(z+1) - 1/z`, which
`Wirsing.exists_continuousOn_lSeries_vonMangoldt_sub` already exhibits as analytic across
`re z = 0` — that lemma is where `riemannZeta_ne_zero_of_one_le_re` entered the development.
The convergence of `∫_0^∞ (ψ(e^t)e^{-t} - 1)\,dt` plus the monotonicity of `ψ` then forces
`ψ(x)/x → 1`.
-/
@[category research solved, AMS 11]
theorem tendsto_chebyshevPsi_div_atTop_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) atTop (𝓝 1) := by
  sorry

/--
**Sharp Mertens.**  `\sum_{p \le N} \log p/p = \log N - E + o(1)` for a constant `E`.

Partial summation from `Newman.tendsto_chebyshevPsi_div_atTop_one`, after discarding the
proper prime powers with `Mertens.sum_vonMangoldt_div_nonprime_le`.  This is the form the
window step of the rigidity argument needs: it certifies that a multiplicative window of any
fixed ratio `> 1` carries prime weight bounded away from `0`, which
`Mertens.abs_sum_log_prime_div_sub_log_le`, with its `O(1)` error, cannot.
-/
@[category API, AMS 11]
theorem exists_tendsto_sum_log_prime_div_sub_log :
    ∃ E : ℝ, Tendsto (fun N : ℕ ↦ (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / p) - Real.log N) atTop (𝓝 (-E)) := by
  sorry

/--
**Primes in short multiplicative windows.**  For every ratio `c > 1` the Mertens weight of the
primes in `(X, cX]` tends to `\log c`.

This is the immediate corollary of `Newman.exists_tendsto_sum_log_prime_div_sub_log` that the
rigidity window step consumes: with `c = 1/(1 - (A - ρ))` it gives a positive weight of primes
in every window, for all large `X`.
-/
@[category API, AMS 11]
theorem tendsto_sum_log_prime_div_window {c : ℝ} (hc : 1 < c) :
    Tendsto (fun X : ℕ ↦ ∑ p ∈ (Finset.Ioc X ⌊c * X⌋₊).filter Nat.Prime,
      Real.log p / p) atTop (𝓝 (Real.log c)) := by
  sorry

end Newman
