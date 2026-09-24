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

/-! ### Abel summation against the harmonic weight -/

/--
**Abel summation for the weight `1/n`,** in purely discrete form.  With
`A(N) = \sum_{n \le N} a_n`,
$$\sum_{n \le N}\frac{a_n}{n} = \frac{A(N)}{N} + \sum_{m < N}\frac{A(m)}{m(m+1)} .$$

This is the bridge from Chebyshev's `ψ` to the Mertens sum `\sum_{n \le N}\Lambda(n)/n`,
and it replaces the usual `\int_1^x \psi(t)/t^2\,dt` by a series, which avoids all
integration bookkeeping: the telescoping identity `1/n = 1/N + \sum_{n \le m < N}
(1/m - 1/(m+1))` is exact.

Applied with `a = Λ` and `A = ψ`, the main term is
`\sum_{m < N} 1/(m+1) = \log N + γ - 1 + o(1)` and the error is
`\sum_{m < N}(ψ(m) - m)/(m(m+1))`, whose convergence is precisely what Newman's analytic
theorem delivers.
-/
@[category API, AMS 11 40]
theorem sum_div_eq_abel (a : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, a n / n
      = (∑ n ∈ Finset.Icc 1 N, a n) / N
        + ∑ m ∈ Finset.Icc 1 (N - 1), (∑ n ∈ Finset.Icc 1 m, a n) / (m * (m + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hsucc : ∀ g : ℕ → ℝ, ∑ k ∈ Finset.Icc 1 (n + 1), g k
        = (∑ k ∈ Finset.Icc 1 n, g k) + g (n + 1) :=
      fun g ↦ Finset.sum_Icc_succ_top (by omega) g
    have htail : ∑ m ∈ Finset.Icc 1 (n + 1 - 1), (∑ k ∈ Finset.Icc 1 m, a k) / (m * (m + 1))
        = (∑ m ∈ Finset.Icc 1 (n - 1), (∑ k ∈ Finset.Icc 1 m, a k) / (m * (m + 1)))
          + (∑ k ∈ Finset.Icc 1 n, a k) / (n * (n + 1)) := by
      rw [show n + 1 - 1 = n from by omega, show n = (n - 1) + 1 from by omega,
        Finset.sum_Icc_succ_top (by omega)]
      simp [show n - 1 + 1 = n from by omega]
    rw [hsucc (fun k ↦ a k / k), ih, hsucc a, htail]
    push_cast
    field_simp
    ring

/-- `\sum_{1 \le m < N} 1/(m+1) = H_N - 1`. -/
@[category API, AMS 11]
theorem sum_one_div_succ_eq_harmonic_sub {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (m + 1) = (harmonic N : ℝ) - 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hstep : ∑ m ∈ Finset.Icc 1 (n + 1 - 1), (1 : ℝ) / (m + 1)
        = (∑ m ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / (m + 1)) + 1 / ((n : ℝ) + 1) := by
      rw [show n + 1 - 1 = n from by omega, show n = (n - 1) + 1 from by omega,
        Finset.sum_Icc_succ_top (by omega)]
      simp [show n - 1 + 1 = n from by omega]
    rw [hstep, ih, harmonic_succ]
    push_cast
    ring

/--
**Sharp Mertens from the two Newman inputs.**  If `ψ(N)/N → 1` and the error series
`\sum_m (ψ(m) - m)/(m(m+1))` converges, then
$$\sum_{n \le N}\frac{\Lambda(n)}{n} = \log N - E + o(1),
  \qquad E = -\gamma - \sum_m \frac{ψ(m) - m}{m(m+1)} .$$

Both hypotheses come from `Newman.tendsto_integral_of_analyticOn`; the summability is the
*direct* output of the analytic theorem and does not wait on `ψ(x) \sim x`.  Everything else
here is `Newman.sum_div_eq_abel` plus mathlib's
`Real.tendsto_harmonic_sub_log`.
-/
@[category API, AMS 11]
theorem exists_tendsto_sum_vonMangoldt_div_sub_log
    (hpsi : Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N) atTop (𝓝 1))
    (hsum : Summable (fun m : ℕ ↦ (Chebyshev.psi m - m) / (m * (m + 1)))) :
    ∃ E : ℝ, Tendsto (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n) - Real.log N)
      atTop (𝓝 (-E)) := by
  classical
  set g : ℕ → ℝ := fun m ↦ (Chebyshev.psi m - m) / (m * (m + 1)) with hg
  -- `ψ` is the partial sum of `Λ`
  have hpsiSum : ∀ m : ℕ, Chebyshev.psi m = ∑ n ∈ Finset.Icc 1 m,
      ArithmeticFunction.vonMangoldt n := by
    intro m
    rw [Chebyshev.psi, Nat.floor_natCast]
    rfl
  -- the tail series, indexed by `range`
  have hg0 : g 0 = 0 := by simp [hg]
  have hrange : ∀ N : ℕ, 1 ≤ N → ∑ m ∈ Finset.Icc 1 (N - 1), g m = ∑ m ∈ Finset.range N, g m := by
    intro N hN
    have hIco : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hcons := Finset.sum_Ico_consecutive g (Nat.zero_le 1) hN
    have hbot : ∑ m ∈ Finset.Ico 0 1, g m = 0 := by simp [hg0]
    rw [hIco, Finset.range_eq_Ico]
    linarith [hcons, hbot]
  have htail : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, g m) atTop (𝓝 (∑' m, g m)) :=
    hsum.hasSum.tendsto_sum_nat
  have hharm := Real.tendsto_harmonic_sub_log
  refine ⟨-(Real.eulerMascheroniConstant + ∑' m, g m), ?_⟩
  have hlim : Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N + ((harmonic N : ℝ) - Real.log N) - 1
      + ∑ m ∈ Finset.range N, g m) atTop
      (𝓝 (1 + Real.eulerMascheroniConstant - 1 + ∑' m, g m)) :=
    ((hpsi.add hharm).sub_const 1).add htail
  rw [show -(-(Real.eulerMascheroniConstant + ∑' m, g m))
      = 1 + Real.eulerMascheroniConstant - 1 + ∑' m, g m by ring]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have habel := sum_div_eq_abel (fun n ↦ ArithmeticFunction.vonMangoldt n) hN
  have hsplit : ∀ m ∈ Finset.Icc 1 (N - 1),
      (∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n) / ((m : ℝ) * (m + 1))
        = 1 / ((m : ℝ) + 1) + g m := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hm1' : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    rw [hg, ← hpsiSum m]
    field_simp
    ring
  rw [habel, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_one_div_succ_eq_harmonic_sub hN, hrange N hN, ← hpsiSum N]
  ring

/--
**Newman's convergent integral, in discrete form.**  The error series of Chebyshev's `ψ`
against the main term converges:
$$\sum_{m}\frac{\psi(m) - m}{m(m+1)} < \infty .$$

This is the *direct* output of `Newman.tendsto_integral_of_analyticOn` applied to
`F(t) = \psi(e^t)e^{-t} - 1` — the analytic theorem proves the convergence of
`\int_0^\infty F`, which is this series up to the change of variable `t = \log m` — and it
comes **before** `\psi(x) \sim x`, which is deduced from it by the monotonicity of `ψ`.
Separated out here so that everything downstream of the two Newman inputs is proved.
-/
@[category API, AMS 11]
theorem summable_psi_sub_div :
    Summable (fun m : ℕ ↦ (Chebyshev.psi m - m) / (m * (m + 1))) := by
  sorry

/--
**The Prime Number Theorem along the integers**, the form the Mertens reduction consumes.
An immediate restriction of `Newman.tendsto_chebyshevPsi_div_atTop_one`.
-/
@[category API, AMS 11]
theorem tendsto_chebyshevPsi_nat_div_atTop_one :
    Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N) atTop (𝓝 1) :=
  tendsto_chebyshevPsi_div_atTop_one.comp tendsto_natCast_atTop_atTop

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
  classical
  obtain ⟨E, hE⟩ := exists_tendsto_sum_vonMangoldt_div_sub_log
    tendsto_chebyshevPsi_nat_div_atTop_one summable_psi_sub_div
  -- the proper prime powers
  set D : ℕ → ℝ := fun N ↦ ∑ d ∈ (Finset.Icc 1 N).filter (fun d ↦ ¬ d.Prime),
    ArithmeticFunction.vonMangoldt d / d with hD
  have hDnn : ∀ N, 0 ≤ D N := fun N ↦
    Finset.sum_nonneg fun d _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hDmono : Monotone D := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hab)
    · exact fun d _ _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hDbdd : BddAbove (Set.range D) := by
    refine ⟨4, ?_⟩
    rintro x ⟨N, rfl⟩
    exact Mertens.sum_vonMangoldt_div_nonprime_le N
  have hDlim : Tendsto D atTop (𝓝 (⨆ N, D N)) := tendsto_atTop_ciSup hDmono hDbdd
  -- splitting the von Mangoldt sum at the primes
  have hsplit : ∀ N : ℕ, (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p)
      = (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n) - D N := by
    intro N
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime
      (fun n ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ))
    have hprime : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt p / (p : ℝ)
        = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2]
    rw [hD]
    rw [hprime] at h
    linarith [h]
  refine ⟨E + ⨆ N, D N, ?_⟩
  have hlim := hE.sub hDlim
  rw [show -(E + ⨆ N, D N) = -E - ⨆ N, D N by ring]
  refine hlim.congr fun N ↦ ?_
  rw [hsplit N]
  ring

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
  classical
  obtain ⟨E, hE⟩ := exists_tendsto_sum_log_prime_div_sub_log
  set g : ℕ → ℝ := fun N ↦ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p with hg
  have hc0 : (0 : ℝ) < c := by linarith
  -- `X ≤ ⌊cX⌋`
  have hfl : ∀ X : ℕ, X ≤ ⌊c * X⌋₊ := by
    intro X
    refine Nat.le_floor ?_
    have : (1 : ℝ) * X ≤ c * X := by
      refine mul_le_mul_of_nonneg_right hc.le (by positivity)
    simpa using this
  -- the window sum splits
  set F : ℕ → ℝ := fun p ↦ if p.Prime then Real.log p / p else 0 with hF
  have hsumF : ∀ S : Finset ℕ, ∑ p ∈ S.filter Nat.Prime, Real.log p / p = ∑ p ∈ S, F p :=
    fun S ↦ by rw [hF, Finset.sum_filter]
  have hgF : ∀ N : ℕ, g N = ∑ p ∈ Finset.Ioc 0 N, F p := by
    intro N
    simp only [hg]
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from rfl, hsumF]
  have hsplit : ∀ X : ℕ, ∑ p ∈ (Finset.Ioc X ⌊c * X⌋₊).filter Nat.Prime, Real.log p / p
      = g ⌊c * X⌋₊ - g X := by
    intro X
    have hcons := Finset.sum_Ioc_consecutive F (Nat.zero_le X) (hfl X)
    rw [hsumF, hgF, hgF]
    linarith [hcons]
  -- the floor tends to infinity
  have hflTop : Tendsto (fun X : ℕ ↦ ⌊c * X⌋₊) atTop atTop :=
    tendsto_atTop_mono hfl tendsto_id
  -- the ratio tends to `c`
  have hratio : Tendsto (fun X : ℕ ↦ ((⌊c * X⌋₊ : ℝ)) / X) atTop (𝓝 c) := by
    have hlb : ∀ᶠ X : ℕ in atTop, c - 1 / X ≤ ((⌊c * X⌋₊ : ℝ)) / X := by
      filter_upwards [eventually_ge_atTop 1] with X hX
      have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
      have h1 : c * X - 1 < (⌊c * X⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (c * (X : ℝ))
        linarith
      rw [le_div_iff₀ hX0]
      field_simp
      linarith
    have hub : ∀ᶠ X : ℕ in atTop, ((⌊c * X⌋₊ : ℝ)) / X ≤ c := by
      filter_upwards [eventually_ge_atTop 1] with X hX
      have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
      rw [div_le_iff₀ hX0]
      exact Nat.floor_le (by positivity)
    have hlim : Tendsto (fun X : ℕ ↦ c - 1 / (X : ℝ)) atTop (𝓝 c) := by
      have : Tendsto (fun X : ℕ ↦ (1 : ℝ) / X) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlb hub
  -- hence `log ⌊cX⌋ - log X → log c`
  have hlogdiff : Tendsto (fun X : ℕ ↦ Real.log (⌊c * X⌋₊ : ℝ) - Real.log X) atTop
      (𝓝 (Real.log c)) := by
    have hcomp : Tendsto (fun X : ℕ ↦ Real.log (((⌊c * X⌋₊ : ℝ)) / X)) atTop
        (𝓝 (Real.log c)) := (Real.continuousAt_log (by linarith)).tendsto.comp hratio
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have hfX : (0 : ℝ) < (⌊c * X⌋₊ : ℝ) := by
      have : X ≤ ⌊c * X⌋₊ := hfl X
      have : (1 : ℕ) ≤ ⌊c * X⌋₊ := le_trans hX this
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    rw [Real.log_div (ne_of_gt hfX) (ne_of_gt hX0)]
  have hEcomp : Tendsto (fun X : ℕ ↦ g ⌊c * X⌋₊ - Real.log (⌊c * X⌋₊ : ℝ)) atTop (𝓝 (-E)) :=
    hE.comp hflTop
  have hfinal := (hEcomp.sub hE).add hlogdiff
  rw [show -E - -E + Real.log c = Real.log c by ring] at hfinal
  refine hfinal.congr fun X ↦ ?_
  rw [hsplit X]
  ring

/-! ### The Newman kernel -/

/--
**The Newman kernel identity.**  On the circle `|z| = R` the kernel
`(1 + z^2/R^2)/z` is *real*, and equals `2\,\mathrm{Re}(z)/R^2`.

This one line is the whole miracle of Newman's proof.  On the right-hand arc the tail
`G(z) - g_T(z)` is `O(Ce^{-xT}/x)` with `x = \mathrm{Re}(z) > 0`, while the kernel times
`e^{zT}` has modulus `2xe^{xT}/R^2`; the `x` and the exponentials cancel exactly and the
product is `2C/R^2`, uniformly in `T`.  Without the factor `1 + z^2/R^2` the kernel would be
`1/R` and the estimate would fail.
-/
@[category API, AMS 30]
theorem kernel_eq {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    (1 + z ^ 2 / (R : ℂ) ^ 2) / z = 2 * (z.re : ℂ) / (R : ℂ) ^ 2 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hRne : ((R : ℂ)) ≠ 0 := by simpa using ne_of_gt hR
  have hR2 : ((R : ℂ)) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj]
    norm_cast
    rw [← hz, Complex.normSq_eq_norm_sq]
  have hadd : z + (starRingEnd ℂ) z = 2 * (z.re : ℂ) := by
    have h := Complex.add_conj z
    push_cast at h
    linear_combination h
  have hkey : ((R : ℂ)) ^ 2 + z ^ 2 = 2 * (z.re : ℂ) * z := by
    rw [hR2]; linear_combination z * hadd
  field_simp
  linear_combination hkey

/-- The modulus of the Newman kernel on `|z| = R` is `2|\mathrm{Re}\,z|/R^2`. -/
@[category API, AMS 30]
theorem norm_kernel {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    ‖(1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ = 2 * |z.re| / R ^ 2 := by
  rw [kernel_eq hR hz]
  rw [norm_div, norm_mul]
  simp [abs_of_pos hR]

/-! ### The Laplace tail on the right-hand arc -/

/-- `\int_T^\infty e^{-bt}\,dt = e^{-bT}/b` for `b > 0`. -/
@[category API, AMS 26]
theorem integral_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in Set.Ioi T, Real.exp (-b * t) = Real.exp (-b * T) / b := by
  have hderiv : ∀ x ∈ Set.Ioi T,
      HasDerivAt (fun t : ℝ ↦ -Real.exp (-b * t) / b) (Real.exp (-b * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul (-b)).exp).neg.div_const b
    simpa [mul_comm, mul_div_assoc, hb.ne'] using h
  have hcont : ContinuousWithinAt (fun t : ℝ ↦ -Real.exp (-b * t) / b) (Set.Ici T) T := by
    fun_prop
  have hlim : Filter.Tendsto (fun t : ℝ ↦ -Real.exp (-b * t) / b) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ ↦ Real.exp (-b * t)) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using (h1.neg.div_const b)
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (exp_neg_integrableOn_Ioi T hb) hlim
  rw [this]
  ring

/--
**The Laplace tail bound.**  If `|F| \le C` then for `\mathrm{Re}\,z = x > 0`
$$\Bigl\|\int_T^\infty F(t)e^{-zt}\,dt\Bigr\| \le \frac{Ce^{-xT}}{x}.$$

Paired with `Newman.norm_kernel` this is what makes the right-hand arc contribute `O(C/R)`.
-/
@[category API, AMS 30]
theorem norm_integral_Ioi_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ}
    (hz : 0 < z.re) (T : ℝ) :
    ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * T) / z.re := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hbound : ∀ t : ℝ, ‖(F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * Real.exp (-z.re * t))
      (Set.Ioi T) := (exp_neg_integrableOn_Ioi T hz).const_mul C
  calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Set.Ioi T, C * Real.exp (-z.re * t) :=
        MeasureTheory.norm_integral_le_of_norm_le hgint
          (Filter.Eventually.of_forall fun t ↦ hbound t)
    _ = C * Real.exp (-z.re * T) / z.re := by
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hz T]
        ring

/--
**The Newman balance.**  On the right-hand arc the tail and the kernel multiply to `2C/R^2`,
uniformly in `T`.  Integrating over the semicircle of length `\pi R` and dividing by `2\pi`
gives the `C/R` bound that drives the whole proof.
-/
@[category API, AMS 30]
theorem norm_tail_mul_kernel_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ} {R T : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hzre : 0 < z.re) :
    ‖(∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have htail := norm_integral_Ioi_le hFb hzre T
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_mul, norm_mul, hexp, norm_kernel hR hz, abs_of_pos hzre]
  have hprod : (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) = C / z.re := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  have hstep : ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
      Real.exp (z.re * T) ≤ C / z.re := by
    calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ * Real.exp (z.re * T)
        ≤ (C * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) :=
          mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
      _ = C / z.re := hprod
  have hfin : (C / z.re) * (2 * z.re / R ^ 2) = 2 * C / R ^ 2 := by
    field_simp
  calc ‖∫ t in Set.Ioi T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ * Real.exp (z.re * T) *
        (2 * z.re / R ^ 2)
      ≤ (C / z.re) * (2 * z.re / R ^ 2) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = 2 * C / R ^ 2 := hfin

/-! ### The truncated transform on the left-hand arc -/

/-- `\int_0^T e^{bt}\,dt = (e^{bT}-1)/b` for `b > 0`. -/
@[category API, AMS 26]
theorem integral_exp_mul_uIoc {b : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.exp (b * t) = (Real.exp (b * T) - 1) / b := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun t : ℝ ↦ Real.exp (b * t) / b) (Real.exp (b * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul b).exp).div_const b
    simpa [mul_comm, hb.ne'] using h
  have hint : IntervalIntegrable (fun x : ℝ ↦ Real.exp (b * x)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  ring

/--
**The truncated transform on the left.**  The entire function
`g_T(z) = \int_0^T F(t)e^{-zt}\,dt` satisfies, for `\mathrm{Re}\,z = x < 0`,
$$\|g_T(z)\| \le \frac{Ce^{-xT}}{-x}.$$

This is the mirror of `Newman.norm_integral_Ioi_le`, and it is why the left half of Newman's
contour contributes the same `O(C/R)`: `g_T` is entire, so its contour there may be deformed
to the left semicircle, where the very same balance applies.
-/
@[category API, AMS 30]
theorem norm_integral_Ioc_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ}
    (hz : z.re < 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ C * Real.exp (-z.re * T) / (-z.re) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  set b := -z.re with hb
  have hbpos : 0 < b := by simpa [hb] using hz
  have hbound : ∀ t : ℝ, ‖(F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ ≤ C * Real.exp (b * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = b * t := by simp [hb]
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hFb t) (Real.exp_pos _).le
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * Real.exp (b * t))
      (Set.Ioc (0 : ℝ) T) := by
    apply Continuous.integrableOn_Ioc
    fun_prop
  have hval : ∫ t in Set.Ioc (0 : ℝ) T, C * Real.exp (b * t)
      = C * ((Real.exp (b * T) - 1) / b) := by
    rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_const_mul,
      integral_exp_mul_uIoc hbpos T]
  calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, C * Real.exp (b * t) :=
        MeasureTheory.norm_integral_le_of_norm_le hgint
          (Filter.Eventually.of_forall fun t ↦ hbound t)
    _ = C * ((Real.exp (b * T) - 1) / b) := hval
    _ ≤ C * Real.exp (b * T) / b := by
        have h1 : C * ((Real.exp (b * T) - 1) / b) = (C * (Real.exp (b * T) - 1)) / b := by
          ring
        rw [h1, div_le_div_iff_of_pos_right hbpos]
        nlinarith [hC0]

/--
**The Newman balance on the left.**  Exactly the same `2C/R^2`, uniformly in `T`.

Together with `Newman.norm_tail_mul_kernel_le` this bounds both semicircles of the contour by
`C/R` after integration, which is the whole quantitative content of
`Newman.tendsto_integral_of_analyticOn`; what is left is the Cauchy bookkeeping and the
dominated-convergence step for the analytic continuation on `\mathrm{Re}\,z \le 0`.
-/
@[category API, AMS 30]
theorem norm_trunc_mul_kernel_le {F : ℝ → ℝ} {C : ℝ} (hFb : ∀ t, |F t| ≤ C) {z : ℂ} {R T : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hzre : z.re < 0) (hT : 0 ≤ T) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))) *
        Complex.exp (z * (T : ℂ)) * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)‖
      ≤ 2 * C / R ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFb 0)
  have hbpos : 0 < -z.re := by linarith
  have htr := norm_integral_Ioc_le hFb hzre hT
  have hexp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [norm_mul, norm_mul, hexp, norm_kernel hR hz, abs_of_neg hzre]
  have hprod : (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) = C / (-z.re) := by
    rw [show -z.re * T = -(z.re * T) by ring, Real.exp_neg]
    field_simp
  have hstep : ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
      Real.exp (z.re * T) ≤ C / (-z.re) := by
    calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
          Real.exp (z.re * T)
        ≤ (C * Real.exp (-z.re * T) / (-z.re)) * Real.exp (z.re * T) :=
          mul_le_mul_of_nonneg_right htr (Real.exp_pos _).le
      _ = C / (-z.re) := hprod
  have hzne : z.re ≠ 0 := ne_of_lt hzre
  have hfin : (C / (-z.re)) * (2 * -z.re / R ^ 2) = 2 * C / R ^ 2 := by
    field_simp
  calc ‖∫ t in Set.Ioc (0 : ℝ) T, (F t : ℂ) * Complex.exp (-z * (t : ℂ))‖ *
        Real.exp (z.re * T) * (2 * -z.re / R ^ 2)
      ≤ (C / (-z.re)) * (2 * -z.re / R ^ 2) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = 2 * C / R ^ 2 := hfin

/-! ### The Cauchy value of the Newman kernel -/

open Metric in
/--
**The Cauchy step of Newman's proof.**  For `h` analytic on the closed disc `|z| \le R`,
$$\frac{1}{2\pi i}\oint_{|z| = R} h(z)\frac{1 + z^2/R^2}{z}\,dz = h(0).$$

The extra factor `1 + z^2/R^2` is `1` at the origin, so it does not change the residue; its
whole purpose is the boundary identity `Newman.kernel_eq`, which makes the kernel `O(1/R^2)`
times `|\mathrm{Re}\,z|` on the circle.  This is the piece of
`Newman.tendsto_integral_of_analyticOn` that mathlib's Cauchy integral formula supplies
directly; what is still missing there is only the *indented* contour needed because the
Laplace transform `G` is analytic on `\mathrm{Re}\,z \ge 0` and not on the full disc.
-/
@[category API, AMS 30]
theorem two_pi_I_inv_circleIntegral_kernel {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (closedBall (0 : ℂ) R)) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ z in C((0 : ℂ), R), h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z)) = h 0 := by
  have hRne : ((R : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hR
  set f : ℂ → ℂ := fun z ↦ h z * (1 + z ^ 2 / (R : ℂ) ^ 2) with hf
  have hpoly : Differentiable ℂ fun z : ℂ ↦ 1 + z ^ 2 / (R : ℂ) ^ 2 := by fun_prop
  have hfd : DifferentiableOn ℂ f (closedBall (0 : ℂ) R) := hd.mul hpoly.differentiableOn
  have hw : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have hcauchy := hfd.circleIntegral_sub_inv_smul hw
  have hrw : (∮ z in C((0 : ℂ), R), (z - 0)⁻¹ • f z)
      = ∮ z in C((0 : ℂ), R), h z * ((1 + z ^ 2 / (R : ℂ) ^ 2) / z) := by
    refine circleIntegral.integral_congr hR.le fun z _ ↦ ?_
    simp only [hf, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hrw] at hcauchy
  have hf0 : f 0 = h 0 := by
    simp [hf]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [hcauchy, smul_eq_mul, hf0, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Newman
