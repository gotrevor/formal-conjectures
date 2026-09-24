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
public import FormalConjectures.ErdosProblems.Wirsing.Laplace

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
`\sum_m (ψ(m) - m)/(m(m+1))` has convergent partial sums, with limit `S`, then
$$\sum_{n \le N}\frac{\Lambda(n)}{n} = \log N - E + o(1),
  \qquad E = -\gamma - \sum_m \frac{ψ(m) - m}{m(m+1)} .$$

Both hypotheses come from `Newman.tendsto_integral_of_analyticOn`; the convergence is the
*direct* output of the analytic theorem and does not wait on `ψ(x) \sim x`.  Everything else
here is `Newman.sum_div_eq_abel` plus mathlib's
`Real.tendsto_harmonic_sub_log`.
-/
@[category API, AMS 11]
theorem exists_tendsto_sum_vonMangoldt_div_sub_log
    (hpsi : Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N) atTop (𝓝 1))
    {S : ℝ} (hsum : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N,
      (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1))) atTop (𝓝 S)) :
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
  have htail : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, g m) atTop (𝓝 S) := hsum
  have hharm := Real.tendsto_harmonic_sub_log
  refine ⟨-(Real.eulerMascheroniConstant + S), ?_⟩
  have hlim : Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N + ((harmonic N : ℝ) - Real.log N) - 1
      + ∑ m ∈ Finset.range N, g m) atTop
      (𝓝 (1 + Real.eulerMascheroniConstant - 1 + S)) :=
    ((hpsi.add hharm).sub_const 1).add htail
  rw [show -(-(Real.eulerMascheroniConstant + S))
      = 1 + Real.eulerMascheroniConstant - 1 + S by ring]
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

/-! ### The Laplace transform of `ψ(e^t)e^{-t} - 1` -/

/--
**The polar part of `-\zeta'/\zeta` is simple, and the rest is ANALYTIC up to the `1`-line.**
The analytic strengthening of `Wirsing.exists_continuousOn_lSeries_vonMangoldt_sub`, which
gives only continuity.  Newman's theorem needs analyticity on a neighbourhood of the closed
half plane, so the continuous version is not enough.

`\Lambda_1(s) = (s-1)\zeta(s)` is entire and has no zero with `\mathrm{Re}\,s \ge 1`: away
from `s = 1` because `\zeta` has none there
(`riemannZeta_ne_zero_of_one_le_re`), and at `s = 1` because the pole of `\zeta` is simple
(`DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero`).  Hence its logarithmic
derivative is analytic there.
-/
@[category API, AMS 11]
theorem exists_analyticOnNhd_lSeries_vonMangoldt_sub :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ {s : ℂ | 1 ≤ s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s = 1 / (s - 1) + Φ s := by
  set L : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1 with hL
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hLa : ∀ s : ℂ, AnalyticAt ℂ L s := fun s ↦ hLd.analyticAt s
  have hLda : ∀ s : ℂ, AnalyticAt ℂ (deriv L) s := fun s ↦ (hLa s).deriv
  have hLne : ∀ s : ℂ, 1 ≤ s.re → L s ≠ 0 := by
    intro s hs
    rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
    · have hval : L s = (s - 1) * riemannZeta s := by
        rw [hL, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
          Wirsing.lFunctionTrivChar_one_eq]
      rw [hval]
      exact mul_ne_zero (sub_ne_zero_of_ne hs1) (riemannZeta_ne_zero_of_one_le_re hs)
  refine ⟨fun s ↦ -deriv L s / L s, ?_, ?_⟩
  · intro s hs
    exact ((hLda s).neg).div (hLa s) (hLne s hs)
  · intro s hs
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    have hval : L s = (s - 1) * riemannZeta s := by
      rw [hL, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
        Wirsing.lFunctionTrivChar_one_eq]
    have hderiv : deriv L s = (s - 1) * deriv riemannZeta s + riemannZeta s := by
      rw [hL, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1,
        Wirsing.lFunctionTrivChar_one_eq]
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    simp only [hderiv, hval]
    field_simp
    ring

/-- `(0,\infty) \cap [a,\infty)` and `(a,\infty)` differ by at most two points. -/
@[category API, AMS 28]
theorem ioi_inter_ici_ae {a : ℝ} (ha : 0 ≤ a) :
    ((Set.Ioi (0 : ℝ) ∩ Set.Ici a : Set ℝ)) =ᵐ[MeasureTheory.volume] Set.Ioi a := by
  rcases eq_or_lt_of_le ha with rfl | h
  · rw [show (Set.Ioi (0 : ℝ) ∩ Set.Ici (0 : ℝ) : Set ℝ) = Set.Ioi 0 from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici, and_iff_left_iff_imp]
      exact le_of_lt]
    exact Filter.EventuallyEq.rfl
  · have hset : (Set.Ioi (0 : ℝ) ∩ Set.Ici a : Set ℝ) = Set.Ici a := by
      refine Set.inter_eq_right.2 fun t ht ↦ ?_
      exact lt_of_lt_of_le h ht
    rw [hset]
    exact MeasureTheory.Ioi_ae_eq_Ici.symm

/-- The Laplace integral of one term of `ψ`: `\int_0^\infty 1_{[a,\infty)}e^{-wt}\,dt
  = e^{-wa}/w`. -/
@[category API, AMS 30]
theorem integral_indicator_cexp {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator (Set.Ici a) (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ))) t)
      = Complex.exp (-w * (a : ℂ)) / w := by
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae ha),
    Newman.integral_cexp_neg_mul_Ioi hw]

/-- The same with the integrand replaced by its norm. -/
@[category API, AMS 30]
theorem integral_indicator_norm_cexp {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Set.Ioi (0 : ℝ),
        ‖Set.indicator (Set.Ici a) (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ))) t‖)
      = Real.exp (-w.re * a) / w.re := by
  have hnorm : ∀ t : ℝ,
      ‖Set.indicator (Set.Ici a) (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ))) t‖
        = Set.indicator (Set.Ici a) (fun t : ℝ ↦ Real.exp (-w.re * t)) t := by
    intro t
    by_cases ht : t ∈ Set.Ici a
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Complex.norm_exp]
      congr 1
      simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, norm_zero]
  simp only [hnorm]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae ha),
    Newman.integral_exp_neg_mul_Ioi hw]

/--
**The Laplace transform of `ψ(e^t)`.**  For `\mathrm{Re}\,w > 1`,
$$\int_0^\infty \psi(e^t)e^{-wt}\,dt = \frac1w\sum_n \frac{\Lambda(n)}{n^w} .$$

Write `\psi(e^t) = \sum_n \Lambda(n)1_{\log n \le t}` and integrate term by term; the `n`-th
term contributes `\Lambda(n)n^{-w}/w`.  The interchange is legitimate because
`\sum_n \Lambda(n)n^{-\mathrm{Re}\,w} < \infty`.
-/
@[category API, AMS 11 30]
theorem integral_psi_exp_eq {w : ℂ} (hw : 1 < w.re) :
    (∫ t in Set.Ioi (0 : ℝ), (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-w * (t : ℂ)))
      = LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) w / w := by
  have hw0 : 0 < w.re := by linarith
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hw0; simp at hw0
  set f : ℕ → ℝ → ℂ := fun n t ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
    Set.indicator (Set.Ici (Real.log n)) (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ))) t with hf
  have hlog0 : ∀ n : ℕ, 0 ≤ Real.log n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  have hE : MeasureTheory.IntegrableOn (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
    have := Newman.integrableOn_laplace (F := fun _ : ℝ ↦ (1 : ℝ)) (C := 1)
      (fun t ↦ by norm_num) (MeasureTheory.locallyIntegrable_const 1) hw0 (a := (0 : ℝ))
    simpa using this
  have hfint : ∀ n : ℕ, MeasureTheory.IntegrableOn (f n) (Set.Ioi (0 : ℝ)) := by
    intro n
    exact ((hE.indicator measurableSet_Ici).const_mul _)
  -- the value and the norm of each term
  have hval : ∀ n : ℕ, 1 ≤ n →
      (∫ t in Set.Ioi (0 : ℝ), f n t)
        = (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℂ) ^ (-w)) / w := by
    intro n hn
    rw [hf]
    simp only
    rw [MeasureTheory.integral_const_mul, integral_indicator_cexp hw0 (hlog0 n)]
    have hcpow : ((n : ℂ)) ^ (-w) = Complex.exp (-w * ((Real.log n : ℝ) : ℂ)) := by
      have hne : ((n : ℂ)) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      rw [Complex.cpow_def_of_ne_zero hne]
      congr 1
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_log (by positivity)]
      ring
    rw [hcpow]
    ring
  have hnormval : ∀ n : ℕ,
      (∫ t in Set.Ioi (0 : ℝ), ‖f n t‖)
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-w.re) / w.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf]
    have hnorm : ∀ t : ℝ, ‖f n t‖ = (ArithmeticFunction.vonMangoldt n : ℝ) *
        ‖Set.indicator (Set.Ici (Real.log n)) (fun t : ℝ ↦ Complex.exp (-w * (t : ℂ))) t‖ := by
      intro t
      rw [hf]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simp only [hnorm]
    rw [MeasureTheory.integral_const_mul, integral_indicator_norm_cexp hw0 (hlog0 n)]
    have hrpow : (n : ℝ) ^ (-w.re) = Real.exp (-w.re * Real.log n) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      ring_nf
    rw [hrpow]
    ring
  -- summability of the norms
  have hsum : Summable fun n : ℕ ↦ ∫ t in Set.Ioi (0 : ℝ), ‖f n t‖ := by
    have hbase : Summable fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 + (w.re - 1))) := Wirsing.summable_vonMangoldt_rpow (by linarith)
    have hbase' : Summable fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-w.re) / w.re := by
      have : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + (w.re - 1)))
          = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-w.re) := by
        intro n; ring_nf
      exact ((hbase.congr this).div_const w.re)
    exact hbase'.congr fun n ↦ (hnormval n).symm
  -- the pointwise sum
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∑' n : ℕ, f n t) = (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-w * (t : ℂ)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    set N : ℕ := ⌊Real.exp t⌋₊ with hN
    have hzero : ∀ n : ℕ, n ∉ Finset.range (N + 1) → f n t = 0 := by
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have hn1 : 1 ≤ n := by
        have : 1 ≤ N + 1 := by omega
        omega
      have hlt : Real.exp t < n := by
        have : N + 1 ≤ n := hn
        have hfl : Real.exp t < (N : ℝ) + 1 := Nat.lt_floor_add_one _
        have : ((N : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      have hnot : t ∉ Set.Ici (Real.log n) := by
        simp only [Set.mem_Ici, not_le]
        have hpos : (0 : ℝ) < n := by positivity
        have := Real.log_lt_log (Real.exp_pos t) hlt
        rwa [Real.log_exp] at this
      rw [hf]
      simp only
      rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [tsum_eq_sum hzero]
    have hterm : ∀ n ∈ Finset.range (N + 1),
        f n t = (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-w * (t : ℂ)) := by
      intro n hn
      simp only [Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · simp [hf]
      · have hle : (n : ℝ) ≤ Real.exp t := by
          have h1 : n ≤ N := by omega
          have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
          exact le_trans this (Nat.floor_le (Real.exp_pos t).le)
        have hmem : t ∈ Set.Ici (Real.log n) := by
          simp only [Set.mem_Ici]
          have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
          have := Real.log_le_log hpos hle
          rwa [Real.log_exp] at this
        rw [hf]
        simp only
        rw [Set.indicator_of_mem hmem]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    rw [Chebyshev.psi_eq_sum_Icc, ← hN]
    have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]; omega
    rw [hIcc]
    push_cast
    ring
  -- assemble
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) hfint hsum
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint] at hswap
  rw [← hswap]
  rw [LSeries, ← tsum_div_const]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf, LSeries.term]
  · rw [hval n hn, LSeries.term_of_ne_zero (by omega)]
    rw [Complex.cpow_neg]
    field_simp

/-! ### The integral of `F` as a partial sum -/

/--
`ψ` is constant on `[m, m+1)`, so the Laplace integrand integrates to
`\psi(m)/(m(m+1))` over `[\log m, \log(m+1)]`.
-/
@[category API, AMS 11]
theorem integral_psi_step {m : ℕ} (hm : 1 ≤ m) :
    (∫ t in Real.log m..Real.log ((m : ℝ) + 1),
        Chebyshev.psi (Real.exp t) * Real.exp (-t))
      = Chebyshev.psi m / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hlog : Real.log m ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log hm0 (by linarith)
  -- on the open interval the integrand is `ψ(m)e^{-t}`
  have hcongr : ∫ t in Real.log m..Real.log ((m : ℝ) + 1),
      Chebyshev.psi (Real.exp t) * Real.exp (-t)
      = ∫ t in Real.log m..Real.log ((m : ℝ) + 1), Chebyshev.psi m * Real.exp (-t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2
      (MeasureTheory.measure_singleton (Real.log ((m : ℝ) + 1)))] with t ht hmem
    have htne : t ≠ Real.log ((m : ℝ) + 1) := ht
    rw [Set.uIoc_of_le hlog] at hmem
    have ht1 : Real.log m < t := hmem.1
    have ht2 : t < Real.log ((m : ℝ) + 1) := lt_of_le_of_ne hmem.2 htne
    have he1 : (m : ℝ) < Real.exp t := by
      have := Real.exp_lt_exp.2 ht1
      rwa [Real.exp_log hm0] at this
    have he2 : Real.exp t < (m : ℝ) + 1 := by
      have := Real.exp_lt_exp.2 ht2
      rwa [Real.exp_log hm1] at this
    have hfloor : ⌊Real.exp t⌋₊ = m := by
      rw [Nat.floor_eq_iff (by positivity)]
      exact ⟨le_of_lt he1, he2⟩
    rw [Chebyshev.psi_eq_psi_coe_floor (Real.exp t), hfloor]
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hexp : ∫ t in Real.log m..Real.log ((m : ℝ) + 1), Real.exp (-t)
      = Real.exp (-Real.log m) - Real.exp (-Real.log ((m : ℝ) + 1)) := by
    have hderiv : ∀ t ∈ Set.uIcc (Real.log m) (Real.log ((m : ℝ) + 1)),
        HasDerivAt (fun u : ℝ ↦ -Real.exp (-u)) (Real.exp (-t)) t := by
      intro t _
      have h1 : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-t)) t := by
        simpa using ((hasDerivAt_id t).neg).exp
      have h2 := h1.neg
      rwa [neg_neg] at h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    ring
  rw [hexp, Real.exp_neg, Real.exp_neg, Real.exp_log hm0, Real.exp_log hm1]
  field_simp
  ring

/-- `\sum_{k < N} 1/(k+2) = H_{N+1} - 1`. -/
@[category API, AMS 11]
theorem sum_one_div_add_two (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 2) = (harmonic (N + 1) : ℝ) - 1 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h := harmonic_succ (n + 1)
    rw [Finset.sum_range_succ, ih, h]
    push_cast
    ring

/--
**The Newman integral is the Newman partial sum.**  For every `N`,
$$\int_0^{\log(N+1)}\bigl(\psi(e^t)e^{-t} - 1\bigr)\,dt
  = \sum_{m \le N}\frac{\psi(m)-m}{m(m+1)} + H_{N+1} - 1 - \log(N+1).$$

Summing `Newman.integral_psi_step` over the blocks `[\log m, \log(m+1)]`.  The harmonic
correction is the difference between the arithmetic weight `1/(m+1)` of the main term `m` and
the analytic weight `\log(m+1) - \log m`.
-/
@[category API, AMS 11]
theorem integral_newman_eq (N : ℕ) :
    (∫ t in (0 : ℝ)..Real.log ((N : ℝ) + 1),
        (Chebyshev.psi (Real.exp t) * Real.exp (-t) - 1))
      = (∑ m ∈ Finset.range (N + 1), (Chebyshev.psi m - m) / ((m : ℝ) * ((m : ℝ) + 1)))
        + ((harmonic (N + 1) : ℝ) - 1 - Real.log ((N : ℝ) + 1)) := by
  have hmono : Monotone (fun t : ℝ ↦ Chebyshev.psi (Real.exp t)) := fun a b hab ↦
    Chebyshev.psi_mono (Real.exp_le_exp.2 hab)
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun t : ℝ ↦ Chebyshev.psi (Real.exp t) * Real.exp (-t)) MeasureTheory.volume a b :=
    fun a b ↦ (hmono.intervalIntegrable).mul_continuousOn (by fun_prop)
  -- the blocks
  set a : ℕ → ℝ := fun k ↦ Real.log ((k : ℝ) + 1) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a N = Real.log ((N : ℝ) + 1) := rfl
  have hblocks := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ ↦ Chebyshev.psi (Real.exp t) * Real.exp (-t))
    (μ := MeasureTheory.volume) (a := a) (n := N) (fun k _ ↦ hint _ _)
  rw [ha0, haN] at hblocks
  have hterm : ∀ k ∈ Finset.range N,
      (∫ t in a k..a (k + 1), Chebyshev.psi (Real.exp t) * Real.exp (-t))
        = Chebyshev.psi (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    intro k _
    have h := integral_psi_step (m := k + 1) (by omega)
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring] at h
    simp only [ha]
    rw [show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 1 + 1 by push_cast; ring, h]
    ring_nf
  rw [Finset.sum_congr rfl hterm] at hblocks
  -- split off the constant
  rw [intervalIntegral.integral_sub (hint _ _)
    (intervalIntegrable_const), intervalIntegral.integral_const, ← hblocks]
  -- the discrete side
  have hsum : (∑ m ∈ Finset.range (N + 1), (Chebyshev.psi m - m) / ((m : ℝ) * ((m : ℝ) + 1)))
      = (∑ k ∈ Finset.range N, Chebyshev.psi (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
        - ((harmonic (N + 1) : ℝ) - 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, Chebyshev.psi_zero]
    rw [← sum_one_div_add_two N, ← Finset.sum_sub_distrib]
    have : ∀ k ∈ Finset.range N,
        (Chebyshev.psi (k + 1) - ((k : ℝ) + 1)) / (((k : ℝ) + 1) * (((k : ℝ) + 1) + 1))
          = Chebyshev.psi (k + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1 / ((k : ℝ) + 2) := by
      intro k _
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      field_simp
      ring
    rw [show ((0 : ℝ) - 0) / (0 * (0 + 1)) = 0 by norm_num, add_zero]
    push_cast
    exact Finset.sum_congr rfl this
  rw [hsum]
  simp only [smul_eq_mul, mul_one, sub_zero]
  ring

/--
**Newman's convergent integral, in discrete form.**  The partial sums of the error series of
Chebyshev's `ψ` against the main term converge:
$$\sum_{m < N}\frac{\psi(m) - m}{m(m+1)} \longrightarrow L .$$

This is the *direct* output of `Newman.tendsto_integral_of_analyticOn` applied to
`F(t) = \psi(e^t)e^{-t} - 1` — the analytic theorem proves the convergence of
`\int_0^\infty F`, which is this series up to the change of variable `t = \log m` — and it
comes **before** `\psi(x) \sim x`, which is deduced from it by the monotonicity of `ψ`.

The conclusion is the convergence of the *ordered* partial sums, not `Summable`.  The two are
not the same here: `Summable` over `ℕ` in `ℝ` is unconditional, hence absolute, convergence,
and `\sum_m |\psi(m) - m|/(m(m+1)) < \infty` is a statement about the size of the error term
in the prime number theorem that no contour argument gives (it is not known
unconditionally).  Newman's theorem gives exactly the improper integral, i.e. the limit of the
ordered partial sums, and that is all the endgame
`Newman.tendsto_chebyshevPsi_nat_div_atTop_one` consumes.
-/
@[category API, AMS 11]
theorem exists_tendsto_sum_psiErr :
    ∃ L : ℝ, Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N,
      (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1))) atTop (𝓝 L) := by
  sorry

/-! ### The Prime Number Theorem from the convergent series -/

/--
**The upper resonance bound.**  If `ψ(n) \ge (1+ε)n` then the Newman series has a block of
consecutive terms just above `n` of total mass at least `ε^2/24`.

For `n \le m \le n + εn/2` monotonicity of `ψ` gives `ψ(m) - m \ge (1+ε)n - (n + εn/2) = εn/2`,
while `m(m+1) \le 6n^2`; there are more than `εn/2` such `m`.  The block mass does not depend
on `n`, so only finitely many `n` can satisfy the hypothesis.
-/
@[category API, AMS 11]
theorem sum_Ico_psiErr_ge {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (h : (1 + ε) * n ≤ Chebyshev.psi n) :
    ε ^ 2 / 24 ≤ ∑ m ∈ Finset.Ico n (n + ⌊ε * n / 2⌋₊ + 1),
      (Chebyshev.psi m - m) / (m * (m + 1)) := by
  set k : ℕ := ⌊ε * n / 2⌋₊ with hk
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hkle : (k : ℝ) ≤ ε * n / 2 := Nat.floor_le (by positivity)
  have hklt : ε * n / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hterm : ∀ m ∈ Finset.Ico n (n + k + 1),
      ε / (12 * n) ≤ (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1)) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    have hmR1 : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmR2 : (m : ℝ) ≤ (n : ℝ) + k := by
      have : m ≤ n + k := by omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn0 hmR1
    have hpsi : Chebyshev.psi n ≤ Chebyshev.psi m := Chebyshev.psi_mono hmR1
    have hnum : ε * n / 2 ≤ Chebyshev.psi m - m := by
      have : (m : ℝ) ≤ (n : ℝ) + ε * n / 2 := by linarith
      linarith
    have hden : (m : ℝ) * (m + 1) ≤ 6 * n ^ 2 := by
      have h1 : (m : ℝ) ≤ 2 * n := by nlinarith
      have h2 : (m : ℝ) + 1 ≤ 3 * n := by nlinarith
      nlinarith
    have hden0 : (0 : ℝ) < (m : ℝ) * (m + 1) := by positivity
    have hnum0 : (0 : ℝ) ≤ Chebyshev.psi m - m := le_trans (by positivity) hnum
    rw [div_le_div_iff₀ (by positivity) hden0]
    nlinarith [mul_le_mul_of_nonneg_left hden hε0.le,
      mul_le_mul_of_nonneg_right hnum (by positivity : (0:ℝ) ≤ 12 * (n : ℝ))]
  have hcard : (Finset.Ico n (n + k + 1)).card = k + 1 := by
    rw [Nat.card_Ico]; omega
  have hsum := Finset.card_nsmul_le_sum (Finset.Ico n (n + k + 1))
    (fun m ↦ (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1))) (ε / (12 * n)) hterm
  rw [hcard, nsmul_eq_mul] at hsum
  refine le_trans ?_ hsum
  have hpos : (0 : ℝ) < ε / (12 * n) := by positivity
  push_cast
  have key : ε ^ 2 / 24 = (ε * n / 2) * (ε / (12 * n)) := by
    field_simp; ring
  rw [key]
  exact mul_le_mul_of_nonneg_right hklt.le hpos.le

/--
**The lower resonance bound.**  If `ψ(n) \le (1-ε)n` then the block of terms just below `n`
has total mass at most `-ε^2/8`.  Mirror of `Newman.sum_Ico_psiErr_ge`.
-/
@[category API, AMS 11]
theorem sum_Ico_psiErr_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    (h : Chebyshev.psi n ≤ (1 - ε) * n) :
    ∑ m ∈ Finset.Ico (n - ⌊ε * n / 2⌋₊) (n + 1),
      (Chebyshev.psi m - m) / (m * (m + 1)) ≤ -(ε ^ 2 / 8) := by
  set k : ℕ := ⌊ε * n / 2⌋₊ with hk
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkle : (k : ℝ) ≤ ε * n / 2 := Nat.floor_le (by positivity)
  have hklt : ε * n / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkn : 2 * k ≤ n := by
    have : (2 : ℝ) * k ≤ n := by nlinarith
    exact_mod_cast this
  have hsubR : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    have : k ≤ n := by omega
    push_cast [this]
    ring
  have hterm : ∀ m ∈ Finset.Ico (n - k) (n + 1),
      (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1)) ≤ -(ε / (4 * n)) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.1 hm
    have hmn : m ≤ n := by omega
    have hmR2 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hmR1 : (n : ℝ) - k ≤ (m : ℝ) := by
      rw [← hsubR]; exact_mod_cast hm1
    have hm1' : 1 ≤ m := by omega
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1'
    have hpsi : Chebyshev.psi m ≤ Chebyshev.psi n := Chebyshev.psi_mono hmR2
    have hnum : Chebyshev.psi m - m ≤ -(ε * n / 2) := by
      have : (n : ℝ) - ε * n / 2 ≤ (m : ℝ) := by linarith
      linarith
    have hden : (m : ℝ) * (m + 1) ≤ 2 * n ^ 2 := by nlinarith
    have hden0 : (0 : ℝ) < (m : ℝ) * (m + 1) := by positivity
    rw [div_le_iff₀ hden0]
    have hkey : (ε / (4 * n)) * ((m : ℝ) * (m + 1)) ≤ ε * n / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (n : ℝ))]
      nlinarith
    have hneg : -(ε / (4 * n)) * ((m : ℝ) * (m + 1))
        = -((ε / (4 * n)) * ((m : ℝ) * (m + 1))) := by ring
    rw [hneg]
    linarith
  have hcard : (Finset.Ico (n - k) (n + 1)).card = k + 1 := by
    rw [Nat.card_Ico]; omega
  have hsum := Finset.sum_le_card_nsmul (Finset.Ico (n - k) (n + 1))
    (fun m ↦ (Chebyshev.psi m - m) / ((m : ℝ) * (m + 1))) (-(ε / (4 * n))) hterm
  rw [hcard, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  have hpos : (0 : ℝ) < ε / (4 * n) := by positivity
  push_cast
  have key : -(ε ^ 2 / 8) = (ε * n / 2) * (-(ε / (4 * n))) := by
    field_simp; ring
  rw [key]
  exact mul_le_mul_of_nonpos_right hklt.le (by linarith)

/--
**The Prime Number Theorem along the integers.**  `ψ(N)/N \to 1`.

This is Zagier's endgame: the convergence of the Newman series
(`Newman.summable_psi_sub_div`) makes its blocks of consecutive terms arbitrarily light,
while `Newman.sum_Ico_psiErr_ge` and `Newman.sum_Ico_psiErr_le` show that a single `n` with
`|ψ(n)/n - 1| \ge ε` forces a nearby block of mass `\ge ε^2/24`.  Only the monotonicity of
`ψ` is used besides the convergence — no further analysis.
-/
@[category API, AMS 11]
theorem tendsto_chebyshevPsi_nat_div_atTop_one :
    Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N) atTop (𝓝 1) := by
  classical
  set g : ℕ → ℝ := fun m ↦ (Chebyshev.psi m - m) / (m * (m + 1)) with hg
  obtain ⟨L, hS⟩ : ∃ L : ℝ, Tendsto (fun K ↦ ∑ m ∈ Finset.range K, g m) atTop (𝓝 L) :=
    exists_tendsto_sum_psiErr
  -- the Cauchy criterion for blocks
  have hcauchy : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n K : ℕ, N₀ ≤ n → n ≤ K →
      |∑ m ∈ Finset.Ico n K, g m| < δ := by
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hS) (δ / 2) (by linarith)
    refine ⟨N₀, fun n K hn hnK ↦ ?_⟩
    have h1 := hN₀ n hn
    have h2 := hN₀ K (le_trans hn hnK)
    rw [Real.dist_eq] at h1 h2
    have hsplit : ∑ m ∈ Finset.range n, g m + ∑ m ∈ Finset.Ico n K, g m
        = ∑ m ∈ Finset.range K, g m := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive g (Nat.zero_le n) hnK]
    have hrw : ∑ m ∈ Finset.Ico n K, g m
        = (∑ m ∈ Finset.range K, g m - L) - (∑ m ∈ Finset.range n, g m - L) := by linarith
    obtain ⟨h1a, h1b⟩ := abs_lt.1 h1
    obtain ⟨h2a, h2b⟩ := abs_lt.1 h2
    rw [hrw, abs_lt]
    constructor <;> linarith
  -- the conclusion
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨N₀, hN₀⟩ := hcauchy (e ^ 2 / 24) (by positivity)
  refine ⟨max (2 * N₀ + 2) 2, fun n hn ↦ ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : 2 * N₀ + 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by positivity
  rw [Real.dist_eq]
  have hnotup : ¬ ((1 + e) * n ≤ Chebyshev.psi n) := by
    intro hup
    have hge := sum_Ico_psiErr_ge he0 he1 (by omega : 1 ≤ n) hup
    have hlt := hN₀ n (n + ⌊e * n / 2⌋₊ + 1) (by omega) (by omega)
    rw [hg] at hlt
    have := (abs_lt.1 hlt).2
    linarith
  have hnotdown : ¬ (Chebyshev.psi n ≤ (1 - e) * n) := by
    intro hdown
    set k : ℕ := ⌊e * n / 2⌋₊ with hk
    have hkle : (k : ℝ) ≤ e * n / 2 := Nat.floor_le (by positivity)
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hkn : 2 * k ≤ n := by
      have : (2 : ℝ) * k ≤ n := by nlinarith
      exact_mod_cast this
    have hN₀le : N₀ ≤ n - k := by omega
    have hle := sum_Ico_psiErr_le he0 he1 hn2 hdown
    have hlt := hN₀ (n - k) (n + 1) hN₀le (by omega)
    rw [hg] at hlt
    have := (abs_lt.1 hlt).1
    have hpos : (0 : ℝ) < e ^ 2 := by positivity
    linarith
  have hup : Chebyshev.psi n < (1 + e) * n := lt_of_not_ge hnotup
  have hdown : (1 - e) * n < Chebyshev.psi n := lt_of_not_ge hnotdown
  have hrw : Chebyshev.psi n / n - 1 = (Chebyshev.psi n - n) / n := by
    field_simp
  refine lt_of_lt_of_le ?_ heε
  rw [hrw, abs_lt]
  constructor
  · rw [lt_div_iff₀ hn0]; nlinarith
  · rw [div_lt_iff₀ hn0]; nlinarith

/--
**The Prime Number Theorem**, Chebyshev form: `ψ(x) \sim x`.

Immediate from `Newman.tendsto_chebyshevPsi_nat_div_atTop_one`, since `ψ` is constant on
`[\lfloor x\rfloor, x)` and `\lfloor x\rfloor / x \to 1`.
-/
@[category research solved, AMS 11]
theorem tendsto_chebyshevPsi_div_atTop_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ ↦ Chebyshev.psi (⌊x⌋₊ : ℕ) / ((⌊x⌋₊ : ℕ) : ℝ)) atTop (𝓝 1) :=
    tendsto_chebyshevPsi_nat_div_atTop_one.comp tendsto_nat_floor_atTop
  have h2 : Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ : ℝ)) / x) atTop (𝓝 1) := by
    have hlb : ∀ᶠ x : ℝ in atTop, 1 - 1 / x ≤ ((⌊x⌋₊ : ℝ)) / x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h := Nat.lt_floor_add_one x
      rw [le_div_iff₀ hx]
      field_simp
      linarith
    have hub : ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊ : ℝ)) / x ≤ 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_le_one hx]
      exact Nat.floor_le hx.le
    have hlim : Tendsto (fun x : ℝ ↦ 1 - 1 / x) atTop (𝓝 1) := by
      have h : Tendsto (fun x : ℝ ↦ (1 : ℝ) / x) atTop (𝓝 0) := by
        simpa [one_div] using tendsto_inv_atTop_zero
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlb hub
  have hmul := h1.mul h2
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hfl : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.2 hx
  have hfl0 : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfl
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  field_simp

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
  obtain ⟨S, hS⟩ := exists_tendsto_sum_psiErr
  obtain ⟨E, hE⟩ := exists_tendsto_sum_vonMangoldt_div_sub_log
    tendsto_chebyshevPsi_nat_div_atTop_one hS
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

end Newman
