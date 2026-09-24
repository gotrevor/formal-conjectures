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

/-- The real part of `n^{-y-it}` for `n ≠ 0`:
$$\mathrm{Re}\,n^{-y-it} = n^{-y}\cos(t\log n).$$ -/
@[category API, AMS 11]
theorem re_natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (y t : ℝ) :
    ((n : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))).re = (n : ℝ) ^ (-y) * Real.cos (t * Real.log n) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hne : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  set L := Real.log (n : ℝ) with hL
  have hcast : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
  have hlog : Complex.log ((n : ℕ) : ℂ) = (L : ℂ) := by
    rw [hcast, hL, Complex.ofReal_log hpos.le]
  have hcpow : ((n : ℕ) : ℂ) ^ (-((y : ℂ) + (t : ℂ) * I))
      = Complex.exp (((-(L * y) : ℝ) : ℂ) + ((-(L * t) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog]
    push_cast
    ring_nf
  have hexp : (n : ℝ) ^ (-y) = Real.exp (-(L * y)) := by
    rw [Real.rpow_def_of_pos hpos, hL]; ring_nf
  rw [hcpow]
  simp only [Complex.exp_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one, zero_add, add_zero]
  rw [← hexp, show -(L * t) = -(t * L) by ring, Real.cos_neg, hL]

/-- `LFunctionTrivChar 1 = riemannZeta`: the trivial character mod `1` has `ζ` as its
`L`-function. -/
@[category API, AMS 11]
theorem lFunctionTrivChar_one_eq : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

/--
**The pole of `-ζ'/ζ` is simple, and the rest is continuous up to the `1`-line.**
There is a `G` continuous on `\{re s ≥ 1\}` with
$$\sum_n \frac{\Lambda(n)}{n^s} = \frac{1}{s-1} + G(s) \qquad (re\,s > 1).$$

This is the packaging of mathlib's
`DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁` at level `1`, and it is
where `riemannZeta_ne_zero_of_one_le_re` enters: `G` is continuous exactly away from the zeros
of `ζ`, and there are none with `re s ≥ 1`.
-/
@[category API, AMS 11]
theorem exists_continuousOn_lSeries_vonMangoldt_sub :
    ∃ G : ℂ → ℂ, ContinuousOn G {s : ℂ | 1 ≤ s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s = 1 / (s - 1) + G s := by
  refine ⟨fun s ↦ -deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s /
    DirichletCharacter.LFunctionTrivChar₁ 1 s, ?_, ?_⟩
  · refine (DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono fun s hs ↦ ?_
    exact Or.inr (by rw [lFunctionTrivChar_one_eq]; exact riemannZeta_ne_zero_of_one_le_re hs)
  · intro s hs
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    have hval : DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
        lFunctionTrivChar_one_eq]
    have hderiv : deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
        = (s - 1) * deriv riemannZeta s + riemannZeta s := by
      rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1,
        lFunctionTrivChar_one_eq]
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    simp only [hderiv, hval]
    field_simp
    ring

/--
**The untwisted von Mangoldt sum is at most its polar main term.**  For `0 < x ≤ 1`,
$$\sum_n \frac{\Lambda(n)}{n^{1+x}} \le \frac{1}{x} + C.$$

The companion upper bound to `Wirsing.exists_tsum_vonMangoldt_twisted_ge`; it is what turns a
Mertens lower bound for the head `n \le N` into an upper bound for the tail `n > N`.
-/
@[category API, AMS 11]
theorem exists_tsum_vonMangoldt_le :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) ≤ 1 / x + C := by
  obtain ⟨G, hGc, hGeq⟩ := exists_continuousOn_lSeries_vonMangoldt_sub
  have hc : IsCompact ((fun u : ℝ ↦ ((1 + u : ℝ) : ℂ)) '' Set.Icc 0 1) :=
    isCompact_Icc.image (by fun_prop)
  have hsub : (fun u : ℝ ↦ ((1 + u : ℝ) : ℂ)) '' Set.Icc 0 1 ⊆ {s : ℂ | 1 ≤ s.re} := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith [hu.1]
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (hGc.mono hsub)
  refine ⟨M, fun x hx hx1 ↦ ?_⟩
  set F : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hF
  set s : ℂ := ((1 + x : ℝ) : ℂ) with hs
  have hsgt : 1 < s.re := by simp only [hs, Complex.ofReal_re]; linarith
  have hterm : ∀ n : ℕ, (LSeries.term F s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hrw : F n / (n : ℂ) ^ s = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(((1 + x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)) := by
        simp only [hF, hs, Complex.ofReal_zero, zero_mul, add_zero, Complex.cpow_neg,
          div_eq_mul_inv]
      rw [hrw, Complex.re_ofReal_mul, re_natCast_cpow_neg hn]
      simp
  have h1 : Summable (LSeries.term F s) := ArithmeticFunction.LSeriesSummable_vonMangoldt hsgt
  have hLre : (LSeries F s).re = ∑' n : ℕ,
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) := by
    simp only [LSeries, Complex.re_tsum h1, hterm]
  rw [← hLre, hGeq _ hsgt, Complex.add_re]
  have hpole : (1 / (s - 1)).re = 1 / x := by
    have hs1 : s - 1 = ((x : ℝ) : ℂ) := by simp [hs]
    rw [hs1]; simp
  have hGb : (G s).re ≤ M := by
    have h2 := Complex.abs_re_le_norm (G s)
    have h3 : ‖G s‖ ≤ M := hM _ ⟨x, ⟨hx.le, hx1⟩, rfl⟩
    linarith [le_abs_self (G s).re]
  rw [hpole]; linarith

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
      1 / x - C ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        (1 - Real.cos (t * Real.log n)) := by
  obtain ⟨G, hGc, hGeq⟩ := exists_continuousOn_lSeries_vonMangoldt_sub
  -- `G` is bounded on each of the two compact segments `{1 + x + iτ : 0 ≤ x ≤ 1}`.
  have hbound : ∀ τ : ℝ, ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖G (((1 + x : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M := by
    intro τ
    have hc : IsCompact ((fun u : ℝ ↦ ((1 + u : ℝ) : ℂ) + (τ : ℂ) * I) '' Set.Icc 0 1) :=
      isCompact_Icc.image (by fun_prop)
    have hsub : (fun u : ℝ ↦ ((1 + u : ℝ) : ℂ) + (τ : ℂ) * I) '' Set.Icc 0 1 ⊆
        {s : ℂ | 1 ≤ s.re} := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hu.1]
    obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (hGc.mono hsub)
    exact ⟨M, fun x hx ↦ hM _ ⟨x, hx, rfl⟩⟩
  obtain ⟨M₀, hM₀⟩ := hbound 0
  obtain ⟨M₁, hM₁⟩ := hbound t
  refine ⟨1 / (2 * |t|) + M₀ + M₁, fun x hx hx1 ↦ ?_⟩
  have htabs : 0 < |t| := abs_pos.2 ht
  set F : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hF
  set s : ℝ → ℂ := fun τ ↦ ((1 + x : ℝ) : ℂ) + (τ : ℂ) * I with hs
  have hsre : ∀ τ : ℝ, (s τ).re = 1 + x := by
    intro τ
    simp [hs, Complex.add_re, Complex.mul_re]
  have hsgt : ∀ τ : ℝ, 1 < (s τ).re := fun τ ↦ by rw [hsre]; linarith
  -- The real part of the `n`-th term of the `L`-series.
  have hterm : ∀ (τ : ℝ) (n : ℕ), (LSeries.term F (s τ) n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        Real.cos (τ * Real.log n) := by
    intro τ n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have : F n / (n : ℂ) ^ (s τ) = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(((1 + x : ℝ) : ℂ) + (τ : ℂ) * I)) := by
        rw [Complex.cpow_neg, hF, hs]
        ring
      rw [this, Complex.re_ofReal_mul, re_natCast_cpow_neg hn]
      ring
  have hsummable : ∀ τ : ℝ, Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) * Real.cos (τ * Real.log n)) := by
    intro τ
    have h1 : Summable (LSeries.term F (s τ)) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (hsgt τ)
    simpa only [hterm τ] using (Complex.hasSum_re h1.hasSum).summable
  have hLre : ∀ τ : ℝ, (LSeries F (s τ)).re = ∑' n : ℕ,
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) * Real.cos (τ * Real.log n) := by
    intro τ
    have h1 : Summable (LSeries.term F (s τ)) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (hsgt τ)
    simp only [LSeries, Complex.re_tsum h1, hterm τ]
  -- Split the target sum into the two `L`-series.
  have hsplit : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        (1 - Real.cos (t * Real.log n))
      = (LSeries F (s 0)).re - (LSeries F (s t)).re := by
    rw [hLre, hLre, ← (hsummable 0).tsum_sub (hsummable t)]
    refine tsum_congr fun n ↦ ?_
    simp only [zero_mul, Real.cos_zero, mul_one]
    ring
  -- Evaluate both `L`-series through the pole.
  have hx0 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.le, hx1⟩
  have hval : ∀ τ : ℝ, (LSeries F (s τ)).re = (1 / (s τ - 1)).re + (G (s τ)).re := by
    intro τ
    rw [hGeq _ (hsgt τ), Complex.add_re]
  have hpole0 : (1 / (s 0 - 1)).re = 1 / x := by
    have : s 0 - 1 = ((x : ℝ) : ℂ) := by simp [hs]
    rw [this]
    simp
  have hpolet : (1 / (s t - 1)).re = x / (x ^ 2 + t ^ 2) := by
    have h1 : s t - 1 = ((x : ℝ) : ℂ) + (t : ℂ) * I := by simp [hs]; ring
    rw [h1, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    ring_nf
  have hpolele : x / (x ^ 2 + t ^ 2) ≤ 1 / (2 * |t|) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - |t|), sq_abs t]
  have hG0 : -M₀ ≤ (G (s 0)).re := by
    have := hM₀ x hx0
    have h2 := Complex.abs_re_le_norm (G (((1 + x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I))
    have : |(G (s 0)).re| ≤ M₀ := le_trans (by simpa [hs] using h2) (by simpa [hs] using hM₀ x hx0)
    linarith [neg_abs_le (G (s 0)).re]
  have hGt : (G (s t)).re ≤ M₁ := by
    have h2 := Complex.abs_re_le_norm (G (((1 + x : ℝ) : ℂ) + (t : ℂ) * I))
    have : |(G (s t)).re| ≤ M₁ := le_trans (by simpa [hs] using h2) (by simpa [hs] using hM₁ x hx0)
    linarith [le_abs_self (G (s t)).re]
  rw [hsplit, hval, hval, hpole0, hpolet]
  linarith

/-- Splitting a sum over `Ioc a c` at an intermediate point `b`. -/
@[category API, AMS 11]
theorem sum_Ioc_add_sum_Ioc {f : ℕ → ℝ} {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    ∑ n ∈ Ioc a b, f n + ∑ n ∈ Ioc b c, f n = ∑ n ∈ Ioc a c, f n := by
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
    Finset.Ioc_union_Ioc_eq_Ioc h₁ h₂]

/-- A monotone family of cut points decomposes `Ioc (k 0) (k m)` into `m` consecutive blocks. -/
@[category API, AMS 11]
theorem sum_range_sum_Ioc {f : ℕ → ℝ} {k : ℕ → ℕ} (hk : Monotone k) (m : ℕ) :
    ∑ i ∈ range m, ∑ n ∈ Ioc (k i) (k (i + 1)), f n = ∑ n ∈ Ioc (k 0) (k m), f n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, sum_Ioc_add_sum_Ioc (hk (Nat.zero_le m)) (hk m.le_succ)]

/--
**Mertens' first theorem in geometric blocks.**  With `x = c/\log N`, the head
`\sum_{n \le N}\Lambda(n)n^{-1-x}` is bounded below by the Riemann sum of `e^{-cu}` on `[0,1]`
with `m` blocks:
$$\sum_{n \le N}\frac{\Lambda(n)}{n^{1+x}}
  \ \ge\ \Bigl(\frac{\log N}{m} - 2B\Bigr)\sum_{i<m} e^{-c(i+1)/m},
  \qquad B = \log 4 + 4.$$

The `i`-th block is `N^{i/m} < n \le N^{(i+1)/m}`, on which `n^{-x} \ge e^{-c(i+1)/m}` and, by
`Mertens.abs_sum_vonMangoldt_div_sub_log_le`, `\sum \Lambda(n)/n \ge \log N/m - 2B`.
-/
@[category API, AMS 11]
theorem sum_vonMangoldt_rpow_head_ge {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hL : 0 < Real.log N) :
    (Real.log N / m - 2 * (Real.log 4 + 4)) *
        ∑ i ∈ range m, Real.exp (-(c * (i + 1) / m))
      ≤ ∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + c / Real.log N)) := by
  set L := Real.log N with hLdef
  set x := c / L with hxdef
  have hx : 0 < x := div_pos hc hL
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hLne : L ≠ 0 := ne_of_gt hL
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  set B := Real.log 4 + 4 with hB
  set k : ℕ → ℕ := fun i ↦ ⌊(N : ℝ) ^ ((i : ℝ) / m)⌋₊ with hk
  have hu1 : ∀ i : ℕ, (1 : ℝ) ≤ (N : ℝ) ^ ((i : ℝ) / m) := fun i ↦
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hulog : ∀ i : ℕ, Real.log ((N : ℝ) ^ ((i : ℝ) / m)) = (i : ℝ) / m * L :=
    fun i ↦ Real.log_rpow hNR _
  have hkmono : Monotone k := by
    intro i j hij
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      (by gcongr))
  have hk0 : k 0 = 1 := by simp [hk]
  have hkm : k m = N := by
    simp only [hk]
    rw [div_self (by positivity), Real.rpow_one, Nat.floor_natCast]
  -- The Mertens partial sums at the cut points.
  have hA : ∀ i : ℕ, |(∑ d ∈ Ioc 0 (k i), (ArithmeticFunction.vonMangoldt d : ℝ) / d)
      - (i : ℝ) / m * L| ≤ B := by
    intro i
    have := Mertens.abs_sum_vonMangoldt_div_sub_log_le (x := (N : ℝ) ^ ((i : ℝ) / m)) (hu1 i)
    rwa [hulog i] at this
  -- Block lower bound.
  have hblock : ∀ i ∈ range m, (L / m - 2 * B) * Real.exp (-(c * (i + 1) / m))
      ≤ ∑ n ∈ Ioc (k i) (k (i + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) := by
    intro i _
    have hmert : L / m - 2 * B ≤ ∑ n ∈ Ioc (k i) (k (i + 1)),
        (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
      have hsplit := sum_Ioc_add_sum_Ioc (f := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℝ) / n)
        (Nat.zero_le (k i)) (hkmono i.le_succ)
      have h1 := abs_le.1 (hA i)
      have h2 := abs_le.1 (hA (i + 1))
      push_cast at h2 ⊢
      have : ((i : ℝ) + 1) / m * L - (i : ℝ) / m * L = L / m := by field_simp; ring
      linarith [hsplit]
    have hexp : ∀ n ∈ Ioc (k i) (k (i + 1)),
        (ArithmeticFunction.vonMangoldt n : ℝ) / n * Real.exp (-(c * (i + 1) / m))
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
      have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn1
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hnle : (n : ℝ) ≤ (N : ℝ) ^ (((i : ℝ) + 1) / m) := by
        have h1 : (n : ℝ) ≤ ((k (i + 1) : ℕ) : ℝ) := by exact_mod_cast hn2
        have h2 : ((k (i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((((i + 1 : ℕ)) : ℝ) / m) :=
          Nat.floor_le (le_trans zero_le_one (hu1 (i + 1)))
        push_cast at h2
        linarith
      have hlogn : Real.log n ≤ ((i : ℝ) + 1) / m * L := by
        have h3 := Real.log_le_log hnR hnle
        rw [Real.log_rpow hNR] at h3
        linarith
      have hpow : Real.exp (-(c * ((i : ℝ) + 1) / m)) ≤ (n : ℝ) ^ (-x) := by
        rw [Real.rpow_def_of_pos hnR]
        refine Real.exp_le_exp.2 ?_
        have h4 : x * Real.log n ≤ x * (((i : ℝ) + 1) / m * L) := by nlinarith [hx.le]
        have h5 : x * (((i : ℝ) + 1) / m * L) = c * ((i : ℝ) + 1) / m := by
          rw [hxdef]; field_simp
        linarith
      have hsplit : (n : ℝ) ^ (-(1 + x)) = (n : ℝ)⁻¹ * (n : ℝ) ^ (-x) := by
        rw [show -(1 + x) = -1 + -x by ring, Real.rpow_add hnR, Real.rpow_neg_one]
      have hnn : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      rw [hsplit]
      calc (ArithmeticFunction.vonMangoldt n : ℝ) / n * Real.exp (-(c * ((i : ℝ) + 1) / m))
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n * (n : ℝ) ^ (-x) := by
            gcongr
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ)⁻¹ * (n : ℝ) ^ (-x)) := by
            rw [div_eq_mul_inv, mul_assoc]
    calc (L / m - 2 * B) * Real.exp (-(c * (i + 1) / m))
        ≤ (∑ n ∈ Ioc (k i) (k (i + 1)), (ArithmeticFunction.vonMangoldt n : ℝ) / n) *
            Real.exp (-(c * (i + 1) / m)) := by
          gcongr
      _ = ∑ n ∈ Ioc (k i) (k (i + 1)),
            (ArithmeticFunction.vonMangoldt n : ℝ) / n * Real.exp (-(c * (i + 1) / m)) := by
          rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum hexp
  calc (L / m - 2 * B) * ∑ i ∈ range m, Real.exp (-(c * (i + 1) / m))
      = ∑ i ∈ range m, (L / m - 2 * B) * Real.exp (-(c * (i + 1) / m)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ range m, ∑ n ∈ Ioc (k i) (k (i + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) :=
        Finset.sum_le_sum hblock
    _ = ∑ n ∈ Ioc (k 0) (k m),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) :=
        sum_range_sum_Ioc hkmono m
    _ ≤ ∑ n ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) := by
        rw [hk0, hkm]
        refine Finset.sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          obtain ⟨ha, hb⟩ := Finset.mem_Ioc.1 hn
          exact Finset.mem_Ioc.2 ⟨by omega, hb⟩) ?_
        intro n hn _
        have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        positivity

/--
**A Riemann-sum lower bound for a geometric sum.**  For `c > 0` and `m ≥ 1`,
$$\sum_{i<m} e^{-c(i+1)/m} \ \ge\ \frac{m}{c}\,e^{-c/m}\,(1 - e^{-c}),$$
which tends to the integral `(1 - e^{-c})/c` as `m \to \infty`.
-/
@[category API, AMS 11]
theorem sum_range_exp_ge {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) :
    (m : ℝ) / c * Real.exp (-(c / m)) * (1 - Real.exp (-c))
      ≤ ∑ i ∈ range m, Real.exp (-(c * (i + 1) / m)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set q := Real.exp (-(c / m)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq]
    refine Real.exp_lt_one_iff.2 ?_
    have : 0 < c / (m : ℝ) := by positivity
    linarith
  have hqm : q ^ m = Real.exp (-c) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hterm : ∀ i ∈ range m, Real.exp (-(c * ((i : ℝ) + 1) / m)) = q ^ (i + 1) := by
    intro i _
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have h1q : 1 - q ≤ c / m := by
    have := Real.add_one_le_exp (-(c / m))
    rw [← hq] at this
    linarith
  have h1qpos : 0 < 1 - q := by linarith
  have hgeom : ∑ i ∈ range m, q ^ (i + 1) = q * (1 - q ^ m) / (1 - q) := by
    have hne : q ≠ 1 := ne_of_lt hq1
    have : ∑ i ∈ range m, q ^ (i + 1) = q * ∑ i ∈ range m, q ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, geom_sum_eq hne]
    field_simp
    ring
  have hnum : 0 ≤ q * (1 - q ^ m) := by
    have : q ^ m ≤ 1 := pow_le_one₀ hq0.le hq1.le
    nlinarith
  calc (m : ℝ) / c * q * (1 - Real.exp (-c))
      = q * (1 - q ^ m) / (c / m) := by rw [hqm]; field_simp
    _ ≤ q * (1 - q ^ m) / (1 - q) := by gcongr
    _ = ∑ i ∈ range m, q ^ (i + 1) := hgeom.symm
    _ = ∑ i ∈ range m, Real.exp (-(c * ((i : ℝ) + 1) / m)) :=
        (Finset.sum_congr rfl hterm).symm

/-- Summability of the twisted von Mangoldt series on `re s = 1 + x`, `x > 0`. -/
@[category API, AMS 11]
theorem summable_vonMangoldt_rpow_cos {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) *
      Real.cos (τ * Real.log n)) := by
  set F : ℕ → ℂ := fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hF
  set s : ℂ := ((1 + x : ℝ) : ℂ) + (τ : ℂ) * I with hs
  have hsgt : 1 < s.re := by
    simp only [hs, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hterm : ∀ n : ℕ, (LSeries.term F s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + x)) *
        Real.cos (τ * Real.log n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hrw : F n / (n : ℂ) ^ s = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(((1 + x : ℝ) : ℂ) + (τ : ℂ) * I)) := by
        simp only [hF, hs, Complex.cpow_neg, div_eq_mul_inv]
      rw [hrw, Complex.re_ofReal_mul, re_natCast_cpow_neg hn]
      ring
  have h1 : Summable (LSeries.term F s) := ArithmeticFunction.LSeriesSummable_vonMangoldt hsgt
  simpa only [hterm] using (Complex.hasSum_re h1.hasSum).summable

/-- Summability of the untwisted von Mangoldt series on `re s = 1 + x`, `x > 0`. -/
@[category API, AMS 11]
theorem summable_vonMangoldt_rpow {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x))) := by
  simpa using summable_vonMangoldt_rpow_cos hx 0

/-- The numeric instance of `Wirsing.sum_range_exp_ge` used below: `m = 32`, `c = 2`. -/
@[category API, AMS 11]
theorem sum_range_exp_ge_32 :
    (90 / 7 : ℝ) ≤ ∑ i ∈ range 32, Real.exp (-(2 * ((i : ℝ) + 1) / 32)) := by
  have h := sum_range_exp_ge (m := 32) (by norm_num) (c := (2 : ℝ)) (by norm_num)
  have he1 : (15 / 16 : ℝ) ≤ Real.exp (-(2 / ((32 : ℕ) : ℝ))) := by
    have h0 := Real.add_one_le_exp (-(2 / ((32 : ℕ) : ℝ)))
    norm_num at h0 ⊢
    linarith
  have he2 : Real.exp (-2 : ℝ) ≤ 1 / 7 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 : (7 : ℝ) ≤ Real.exp 2 := by nlinarith [Real.exp_pos (1 : ℝ)]
    have h4 : Real.exp (-2 : ℝ) * Real.exp (2 : ℝ) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-2 : ℝ)]
  have hcast : ((32 : ℕ) : ℝ) / 2 = 16 := by norm_num
  rw [hcast] at h
  refine le_trans ?_ h
  nlinarith [Real.exp_pos (-(2 / ((32 : ℕ) : ℝ))), Real.exp_pos (-2 : ℝ), he1, he2]

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
  obtain ⟨C₁, hC₁⟩ := exists_tsum_vonMangoldt_twisted_ge ht
  obtain ⟨C₂, hC₂⟩ := exists_tsum_vonMangoldt_le
  set B := Real.log 4 + 4 with hB
  have hB4 : 4 ≤ B := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨|C₁| + 2 * |C₂| + (360 / 7) * B + 8 + 16 * B, fun N hN ↦ ?_⟩
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set L := Real.log N with hLdef
  have hLnn : 0 ≤ L := Real.log_nonneg hNR
  have hSnn : 0 ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * (1 - Real.cos (t * Real.log p)) := by
    refine Finset.sum_nonneg fun p hp ↦ ?_
    obtain ⟨_, hpp⟩ := Finset.mem_filter.1 hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlp : 0 ≤ Real.log p / p := by
      have : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      positivity
    nlinarith [Real.cos_le_one (t * Real.log p)]
  have habs1 : 0 ≤ |C₁| := abs_nonneg C₁
  have habs2 : 0 ≤ |C₂| := abs_nonneg C₂
  rcases lt_or_ge L (64 * B) with hsmall | hlarge
  · linarith
  have hLpos : 0 < L := by linarith
  set x := 2 / L with hxdef
  have hx : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hLpos]; linarith
  have hinv : 1 / x = L / 2 := by rw [hxdef]; field_simp
  set g : ℕ → ℝ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) *
    (1 - Real.cos (t * Real.log n)) with hg
  set Gf : ℕ → ℝ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x))
    with hGf
  have hGsum : Summable Gf := summable_vonMangoldt_rpow hx
  have hgsum : Summable g := by
    refine (hGsum.sub (summable_vonMangoldt_rpow_cos hx t)).congr fun n ↦ ?_
    simp only [hg, hGf]; ring
  have hgnn : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + x)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h3 := Real.cos_le_one (t * Real.log n)
    simp only [hg]
    have : 0 ≤ 1 - Real.cos (t * Real.log n) := by linarith
    positivity
  have hgle : ∀ n : ℕ, g n ≤ 2 * Gf n := by
    intro n
    have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + x)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h3 := Real.neg_one_le_cos (t * Real.log n)
    simp only [hg, hGf]
    nlinarith [mul_nonneg h1 h2]
  -- Head/tail split of both series at `N`.
  set s0 : Finset ℕ := Ioc 0 N with hs0
  have hsplitg := hgsum.sum_add_tsum_compl (s := s0)
  have hsplitG := hGsum.sum_add_tsum_compl (s := s0)
  set S : Set ℕ := ((s0 : Set ℕ))ᶜ with hSdef
  have htailg : ∑' i : S, g i ≤ 2 * ∑' i : S, Gf i := by
    have h1 : Summable (fun i : S ↦ g i) := hgsum.subtype _
    have h2 : Summable (fun i : S ↦ Gf i) := hGsum.subtype _
    calc ∑' i : S, g i ≤ ∑' i : S, (2 * Gf i) :=
          h1.tsum_le_tsum (fun i ↦ hgle i) (h2.mul_left 2)
      _ = 2 * ∑' i : S, Gf i := tsum_mul_left
  have hT : 1 / x - C₁ ≤ ∑' n : ℕ, g n := hC₁ x hx hx1
  have hTt : ∑' n : ℕ, Gf n ≤ 1 / x + C₂ := hC₂ x hx hx1
  -- Mertens in geometric blocks bounds the head of the untwisted series.
  have hheadG : (L / 32 - 2 * B) * (90 / 7) ≤ ∑ n ∈ s0, Gf n := by
    have h := sum_vonMangoldt_rpow_head_ge (m := 32) (by norm_num) (c := (2 : ℝ))
      (by norm_num) hN hLpos
    have hcast : ((32 : ℕ) : ℝ) = 32 := by norm_num
    rw [hcast] at h
    refine le_trans ?_ h
    have hnn : 0 ≤ L / 32 - 2 * B := by linarith
    exact mul_le_mul_of_nonneg_left sum_range_exp_ge_32 hnn
  -- Collect: the head of the twisted series.
  have hheadg : L / 2 - |C₁| - 2 * ((L / 2 + |C₂|) - (L / 32 - 2 * B) * (90 / 7))
      ≤ ∑ n ∈ s0, g n := by
    rw [hinv] at hT hTt
    have h1 : C₁ ≤ |C₁| := le_abs_self C₁
    have h2 : C₂ ≤ |C₂| := le_abs_self C₂
    linarith
  -- Drop the proper prime powers and compare the prime part.
  have hIoc : s0 = Icc 1 N := by
    rw [hs0]; ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hle_div : ∀ n : ℕ, 1 ≤ n → g n ≤ 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
    intro n hn1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hpow : (n : ℝ) ^ (-(1 + x)) ≤ (n : ℝ)⁻¹ := by
      rw [show ((n : ℝ)⁻¹) = (n : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]]
      exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + x)) := Real.rpow_nonneg (by linarith) _
    have h3 := Real.neg_one_le_cos (t * Real.log n)
    have h4 := Real.cos_le_one (t * Real.log n)
    simp only [hg]
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg h1 h2, mul_le_mul_of_nonneg_left hpow h1]
  have hnonprime : ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ n.Prime), g n ≤ 8 := by
    calc ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ n.Prime), g n
        ≤ ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ n.Prime),
            2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
          refine Finset.sum_le_sum fun n hn ↦ hle_div n ?_
          exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
      _ = 2 * ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ n.Prime),
            (ArithmeticFunction.vonMangoldt n : ℝ) / n := by rw [Finset.mul_sum]
      _ ≤ 2 * 4 := by
          have := Mertens.sum_vonMangoldt_div_nonprime_le N
          linarith
      _ = 8 := by norm_num
  have hprime : ∑ n ∈ (Icc 1 N).filter Nat.Prime, g n
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          Real.log p / p * (1 - Real.cos (t * Real.log p)) := by
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlam : (ArithmeticFunction.vonMangoldt p : ℝ) = Real.log p :=
      ArithmeticFunction.vonMangoldt_apply_prime hpp
    have hpow : (p : ℝ) ^ (-(1 + x)) ≤ (p : ℝ)⁻¹ := by
      rw [show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have h3 := Real.cos_le_one (t * Real.log p)
    have hrn : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + x)) :=
      Real.rpow_nonneg (show (0 : ℝ) ≤ (p : ℝ) by linarith) _
    simp only [hg, hlam]
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hlogp hrn, mul_le_mul_of_nonneg_left hpow hlogp]
  have hsplitfilter : ∑ n ∈ Icc 1 N, g n
      = ∑ n ∈ (Icc 1 N).filter Nat.Prime, g n
        + ∑ n ∈ (Icc 1 N).filter (fun n ↦ ¬ n.Prime), g n :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hIoc] at hheadg
  rw [hsplitfilter] at hheadg
  linarith

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
