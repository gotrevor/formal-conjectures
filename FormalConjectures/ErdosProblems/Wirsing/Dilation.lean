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
public import FormalConjectures.ErdosProblems.Wirsing.BddLog
public import FormalConjectures.ErdosProblems.Wirsing.Contract
public import FormalConjectures.ErdosProblems.Wirsing.Sharp

/-!
# The functional relation satisfied by the dilation difference

Fix `a ≥ 1` and set `D(N) = \text{mean } g\ N - \text{mean } g\ \lfloor N/a\rfloor`.
`Wirsing.DilationInvariant` asserts `D(N) \to 0`.

Subtracting the log-weighted functional relation
`\sigma(N)\log N = \sum_{p\le N}\frac{\log p}{p}g(p)\sigma(\lfloor N/p\rfloor) + O(1)` at `N` and
at `\lfloor N/a\rfloor` gives the **same relation for `D` itself**:
$$D(N)\log N = \sum_{p \le N/a}\frac{\log p}{p}g(p) D(\lfloor N/p\rfloor)
  + O\big(1 + \log N - \log\lfloor N/a\rfloor\big),$$
`Wirsing.abs_dilationDiff_mul_log_sub_sum_le`.  The two floors match exactly:
`\lfloor\lfloor N/a\rfloor/p\rfloor = \lfloor\lfloor N/p\rfloor/a\rfloor`, so the differences
that appear on the right are `D` at the smaller scales `\lfloor N/p\rfloor`.

The relation is homogeneous in `D`, and the weights `\log p/p` have total mass `\log N + O(1)`,
so it is exactly critical: it does not by itself force `D \to 0`.  It is the starting point of
Elliott's proof, where the gain comes from the primes in a short range.

*References:*
- [El79] Elliott, P.D.T.A., Probabilistic number theory II.
- [GHS19] Granville, A., Harper, A.J., Soundararajan, K., A new proof of Halász's theorem, and
  its consequences. Compositio Math. 155 (2019), 126-163.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-- The dilation difference `D(N) = \text{mean } g\ N - \text{mean } g\ \lfloor N/a\rfloor`. -/
noncomputable def dilationDiff (g : ℕ → ℝ) (a N : ℕ) : ℝ := mean g N - mean g (N / a)

/-- `\lfloor\lfloor N/a\rfloor/p\rfloor = \lfloor\lfloor N/p\rfloor/a\rfloor`. -/
@[category API, AMS 11]
theorem natDiv_div_comm (N a p : ℕ) : N / a / p = N / p / a := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/--
**The functional relation for the dilation difference.**  For `1 ≤ a ≤ N`,
$$\Big|D(N)\log N - \sum_{p \le N/a}\frac{\log p}{p}g(p)D(\lfloor N/p\rfloor)\Big|
  \le 2(9 + \log 4) + 2(\log 4 + 8) + 2\big(\log N - \log\lfloor N/a\rfloor\big).$$
The error is bounded uniformly in `N` once `a` is fixed, because
`\log N - \log\lfloor N/a\rfloor \to \log a`.
-/
@[category API, AMS 11]
theorem abs_dilationDiff_mul_log_sub_sum_le (g : ℕ → ℝ) (hg : IsBddMultiplicative g) {a N : ℕ}
    (ha : 1 ≤ a) (haN : a ≤ N) :
    |dilationDiff g a N * Real.log N
      - ∑ p ∈ (Icc 1 (N / a)).filter Nat.Prime,
          Real.log p / p * (g p * dilationDiff g a (N / p))|
      ≤ 2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8)
        + 2 * (Real.log N - Real.log ((N / a : ℕ) : ℝ)) := by
  classical
  set M := N / a with hM
  have hN1 : 1 ≤ N := le_trans ha haN
  have hM1 : 1 ≤ M := (Nat.one_le_div_iff (by omega)).2 haN
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hlogM : 0 ≤ Real.log ((M : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogMN : Real.log ((M : ℕ) : ℝ) ≤ Real.log N := log_natCast_mono hMN
  set PN := (Icc 1 N).filter Nat.Prime with hPN
  set PM := (Icc 1 M).filter Nat.Prime with hPM
  have hsub : PM ⊆ PN := by
    intro p hp
    simp only [hPM, hPN, mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hMN⟩, hp.2⟩
  have hR1 := bdd_abs_mean_mul_log_sub_sum_prime_le g hg hN1
  have hR2 := bdd_abs_mean_mul_log_sub_sum_prime_le g hg hM1
  -- the split of the prime sums
  have hsplit : ∑ p ∈ PN, Real.log p / p * (g p * mean g (N / p))
      = (∑ p ∈ PM, Real.log p / p * (g p * mean g (N / p)))
        + ∑ p ∈ PN \ PM, Real.log p / p * (g p * mean g (N / p)) := by
    rw [add_comm]
    exact (Finset.sum_sdiff hsub).symm
  have hcommon : (∑ p ∈ PM, Real.log p / p * (g p * mean g (N / p)))
      - ∑ p ∈ PM, Real.log p / p * (g p * mean g (M / p))
      = ∑ p ∈ PM, Real.log p / p * (g p * dilationDiff g a (N / p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [dilationDiff, hM, natDiv_div_comm]
    ring
  -- the identity
  have hid : dilationDiff g a N * Real.log N
      - ∑ p ∈ PM, Real.log p / p * (g p * dilationDiff g a (N / p))
      = (mean g N * Real.log N - ∑ p ∈ PN, Real.log p / p * (g p * mean g (N / p)))
        - (mean g M * Real.log ((M : ℕ) : ℝ)
            - ∑ p ∈ PM, Real.log p / p * (g p * mean g (M / p)))
        - mean g M * (Real.log N - Real.log ((M : ℕ) : ℝ))
        + ∑ p ∈ PN \ PM, Real.log p / p * (g p * mean g (N / p)) := by
    rw [dilationDiff, ← hcommon, hsplit]
    ring
  -- the new primes contribute at most the Mertens gap
  have hgap : |∑ p ∈ PN \ PM, Real.log p / p * (g p * mean g (N / p))|
      ≤ Real.log N - Real.log ((M : ℕ) : ℝ) + 2 * (Real.log 4 + 8) := by
    have hterm : ∀ p ∈ PN \ PM, |Real.log p / p * (g p * mean g (N / p))|
        ≤ Real.log p / p := by
      intro p hp
      have hpp : p.Prime := (mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hw : (0 : ℝ) ≤ Real.log p / p :=
        div_nonneg (Real.log_natCast_nonneg _) hpR.le
      rw [abs_mul, abs_of_nonneg hw, abs_mul]
      have h1 : |g p| * |mean g (N / p)| ≤ 1 :=
        mul_le_one₀ (hg.abs_le_one _ hpp.one_lt.le) (abs_nonneg _)
          (abs_mean_le_one_of_bdd hg _)
      calc Real.log p / p * (|g p| * |mean g (N / p)|) ≤ Real.log p / p * 1 :=
            mul_le_mul_of_nonneg_left h1 hw
        _ = Real.log p / p := mul_one _
    have hsum : ∑ p ∈ PN \ PM, Real.log p / p
        = (∑ p ∈ PN, Real.log p / p) - ∑ p ∈ PM, Real.log p / p :=
      Finset.sum_sdiff_eq_sub hsub
    have hm1 := Mertens.abs_sum_log_prime_div_sub_log_le hN1
    have hm2 := Mertens.abs_sum_log_prime_div_sub_log_le hM1
    rw [abs_le] at hm1 hm2
    calc |∑ p ∈ PN \ PM, Real.log p / p * (g p * mean g (N / p))|
        ≤ ∑ p ∈ PN \ PM, |Real.log p / p * (g p * mean g (N / p))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ PN \ PM, Real.log p / p := Finset.sum_le_sum hterm
      _ ≤ Real.log N - Real.log ((M : ℕ) : ℝ) + 2 * (Real.log 4 + 8) := by
          rw [hsum]
          simp only [hPN, hPM] at hm1 hm2 ⊢
          linarith [hm1.1, hm1.2, hm2.1, hm2.2]
  have hmeanM : |mean g M| ≤ 1 := abs_mean_le_one_of_bdd hg M
  have hdrift : |mean g M * (Real.log N - Real.log ((M : ℕ) : ℝ))|
      ≤ Real.log N - Real.log ((M : ℕ) : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log N - Real.log ((M : ℕ) : ℝ))]
    calc |mean g M| * (Real.log N - Real.log ((M : ℕ) : ℝ))
        ≤ 1 * (Real.log N - Real.log ((M : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hmeanM (by linarith)
      _ = Real.log N - Real.log ((M : ℕ) : ℝ) := one_mul _
  rw [hid]
  have hstep : ∀ x y z w : ℝ, |x - y - z + w| ≤ |x| + |y| + |z| + |w| := by
    intro x y z w
    calc |x - y - z + w| ≤ |x - y - z| + |w| := abs_add_le _ _
      _ ≤ (|x - y| + |z|) + |w| := by
          have := abs_sub (x - y) z
          linarith [abs_sub (x - y) z]
      _ ≤ ((|x| + |y|) + |z|) + |w| := by linarith [abs_sub x y]
      _ = |x| + |y| + |z| + |w| := by ring
  refine (hstep _ _ _ _).trans ?_
  linarith [hR1, hR2, hgap, hdrift]

/-- `\lfloor N/a\rfloor \to \infty` for fixed `a \ge 1`. -/
@[category API, AMS 11]
theorem tendsto_natDiv_atTop {a : ℕ} (ha : 1 ≤ a) :
    Tendsto (fun N : ℕ ↦ N / a) atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨b * a, fun n hn ↦ (Nat.le_div_iff_mul_le (by omega)).2 hn⟩

/--
**`DilationInvariant` only has to be proved for a prime dilation.**  Writing `a = pb`,
`D_a(N) = D_p(N) + D_b(\lfloor N/p\rfloor)`, and `\lfloor N/p\rfloor \to \infty`, so the
general case follows by strong induction on `a`.

Together with `Wirsing.eventually_abs_mean_le`, which only ever dilates by a power of the one
prime being removed, this cuts the remaining obligation down to: *for every real multiplicative
`g` with `|g| \le 1` and every prime `p`, `\text{mean } g\ N - \text{mean } g\ \lfloor N/p\rfloor
\to 0`.*
-/
@[category API, AMS 11]
theorem dilationInvariant_of_prime
    (h : ∀ g : ℕ → ℝ, IsBddMultiplicative g → ∀ p : ℕ, p.Prime →
      Tendsto (fun N : ℕ ↦ mean g N - mean g (N / p)) atTop (𝓝 0)) :
    DilationInvariant := by
  intro g hg a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    rcases eq_or_lt_of_le ha with h1 | h1
    · simp [← h1]
    · obtain ⟨p, hp, b, rfl⟩ : ∃ p, p.Prime ∧ ∃ b, a = p * b := by
        obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
        obtain ⟨b, hb⟩ := hpa
        exact ⟨p, hp, b, hb⟩
      have hb1 : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with rfl | hb; · simp at h1
        exact hb
      have hblt : b < p * b := by
        have := hp.two_le
        nlinarith
      have h1p := h g hg p hp
      have h2b := (ih b hblt hb1).comp (tendsto_natDiv_atTop (a := p) hp.pos)
      have hsum := h1p.add h2b
      rw [add_zero] at hsum
      refine hsum.congr fun N ↦ ?_
      simp only [Function.comp_apply, Nat.div_div_eq_div_mul]
      ring

/-- `|D(N)| ≤ 2`. -/
@[category API, AMS 11]
theorem abs_dilationDiff_le_two {g : ℕ → ℝ} (hg : IsBddMultiplicative g) (a N : ℕ) :
    |dilationDiff g a N| ≤ 2 := by
  refine (abs_sub _ _).trans ?_
  linarith [abs_mean_le_one_of_bdd hg N, abs_mean_le_one_of_bdd hg (N / a)]

/-- **The dilation difference is log-Lipschitz**: `|D(m) - D(m-1)| \le (2 + 4a)/m`. -/
@[category API, AMS 11]
theorem abs_dilationDiff_sub_le {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {a : ℕ} (ha : 1 ≤ a)
    {m : ℕ} (hm : 2 ≤ m) :
    |dilationDiff g a m - dilationDiff g a (m - 1)| ≤ (2 + 4 * (a : ℝ)) / m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  -- the first term
  have t1 : |mean g m - mean g (m - 1)| ≤ 2 / (m : ℝ) := by
    have h := bdd_abs_mean_sub_mean_le g hg (M := m - 1) (N := m) (by omega) (by omega)
    rw [hcast] at h
    calc |mean g m - mean g (m - 1)| ≤ 2 * ((m : ℝ) - ((m : ℝ) - 1)) / m := h
      _ = 2 / (m : ℝ) := by ring_nf
  -- the second term
  set M := m / a with hMdef
  set M' := (m - 1) / a with hM'def
  have hMM' : M' ≤ M := Nat.div_le_div_right (by omega)
  have hMM'1 : M ≤ M' + 1 := by
    have h1 : m ≤ (m - 1) + a := by omega
    calc M ≤ ((m - 1) + a) / a := Nat.div_le_div_right h1
      _ = (m - 1) / a + 1 := Nat.add_div_right _ (by omega)
  have t2 : |mean g M - mean g M'| ≤ 4 * (a : ℝ) / m := by
    rcases eq_or_lt_of_le hMM' with heq | hlt
    · rw [heq]; simp; positivity
    · have hM : M = M' + 1 := by omega
      rcases Nat.eq_zero_or_pos M' with hM'0 | hM'1
      · -- `M = 1`, so `m ≤ a`
        have hmle : m ≤ a := by
          have hlt : m - 1 < a := by
            by_contra hc
            simp only [not_lt] at hc
            have h1 : 1 ≤ (m - 1) / a := (Nat.one_le_div_iff (by omega)).2 hc
            rw [← hM'def] at h1
            omega
          omega
        have hmleR : (m : ℝ) ≤ (a : ℝ) := by exact_mod_cast hmle
        have hbig : (1 : ℝ) ≤ 4 * (a : ℝ) / m := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        rw [hM, hM'0]
        simp only [zero_add]
        have h1 : mean g 0 = 0 := by simp [mean]
        rw [h1, sub_zero]
        exact le_trans (abs_mean_le_one_of_bdd hg 1) hbig
      · have hMpos : 1 ≤ M := by omega
        have h := bdd_abs_mean_sub_mean_le g hg (M := M') (N := M) hM'1 hMM'
        have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        have hM'R : (M' : ℝ) = (M : ℝ) - 1 := by
          rw [hM]; push_cast; ring
        rw [hM'R] at h
        have hstep : 2 * ((M : ℝ) - ((M : ℝ) - 1)) / M = 2 / (M : ℝ) := by ring_nf
        rw [hstep] at h
        -- `m < a(M+1) ≤ 2aM`
        have hmlt : m < a * M + a := by
          have h1 := Nat.div_add_mod m a
          have h2 := Nat.mod_lt m (show 0 < a by omega)
          rw [hMdef]
          omega
        have hmltR : (m : ℝ) < (a : ℝ) * (M : ℝ) + (a : ℝ) := by exact_mod_cast hmlt
        have haR : (0 : ℝ) < (a : ℝ) := by
          have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
          linarith
        have hkey : (m : ℝ) ≤ 2 * (a : ℝ) * (M : ℝ) := by nlinarith [hmltR, hMR, haR]
        have hfin : 2 / (M : ℝ) ≤ 4 * (a : ℝ) / m := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
        linarith
  have hexp : dilationDiff g a m - dilationDiff g a (m - 1)
      = (mean g m - mean g (m - 1)) - (mean g M - mean g M') := by
    simp only [dilationDiff, hMdef, hM'def]
    ring
  rw [hexp]
  calc |(mean g m - mean g (m - 1)) - (mean g M - mean g M')|
      ≤ |mean g m - mean g (m - 1)| + |mean g M - mean g M'| := abs_sub _ _
    _ ≤ 2 / (m : ℝ) + 4 * (a : ℝ) / m := add_le_add t1 t2
    _ = (2 + 4 * (a : ℝ)) / m := by ring

/-- The sharp weight comparison, scaled to increments `c/m` and bound `c`. -/
@[category API, AMS 11]
theorem exists_abs_sum_primeWeight_comp_sub_sum_div_le_scaled {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c) :
    ∃ C : ℝ, ∀ (h : ℕ → ℝ) (N : ℕ),
      (∀ m, 2 ≤ m → m ≤ N → |h m - h (m - 1)| ≤ c / m) → (∀ m, |h m| ≤ c) →
        |(∑ k ∈ Icc 1 N, primeWeight k * h (N / k)) - ∑ n ∈ Icc 1 N, h n / n|
          ≤ ε * Real.log N + C := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primeWeight_comp_sub_sum_div_le (ε := ε / c) (by positivity)
  refine ⟨c * C, fun h N hinc hbd ↦ ?_⟩
  have hinc' : ∀ m, 2 ≤ m → m ≤ N → |h m / c - h (m - 1) / c| ≤ 1 / (m : ℝ) := by
    intro m hm2 hmN
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    rw [div_sub_div_same, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    have he : (1 : ℝ) / m * c = c / m := by ring
    linarith [hinc m hm2 hmN, he]
  have hbd' : ∀ m, |h m / c| ≤ 1 := by
    intro m
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact hbd m
  have hb := hC (fun n ↦ h n / c) N hinc' hbd'
  have e1 : ∑ k ∈ Icc 1 N, primeWeight k * (h (N / k) / c)
      = (∑ k ∈ Icc 1 N, primeWeight k * h (N / k)) / c := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e2 : ∑ n ∈ Icc 1 N, (h n / c) / n = (∑ n ∈ Icc 1 N, h n / n) / c := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun n _ ↦ by ring
  simp only [e1, e2, ← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc] at hb
  calc |(∑ k ∈ Icc 1 N, primeWeight k * h (N / k)) - ∑ n ∈ Icc 1 N, h n / n|
      ≤ (ε / c * Real.log N + C) * c := hb
    _ = ε * Real.log N + c * C := by field_simp

/--
**The differential inequality for the dilation difference.**  For every `\varepsilon > 0` there
is a constant `C` with
$$|D(N)|\log N \le \sum_{n \le N}\frac{|D(n)|}{n} + \varepsilon\log N + C \qquad (N \ge 2a).$$

This is the exact analogue of `Wirsing.exists_abs_mean_mul_log_le`, obtained from the
functional relation `Wirsing.abs_dilationDiff_mul_log_sub_sum_le` for `D` and the sharp
weight comparison.  Its consequence `Wirsing.tendsto_dilationDiff_of_tendsto_logAvg` is the
point: `D(N) \to 0` follows from the **logarithmic average** of `|D|` tending to `0`, a
statement that is itself invariant under dilation.
-/
@[category API, AMS 11]
theorem exists_abs_dilationDiff_mul_log_le (g : ℕ → ℝ) (hg : IsBddMultiplicative g) {a : ℕ}
    (ha : 1 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, 2 * a ≤ N →
      |dilationDiff g a N| * Real.log N
        ≤ (∑ n ∈ Icc 1 N, |dilationDiff g a n| / n) + ε * Real.log N + C := by
  classical
  set c : ℝ := 2 + 4 * (a : ℝ) with hcdef
  have hc : (0 : ℝ) < c := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    simp only [hcdef]; linarith
  obtain ⟨C, hC⟩ := exists_abs_sum_primeWeight_comp_sub_sum_div_le_scaled hε hc
  set h : ℕ → ℝ := fun n ↦ |dilationDiff g a n| with hhdef
  have hinc : ∀ m, 2 ≤ m → |h m - h (m - 1)| ≤ c / m := fun m hm ↦
    le_trans (abs_abs_sub_abs_le_abs_sub _ _) (abs_dilationDiff_sub_le hg ha hm)
  have hbd : ∀ m, |h m| ≤ c := by
    intro m
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    simp only [hhdef, abs_abs, hcdef]
    linarith [abs_dilationDiff_le_two hg a m]
  refine ⟨C + (2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8) + 2 * Real.log (2 * a)), fun N hN ↦ ?_⟩
  have haN : a ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  -- the Mertens drift is bounded by `log (2a)`
  have hdrift : Real.log N - Real.log ((N / a : ℕ) : ℝ) ≤ Real.log (2 * a) := by
    have hq1 : 1 ≤ N / a := (Nat.one_le_div_iff (by omega)).2 haN
    have hnat : N ≤ 2 * (a * (N / a)) := by
      have hmod := Nat.div_add_mod N a
      have hlt := Nat.mod_lt N (show 0 < a by omega)
      omega
    have hqR : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by exact_mod_cast hq1
    have hkey : (N : ℝ) ≤ (2 * (a : ℝ)) * ((N / a : ℕ) : ℝ) :=
      calc (N : ℝ) ≤ ((2 * (a * (N / a)) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 * (a : ℝ)) * ((N / a : ℕ) : ℝ) := by push_cast; ring
    have hlog := Real.log_le_log (by positivity) hkey
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    linarith
  -- the prime side dominates
  have hprime : |dilationDiff g a N| * Real.log N
      ≤ (∑ k ∈ Icc 1 N, primeWeight k * h (N / k))
        + (2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8) + 2 * Real.log (2 * a)) := by
    have hrel := abs_dilationDiff_mul_log_sub_sum_le g hg ha haN
    have hps : ∑ k ∈ Icc 1 N, primeWeight k * h (N / k)
        = ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * h (N / p) :=
      sum_primeWeight_mul (fun k ↦ h (N / k)) N
    have hsub : (Icc 1 (N / a)).filter Nat.Prime ⊆ (Icc 1 N).filter Nat.Prime := by
      intro q hq
      simp only [mem_filter, mem_Icc] at hq ⊢
      exact ⟨⟨hq.1.1, le_trans hq.1.2 (Nat.div_le_self _ _)⟩, hq.2⟩
    have hdom : |∑ p ∈ (Icc 1 (N / a)).filter Nat.Prime,
          Real.log p / p * (g p * dilationDiff g a (N / p))|
        ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * h (N / p) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      · intro q hq
        simp only [mem_filter, mem_Icc] at hq
        have hqp : q.Prime := hq.2
        have hw : (0 : ℝ) ≤ Real.log q / q :=
          div_nonneg (Real.log_natCast_nonneg _) (by positivity)
        rw [abs_mul, abs_of_nonneg hw, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ hw
        simp only [hhdef]
        calc |g q| * |dilationDiff g a (N / q)|
            ≤ 1 * |dilationDiff g a (N / q)| :=
              mul_le_mul_of_nonneg_right (hg.abs_le_one _ hqp.one_lt.le) (abs_nonneg _)
          _ = |dilationDiff g a (N / q)| := one_mul _
      · intro q hq _
        have hqp : q.Prime := (mem_filter.1 hq).2
        have hw : (0 : ℝ) ≤ Real.log q / q :=
          div_nonneg (Real.log_natCast_nonneg _) (by positivity)
        simp only [hhdef]
        positivity
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have habs : |dilationDiff g a N * Real.log N| = |dilationDiff g a N| * Real.log N := by
      rw [abs_mul, abs_of_nonneg hlogN]
    rw [hps]
    have hsa := abs_sub_abs_le_abs_sub (dilationDiff g a N * Real.log N)
      (∑ p ∈ (Icc 1 (N / a)).filter Nat.Prime,
        Real.log p / p * (g p * dilationDiff g a (N / p)))
    rw [habs] at hsa
    linarith [hdom, hrel, hsa]
  have hcmp := hC h N (fun m hm2 _ ↦ hinc m hm2) hbd
  have hsum : (∑ k ∈ Icc 1 N, primeWeight k * h (N / k))
      ≤ (∑ n ∈ Icc 1 N, h n / n) + ε * Real.log N + C := by
    linarith [(abs_le.1 hcmp).2]
  simp only [hhdef] at hsum hprime ⊢
  linarith

/--
**The bridge.**  If the logarithmic average of `|D|` tends to `0`, so does `D`.
-/
@[category API, AMS 11]
theorem tendsto_dilationDiff_of_tendsto_logAvg (g : ℕ → ℝ) (hg : IsBddMultiplicative g) {a : ℕ}
    (ha : 1 ≤ a)
    (hlog : Tendsto (fun N : ℕ ↦ (∑ n ∈ Icc 1 N, |dilationDiff g a n| / n) / Real.log N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ dilationDiff g a N) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨C, hC⟩ := exists_abs_dilationDiff_mul_log_le g hg ha (ε := ε / 4) (by positivity)
  have hA : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 1 N, |dilationDiff g a n| / n) / Real.log N < ε / 4 := by
    have := hlog.eventually_lt_const (show (0 : ℝ) < ε / 4 by positivity)
    exact this
  have hCsmall : ∀ᶠ N : ℕ in atTop, |C| / Real.log N < ε / 4 :=
    (Filter.Tendsto.div_atTop (tendsto_const_nhds (x := |C|))
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_lt_const
        (by positivity)
  have hlogpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [hA, hCsmall, hlogpos, eventually_ge_atTop (2 * a)] with N hAN hCN hlN hNa
  have h := hC N hNa
  rw [Real.norm_eq_abs]
  rw [div_lt_iff₀ hlN] at hAN hCN
  have hCle : C ≤ |C| := le_abs_self C
  have : |dilationDiff g a N| * Real.log N < ε * Real.log N := by
    calc |dilationDiff g a N| * Real.log N
        ≤ (∑ n ∈ Icc 1 N, |dilationDiff g a n| / n) + ε / 4 * Real.log N + C := h
      _ < ε / 4 * Real.log N + ε / 4 * Real.log N + ε / 4 * Real.log N := by
          linarith
      _ < ε * Real.log N := by nlinarith
  exact lt_of_mul_lt_mul_right (by linarith) hlN.le

/-- **The cocycle identity** `D_{ab}(N) = D_a(N) + D_b(\lfloor N/a\rfloor)`. -/
@[category API, AMS 11]
theorem dilationDiff_mul (g : ℕ → ℝ) (a b N : ℕ) :
    dilationDiff g (a * b) N = dilationDiff g a N + dilationDiff g b (N / a) := by
  simp only [dilationDiff, Nat.div_div_eq_div_mul]
  ring

/-- `D_a` and `D_b` differ only through the two scales `\lfloor N/a\rfloor`,
`\lfloor N/b\rfloor`. -/
@[category API, AMS 11]
theorem dilationDiff_sub_dilationDiff (g : ℕ → ℝ) (a b N : ℕ) :
    dilationDiff g a N - dilationDiff g b N = mean g (N / b) - mean g (N / a) := by
  simp only [dilationDiff]
  ring

/--
**Nearby dilations give nearly equal differences.**  For `1 ≤ a ≤ b ≤ N`,
$$|D_a(N) - D_b(N)| \le
  2\,\frac{\lfloor N/a\rfloor - \lfloor N/b\rfloor}{\lfloor N/a\rfloor},$$
which for fixed `a ≤ b` tends to `2(1 - a/b)` as `N \to \infty`.  So `D_a(N)` varies slowly in
the multiplicative variable `a`: two primes `p < q` with `q/p` close to `1` have essentially the
same dilation difference at every `N`.
-/
@[category API, AMS 11]
theorem abs_dilationDiff_sub_dilationDiff_le {g : ℕ → ℝ} (hg : IsBddMultiplicative g)
    {a b N : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N) :
    |dilationDiff g a N - dilationDiff g b N|
      ≤ 2 * (((N / a : ℕ) : ℝ) - ((N / b : ℕ) : ℝ)) / ((N / a : ℕ) : ℝ) := by
  have hb1 : 1 ≤ b := le_trans ha hab
  have hM1 : 1 ≤ N / b := (Nat.one_le_div_iff (by omega)).2 hbN
  have hMM' : N / b ≤ N / a := Nat.div_le_div_left hab (by omega)
  rw [dilationDiff_sub_dilationDiff, abs_sub_comm]
  exact bdd_abs_mean_sub_mean_le g hg hM1 hMM'

end Wirsing
