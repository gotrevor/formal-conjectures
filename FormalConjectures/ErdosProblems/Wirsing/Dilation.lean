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

end Wirsing
