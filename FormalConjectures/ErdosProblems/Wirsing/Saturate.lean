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
public import FormalConjectures.ErdosProblems.Wirsing.Dilation

/-!
# Saturation, runs, and crossings for the dilation difference

Fix a prime `q` and write `D(N) = \text{mean } g\ N - \text{mean } g\ \lfloor N/q\rfloor`.  This
file contains the three elementary inputs of the crossing argument for
`Wirsing.dilationInvariant_prime` (see `PENDING_WORK.md`, lap 16):

1. **The run bound.**  The values of `D` along a geometric progression telescope,
   `\sum_{i_1 \le i < i_2} D(\lfloor N/q^i\rfloor)
      = \sigma(\lfloor N/q^{i_1}\rfloor) - \sigma(\lfloor N/q^{i_2}\rfloor)`,
   so their partial sums are bounded by `2`.  Hence `D` cannot keep one sign and stay away
   from `0` along more than `2/\delta` consecutive terms.

2. **Crossings.**  `D` is real, and its steps are `O(1/m)`
   (`Wirsing.abs_dilationDiff_sub_le`), so between a positive and a negative value it must pass
   within `O(1/m)` of `0`.  Combined with 1: **every geometric block of bounded length contains
   a scale at which `|D|` is small** (`Wirsing.exists_abs_dilationDiff_le_of_block`).  This is
   the only step that uses that `g` is real; it is false for `g(n) = n^{i\theta}`, where `D`
   rotates at constant modulus.

3. **Saturation.**  The functional relation of `Wirsing/Dilation.lean` is exactly critical, so
   if `|D(N)|` is within `\varepsilon` of its own limsup `B`, then the scales `\lfloor N/p\rfloor`
   where `|D|` drops below `B - \delta` carry Mertens weight at most
   `(\varepsilon\log N + O(1))/\delta` (`Wirsing.exists_saturation`).

Together with the prime number theorem — available here as
`Wirsing.Newman.tendsto_sum_log_prime_div_window`, the statement that a multiplicative window of
any fixed ratio carries Mertens weight bounded away from `0` — these contradict each other: 2
produces a positive proportion of deficient scales, 3 forbids it.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-! ### The run bound -/

/-- **Telescoping along a geometric progression.**  The dilation differences at the scales
`\lfloor N/q^i\rfloor` telescope. -/
@[category API, AMS 11]
theorem sum_Ico_dilationDiff (g : ℕ → ℝ) (q N : ℕ) {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) :
    ∑ i ∈ Ico i₁ i₂, dilationDiff g q (N / q ^ i)
      = mean g (N / q ^ i₁) - mean g (N / q ^ i₂) := by
  induction i₂, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep : N / q ^ n / q = N / q ^ (n + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      rw [Finset.sum_Ico_succ_top hn, ih, dilationDiff, hstep]
      ring

/-- **The run bound.**  Partial sums of `D` along a geometric progression are bounded by `2`. -/
@[category API, AMS 11]
theorem abs_sum_Ico_dilationDiff_le_two {g : ℕ → ℝ} (hg : IsBddMultiplicative g) (q N : ℕ)
    {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) :
    |∑ i ∈ Ico i₁ i₂, dilationDiff g q (N / q ^ i)| ≤ 2 := by
  rw [sum_Ico_dilationDiff g q N h]
  refine (abs_sub _ _).trans ?_
  linarith [abs_mean_le_one_of_bdd hg (N / q ^ i₁), abs_mean_le_one_of_bdd hg (N / q ^ i₂)]

/-- A run of terms all at least `δ > 0` has at most `2/δ` terms. -/
@[category API, AMS 11]
theorem card_le_of_forall_dilationDiff_ge {g : ℕ → ℝ} (hg : IsBddMultiplicative g) (q N : ℕ)
    {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) {δ : ℝ}
    (hrun : ∀ i ∈ Ico i₁ i₂, δ ≤ dilationDiff g q (N / q ^ i)) :
    ((i₂ - i₁ : ℕ) : ℝ) * δ ≤ 2 := by
  have hsum : ((i₂ - i₁ : ℕ) : ℝ) * δ ≤ ∑ i ∈ Ico i₁ i₂, dilationDiff g q (N / q ^ i) := by
    have := Finset.card_nsmul_le_sum (Ico i₁ i₂) (fun i ↦ dilationDiff g q (N / q ^ i)) δ hrun
    simpa [Nat.card_Ico, nsmul_eq_mul] using this
  exact hsum.trans (le_abs_self _ |>.trans (abs_sum_Ico_dilationDiff_le_two hg q N h))

/-! ### Crossings: a real sequence that changes sign passes near `0` -/

/-- **Discrete intermediate value theorem.**  A real sequence that is negative at `a` and
nonnegative at `b ≥ a` has an adjacent pair straddling `0`. -/
@[category API, AMS 11]
theorem exists_sign_change {h : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) (ha : h a < 0) (hb : 0 ≤ h b) :
    ∃ t, a ≤ t ∧ t < b ∧ h t ≤ 0 ∧ 0 ≤ h (t + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hb (by linarith)
  | succ n hn ih =>
      rcases lt_or_ge (h n) 0 with hneg | hpos
      · exact ⟨n, hn, Nat.lt_succ_self n, hneg.le, hb⟩
      · obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih hpos
        exact ⟨t, ht1, ht2.trans (Nat.lt_succ_self n), ht3, ht4⟩

/--
**A sign change of `D` forces `|D|` to be small.**  If `D(m)` and `D(m+1)` have opposite signs
then both are at most the step bound `(2 + 4q)/(m+1)`.
-/
@[category API, AMS 11]
theorem abs_dilationDiff_le_of_straddle {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {q : ℕ}
    (hq : 1 ≤ q) {m : ℕ} (hm : 1 ≤ m)
    (h : dilationDiff g q m * dilationDiff g q (m + 1) ≤ 0) :
    |dilationDiff g q (m + 1)| ≤ (2 + 4 * (q : ℝ)) / (m + 1) := by
  have hstep := abs_dilationDiff_sub_le hg hq (m := m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hstep
  push_cast at hstep
  rw [abs_le] at hstep
  set x := dilationDiff g q m with hx
  set y := dilationDiff g q (m + 1) with hy
  rcases le_or_gt 0 y with hy0 | hy0
  · rcases eq_or_lt_of_le hy0 with heq | hpos
    · rw [← heq, abs_zero]
      positivity
    · have hxle : x ≤ 0 := by nlinarith
      rw [abs_of_pos hpos]
      linarith [hstep.2]
  · have hxge : 0 ≤ x := by nlinarith
    rw [abs_of_neg hy0]
    linarith [hstep.1]

/-- A run of terms all at most `-δ < 0` has at most `2/δ` terms. -/
@[category API, AMS 11]
theorem card_le_of_forall_dilationDiff_le_neg {g : ℕ → ℝ} (hg : IsBddMultiplicative g) (q N : ℕ)
    {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) {δ : ℝ}
    (hrun : ∀ i ∈ Ico i₁ i₂, dilationDiff g q (N / q ^ i) ≤ -δ) :
    ((i₂ - i₁ : ℕ) : ℝ) * δ ≤ 2 := by
  have hsum : ∑ i ∈ Ico i₁ i₂, dilationDiff g q (N / q ^ i) ≤ ((i₂ - i₁ : ℕ) : ℝ) * (-δ) := by
    have := Finset.sum_le_card_nsmul (Ico i₁ i₂) (fun i ↦ dilationDiff g q (N / q ^ i)) (-δ) hrun
    simpa [Nat.card_Ico, nsmul_eq_mul] using this
  have habs := abs_sum_Ico_dilationDiff_le_two hg q N h
  have := (abs_le.1 habs).1
  linarith

/--
**Every geometric block contains a scale at which `|D|` is small.**  Fix `J` with
`J\cdot\Delta/4 > 2`.  Then in the block of scales `[\lfloor m/q^J\rfloor, m]` there is an `s`
with `|D(s)| \le \Delta/4`.

Proof: the run bound forbids all `J` progression values `D(\lfloor m/q^i\rfloor)` from being
`\ge \Delta/4`, and forbids them all from being `\le -\Delta/4`.  So either one of them already
has `|D| \le \Delta/4`, or two adjacent ones have opposite signs — and then, since `D` is
**real** with steps `O(1/s)`, the discrete intermediate value theorem produces a scale between
them at which `|D|` is at most the step bound.

This is the only step of the crossing argument that uses that `g` is real; for
`g(n) = n^{i\theta}` the dilation difference rotates at constant modulus and never crosses `0`.
-/
@[category API, AMS 11]
theorem exists_abs_dilationDiff_le_of_block {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {q : ℕ}
    (hq : 1 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ) {J m : ℕ} (hJ : 2 < (J : ℝ) * (Δ / 4))
    (hmlow : 1 ≤ m / q ^ J)
    (hstep : (2 + 4 * (q : ℝ)) / ((m / q ^ J : ℕ) : ℝ) ≤ Δ / 4) :
    ∃ s, m / q ^ J ≤ s ∧ s ≤ m ∧ |dilationDiff g q s| ≤ Δ / 4 := by
  by_contra hcon
  push Not at hcon
  set t : ℕ → ℕ := fun i ↦ m / q ^ i with ht
  have htmono : ∀ i, i ≤ J → m / q ^ J ≤ t i := by
    intro i hi
    exact Nat.div_le_div_left (Nat.pow_le_pow_right hq hi) (Nat.pow_pos (by omega))
  have htle : ∀ i, t i ≤ m := fun i ↦ Nat.div_le_self _ _
  have hsucc : ∀ i, t (i + 1) = t i / q := by
    intro i
    simp only [ht, Nat.div_div_eq_div_mul, pow_succ]
  have hbig : ∀ i, i ≤ J → Δ / 4 < |dilationDiff g q (t i)| :=
    fun i hi ↦ hcon (t i) (htmono i hi) (htle i)
  have hJ1 : 1 ≤ J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · rw [h] at hJ
      norm_num at hJ
    · exact h
  have hnotpos : ¬ (∀ i, i < J → 0 < dilationDiff g q (t i)) := by
    intro hall
    have hrun : ∀ i ∈ Ico 0 J, Δ / 4 ≤ dilationDiff g q (m / q ^ i) := by
      intro i hi
      have hi' : i < J := (mem_Ico.1 hi).2
      have h1 := hbig i hi'.le
      have h2 := hall i hi'
      rw [abs_of_pos h2] at h1
      exact h1.le
    have hcard := card_le_of_forall_dilationDiff_ge hg q m (Nat.zero_le J) hrun
    simp only [Nat.sub_zero] at hcard
    linarith
  have hnotneg : ¬ (∀ i, i < J → dilationDiff g q (t i) < 0) := by
    intro hall
    have hrun : ∀ i ∈ Ico 0 J, dilationDiff g q (m / q ^ i) ≤ -(Δ / 4) := by
      intro i hi
      have hi' : i < J := (mem_Ico.1 hi).2
      have h1 := hbig i hi'.le
      have h2 := hall i hi'
      rw [abs_of_neg h2] at h1
      linarith
    have hcard := card_le_of_forall_dilationDiff_le_neg hg q m (Nat.zero_le J) hrun
    simp only [Nat.sub_zero] at hcard
    linarith
  push Not at hnotpos hnotneg
  obtain ⟨j, hjJ, hjneg⟩ := hnotpos
  obtain ⟨i, hiJ, hipos⟩ := hnotneg
  have hjneg' : dilationDiff g q (t j) < 0 := by
    rcases lt_or_eq_of_le hjneg with h | h
    · exact h
    · have hb := hbig j hjJ.le
      rw [h, abs_zero] at hb
      linarith
  have hipos' : 0 < dilationDiff g q (t i) := by
    rcases lt_or_eq_of_le hipos with h | h
    · exact h
    · have hb := hbig i hiJ.le
      rw [← h, abs_zero] at hb
      linarith
  -- an adjacent pair of progression indices with opposite signs
  have hadj : ∃ k, k + 1 ≤ J ∧
      dilationDiff g q (t k) * dilationDiff g q (t (k + 1)) ≤ 0 := by
    rcases le_or_gt i j with hij | hij
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
        exists_sign_change (h := fun k ↦ - dilationDiff g q (t k)) hij
          (neg_lt_zero.2 hipos') (neg_nonneg.2 hjneg'.le)
      have h3 : -dilationDiff g q (t k) ≤ 0 := hk3
      have h4 : 0 ≤ -dilationDiff g q (t (k + 1)) := hk4
      refine ⟨k, by omega, ?_⟩
      nlinarith
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
        exists_sign_change (h := fun k ↦ dilationDiff g q (t k)) hij.le hjneg' hipos'.le
      have h3 : dilationDiff g q (t k) ≤ 0 := hk3
      have h4 : 0 ≤ dilationDiff g q (t (k + 1)) := hk4
      refine ⟨k, by omega, ?_⟩
      nlinarith
  obtain ⟨k, hkJ, hkprod⟩ := hadj
  have hbu : Δ / 4 < |dilationDiff g q (t k)| := hbig k (by omega)
  have hbv : Δ / 4 < |dilationDiff g q (t (k + 1))| := hbig (k + 1) hkJ
  set u := t k with hu
  set v := t (k + 1) with hv
  have hvu : v ≤ u := by rw [hv, hsucc k]; exact Nat.div_le_self _ _
  have hvlow : m / q ^ J ≤ v := htmono (k + 1) hkJ
  -- the intermediate value theorem in the scale variable
  have hcross : ∃ r, v ≤ r ∧ r < u ∧
      dilationDiff g q r * dilationDiff g q (r + 1) ≤ 0 := by
    rcases le_or_gt 0 (dilationDiff g q u) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hbu
      have hDu : 0 < dilationDiff g q u := by linarith
      have hvle : dilationDiff g q v ≤ 0 := by nlinarith
      have hvneg : dilationDiff g q v < 0 := by
        rcases lt_or_eq_of_le hvle with h | h
        · exact h
        · rw [h, abs_zero] at hbv; linarith
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
        exists_sign_change (h := fun r ↦ dilationDiff g q r) hvu hvneg hpos
      have h3 : dilationDiff g q r ≤ 0 := hr3
      have h4 : 0 ≤ dilationDiff g q (r + 1) := hr4
      exact ⟨r, hr1, hr2, by nlinarith⟩
    · rw [abs_of_neg hneg] at hbu
      have hvge : 0 ≤ dilationDiff g q v := by nlinarith
      have hvpos : 0 < dilationDiff g q v := by
        rcases lt_or_eq_of_le hvge with h | h
        · exact h
        · rw [← h, abs_zero] at hbv; linarith
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ :=
        exists_sign_change (h := fun r ↦ - dilationDiff g q r) hvu (neg_lt_zero.2 hvpos)
          (neg_nonneg.2 hneg.le)
      have h3 : -dilationDiff g q r ≤ 0 := hr3
      have h4 : 0 ≤ -dilationDiff g q (r + 1) := hr4
      exact ⟨r, hr1, hr2, by nlinarith⟩
  obtain ⟨r, hr1, hr2, hrprod⟩ := hcross
  have hr0 : 1 ≤ r := le_trans (le_trans hmlow hvlow) hr1
  have hbound := abs_dilationDiff_le_of_straddle hg hq hr0 hrprod
  have hmono : (2 + 4 * (q : ℝ)) / ((r : ℝ) + 1) ≤ (2 + 4 * (q : ℝ)) / ((m / q ^ J : ℕ) : ℝ) := by
    have hd1 : (0 : ℝ) < ((m / q ^ J : ℕ) : ℝ) := by exact_mod_cast hmlow
    have hd2 : ((m / q ^ J : ℕ) : ℝ) ≤ (r : ℝ) + 1 := by
      have h' : (m / q ^ J : ℕ) ≤ r := le_trans hvlow hr1
      have h'' : ((m / q ^ J : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h'
      linarith
    exact div_le_div_of_nonneg_left (by positivity) hd1 hd2
  have hfin : |dilationDiff g q (r + 1)| ≤ Δ / 4 := le_trans hbound (le_trans hmono hstep)
  have hin1 : m / q ^ J ≤ r + 1 := le_trans (le_trans hvlow hr1) (by omega)
  have hin2 : r + 1 ≤ m := le_trans (by omega) (htle k)
  exact absurd hfin (not_le.2 (hcon (r + 1) hin1 hin2))

/-! ### Saturation -/

open scoped Classical in
/--
**The saturation lemma.**  Let `B` bound `|D|` at every scale `\ge n_0`.  Then the scales
`\lfloor N/p\rfloor \ge n_0` at which `|D|` drops below `B - \delta` carry Mertens weight at
most `\big((B - |D(N)|)\log N + C\big)/\delta`, with `C` independent of `N`.

So if `|D(N)|` is nearly as large as `B`, then `|D|` is nearly as large as `B` at almost every
scale `\lfloor N/p\rfloor`, in Mertens weight.  This is what makes the exactly critical
functional relation of `Wirsing/Dilation.lean` usable: it cannot be iterated, but it does force
the deficient scales to be rare.
-/
@[category API, AMS 11]
theorem exists_saturation (g : ℕ → ℝ) (hg : IsBddMultiplicative g) {a : ℕ} (ha : 1 ≤ a)
    {B δ : ℝ} (hB : 0 ≤ B) {n₀ : ℕ} (hn₀ : a ≤ n₀)
    (hbd : ∀ n, n₀ ≤ n → |dilationDiff g a n| ≤ B) :
    ∃ C : ℝ, ∀ N : ℕ, 2 * a * n₀ ≤ N →
      δ * (∑ p ∈ ((Icc 1 (N / a)).filter Nat.Prime).filter
              (fun p ↦ |dilationDiff g a (N / p)| ≤ B - δ ∧ n₀ ≤ N / p), Real.log p / p)
        ≤ (B - |dilationDiff g a N|) * Real.log N + C := by
  classical
  set K : ℝ := Real.log 4 + 8 with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hK]; linarith
  have hn₀1 : 1 ≤ n₀ := le_trans ha hn₀
  refine ⟨B * K + 2 * Real.log (2 * n₀) + 4 * K
    + (2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8) + 2 * Real.log (2 * a)), ?_⟩
  intro N hN
  have hpos : 0 < 2 * a * n₀ :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hN1 : 1 ≤ N := le_trans hpos hN
  have haN : a ≤ N := le_trans (by nlinarith [hn₀1, ha]) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hn₀R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀1
  have hNbig : (2 * a * n₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- a general floor bound: `log N - log (2 c) ≤ log ⌊N/c⌋` when `2 c ≤ N`
  have hfloorlog : ∀ c : ℕ, 1 ≤ c → 2 * c ≤ N →
      Real.log N - Real.log (2 * c) ≤ Real.log ((N / c : ℕ) : ℝ) := by
    intro c hc1 hcN
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hcNR : (2 * c : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
    set m := N / c with hm
    have hdm := Nat.div_add_mod N c
    have hmod : N % c < c := Nat.mod_lt _ (by omega)
    have hlt : N < c * m + c := by rw [← hdm]; exact Nat.add_lt_add_left hmod _
    have hcast : (N : ℝ) < (c : ℝ) * (m : ℝ) + (c : ℝ) := by exact_mod_cast hlt
    have hd : (N : ℝ) / c ≤ (m : ℝ) + 1 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h3 : (N : ℝ) / c - (N : ℝ) / (2 * c) = (N : ℝ) / (2 * c) := by
      field_simp; ring
    have hmR : (N : ℝ) / (2 * c) ≤ (m : ℝ) := by linarith
    have hNa : (0 : ℝ) < (N : ℝ) / (2 * c) := by positivity
    have hlog := Real.log_le_log hNa hmR
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have hlogc : Real.log (2 * (c : ℝ)) = Real.log 2 + Real.log c :=
      Real.log_mul (by norm_num) (by positivity)
    linarith
  set M := N / a with hMdef
  have hM1 : 1 ≤ M := (Nat.one_le_div_iff (by omega)).2 haN
  have hMN : M ≤ N := Nat.div_le_self _ _
  set P := (Icc 1 M).filter Nat.Prime with hP
  have hwnn : ∀ p ∈ P, 0 ≤ Real.log p / p := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    exact div_nonneg (Real.log_nonneg this) (by linarith)
  -- the functional relation
  have hrel := abs_dilationDiff_mul_log_sub_sum_le g hg ha haN
  rw [← hMdef, ← hP] at hrel
  -- the log gap `log N - log M ≤ log (2 a)`
  have hgap : Real.log N - Real.log ((M : ℕ) : ℝ) ≤ Real.log (2 * a) := by
    have := hfloorlog a ha (by nlinarith [hn₀1])
    rw [← hMdef] at this
    linarith
  set pred : ℕ → Prop := fun p ↦ |dilationDiff g a (N / p)| ≤ B - δ ∧ n₀ ≤ N / p with hpred
  set S1 := P.filter pred with hS1
  set W := ∑ p ∈ P, Real.log p / p with hWdef
  set W1 := ∑ p ∈ S1, Real.log p / p with hW1
  set Big := P.filter (fun p ↦ n₀ ≤ N / p) with hBig
  set S3 := P.filter (fun p ↦ ¬ (n₀ ≤ N / p)) with hS3
  set W3 := ∑ p ∈ S3, Real.log p / p with hW3
  have hS1sub : S1 ⊆ Big := by
    intro p hp
    simp only [hS1, mem_filter, hpred] at hp
    exact mem_filter.2 ⟨hp.1, hp.2.2⟩
  -- the three groups
  have hsplitA : ∑ p ∈ P, Real.log p / p * |dilationDiff g a (N / p)|
      = (∑ p ∈ Big, Real.log p / p * |dilationDiff g a (N / p)|)
        + ∑ p ∈ S3, Real.log p / p * |dilationDiff g a (N / p)| :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsplitB : ∑ p ∈ Big, Real.log p / p * |dilationDiff g a (N / p)|
      = (∑ p ∈ S1, Real.log p / p * |dilationDiff g a (N / p)|)
        + ∑ p ∈ Big \ S1, Real.log p / p * |dilationDiff g a (N / p)| := by
    rw [add_comm]
    exact (Finset.sum_sdiff hS1sub).symm
  have hb1 : ∑ p ∈ S1, Real.log p / p * |dilationDiff g a (N / p)| ≤ (B - δ) * W1 := by
    rw [hW1, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hmem : p ∈ P := (mem_filter.1 hp).1
    have hbd' : |dilationDiff g a (N / p)| ≤ B - δ := by
      have := (mem_filter.1 hp).2
      simp only [hpred] at this
      exact this.1
    rw [mul_comm (B - δ) (Real.log p / p)]
    exact mul_le_mul_of_nonneg_left hbd' (hwnn p hmem)
  have hb2 : ∑ p ∈ Big \ S1, Real.log p / p * |dilationDiff g a (N / p)|
      ≤ B * ∑ p ∈ Big \ S1, Real.log p / p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hmem' := Finset.mem_sdiff.1 hp
    have hmem : p ∈ P := (mem_filter.1 hmem'.1).1
    have hge : n₀ ≤ N / p := (mem_filter.1 hmem'.1).2
    rw [mul_comm B (Real.log p / p)]
    exact mul_le_mul_of_nonneg_left (hbd _ hge) (hwnn p hmem)
  have hb3 : ∑ p ∈ S3, Real.log p / p * |dilationDiff g a (N / p)| ≤ 2 * W3 := by
    rw [hW3, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hmem : p ∈ P := (mem_filter.1 hp).1
    rw [mul_comm (2 : ℝ) (Real.log p / p)]
    exact mul_le_mul_of_nonneg_left (abs_dilationDiff_le_two hg a (N / p)) (hwnn p hmem)
  -- the total weight
  have hWle : W ≤ Real.log N + K := by
    have h := (abs_le.1 (Mertens.abs_sum_log_prime_div_sub_log_le hM1)).2
    have hlogM : Real.log ((M : ℕ) : ℝ) ≤ Real.log N := log_natCast_mono hMN
    rw [hWdef, hP]
    linarith
  -- the weight of the small scales
  have hW3le : W3 ≤ Real.log (2 * n₀) + 2 * K := by
    set Q := (Icc 1 (N / n₀)).filter Nat.Prime with hQ
    have hQ1 : 1 ≤ N / n₀ := (Nat.one_le_div_iff (by omega)).2 (by
      calc n₀ ≤ 2 * a * n₀ := by nlinarith [ha]
        _ ≤ N := hN)
    have hQP : Q ⊆ P := by
      intro p hp
      simp only [hQ, mem_filter, mem_Icc] at hp
      refine mem_filter.2 ⟨mem_Icc.2 ⟨hp.1.1, ?_⟩, hp.2⟩
      exact le_trans hp.1.2 (Nat.div_le_div_left hn₀ (by omega))
    have hdisj : S3 ⊆ P \ Q := by
      intro p hp
      simp only [hS3, mem_filter] at hp
      refine Finset.mem_sdiff.2 ⟨hp.1, fun hq ↦ hp.2 ?_⟩
      have hple : p ≤ N / n₀ := (mem_Icc.1 (mem_filter.1 hq).1).2
      have hp0 : 0 < p := (mem_filter.1 hq).2.pos
      refine (Nat.le_div_iff_mul_le hp0).2 ?_
      have h' := (Nat.le_div_iff_mul_le (show 0 < n₀ by omega)).1 hple
      rw [Nat.mul_comm]
      exact h'
    have hsub : W3 ≤ ∑ p ∈ P \ Q, Real.log p / p := by
      rw [hW3]
      refine Finset.sum_le_sum_of_subset_of_nonneg hdisj fun p hp _ ↦ ?_
      exact hwnn p (Finset.mem_sdiff.1 hp).1
    have hsd : (∑ p ∈ P \ Q, Real.log p / p) + ∑ p ∈ Q, Real.log p / p = W := by
      rw [hWdef]
      exact Finset.sum_sdiff hQP
    have hQge : Real.log ((N / n₀ : ℕ) : ℝ) - K ≤ ∑ p ∈ Q, Real.log p / p := by
      have h := (abs_le.1 (Mertens.abs_sum_log_prime_div_sub_log_le hQ1)).1
      rw [hQ]
      linarith
    have hlow := hfloorlog n₀ hn₀1 (by nlinarith [ha])
    linarith
  -- the three groups assemble
  have hW1nn : 0 ≤ W1 := by
    rw [hW1]; exact Finset.sum_nonneg fun p hp ↦ hwnn p (mem_filter.1 hp).1
  have hsumle : ∑ p ∈ P, Real.log p / p * |dilationDiff g a (N / p)|
      ≤ B * W - δ * W1 + 2 * W3 := by
    have hW2 : ∑ p ∈ Big \ S1, Real.log p / p ≤ W - W1 := by
      have h1 : (∑ p ∈ Big \ S1, Real.log p / p) + W1 = ∑ p ∈ Big, Real.log p / p := by
        rw [hW1]
        exact Finset.sum_sdiff hS1sub
      have h2 : ∑ p ∈ Big, Real.log p / p ≤ W := by
        rw [hWdef, hBig]
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ ↦ ?_
        exact hwnn p hp
      linarith
    have hprod : B * ∑ p ∈ Big \ S1, Real.log p / p ≤ B * (W - W1) :=
      mul_le_mul_of_nonneg_left hW2 hB
    have hexp : B * (W - W1) = B * W - B * W1 := by ring
    rw [hsplitA, hsplitB]
    have hBW1 : 0 ≤ B * W1 := mul_nonneg hB hW1nn
    have hδB : (B - δ) * W1 = B * W1 - δ * W1 := by ring
    linarith [hb1, hb2, hb3]
  -- the relation, with `|g p| \le 1`
  have hgabs : |∑ p ∈ P, Real.log p / p * (g p * dilationDiff g a (N / p))|
      ≤ ∑ p ∈ P, Real.log p / p * |dilationDiff g a (N / p)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    have hgp : |g p| ≤ 1 := hg.abs_le_one p hp1
    have hwp : 0 ≤ Real.log p / p := hwnn p hp
    calc |Real.log p / p * (g p * dilationDiff g a (N / p))|
        = Real.log p / p * (|g p| * |dilationDiff g a (N / p)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hwp]
      _ ≤ Real.log p / p * (1 * |dilationDiff g a (N / p)|) := by
          refine mul_le_mul_of_nonneg_left ?_ hwp
          exact mul_le_mul_of_nonneg_right hgp (abs_nonneg _)
      _ = Real.log p / p * |dilationDiff g a (N / p)| := by ring
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg _
  have hDN : |dilationDiff g a N| * Real.log N
      ≤ (∑ p ∈ P, Real.log p / p * |dilationDiff g a (N / p)|)
        + (2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8) + 2 * Real.log (2 * a)) := by
    have habs : |dilationDiff g a N * Real.log N|
        ≤ |∑ p ∈ P, Real.log p / p * (g p * dilationDiff g a (N / p))|
          + (2 * (9 + Real.log 4) + 2 * (Real.log 4 + 8)
             + 2 * (Real.log N - Real.log ((M : ℕ) : ℝ))) := by
      have h := abs_sub_abs_le_abs_sub (dilationDiff g a N * Real.log N)
        (∑ p ∈ P, Real.log p / p * (g p * dilationDiff g a (N / p)))
      linarith [h.trans hrel]
    rw [abs_mul, abs_of_nonneg hlogN] at habs
    linarith [hgabs, hgap]
  have hBW : B * W ≤ B * Real.log N + B * K := by nlinarith [hWle, hB]
  rw [sub_mul]
  linarith [hDN, hsumle, hW3le]

end Wirsing
