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
public import FormalConjectures.ErdosProblems.Wirsing.Split
public import FormalConjectures.ErdosProblems.Wirsing.PrimeCos
public import FormalConjectures.ErdosProblems.Wirsing.Uniform

/-!
# Non-pretentiousness for real multiplicative functions bounded by `1`

The arithmetic input to Halász's theorem is that a **real** multiplicative function is at
infinite pretentious distance from every `n^{it}` with `t \ne 0`:
$$\sum_p \frac{1 - g(p)\cos(t\log p)}{p} = \infty .$$
`Wirsing/Pretentious.lean` and `Wirsing/PrimeCos.lean` prove this for `±1`-valued `f`.  The
proofs use the values only through the pointwise inequality
$$\tfrac14\bigl(1 - \cos 2\theta\bigr) \le 1 - g\cos\theta ,$$
which holds for every real `g` with `|g| \le 1`, since
`1 + \cos^2\theta - 2g\cos\theta
   = \tfrac12(1-g)(1+\cos\theta)^2 + \tfrac12(1+g)(1-\cos\theta)^2 \ge 0`.
So the whole non-pretentiousness package transfers to `Wirsing.IsBddMultiplicative`, which is
the class the coprime restrictions of `Wirsing/Split.lean` live in.

*References:*
- [Ha68] Halász, G., Über die Mittelwerte multiplikativer zahlentheoretischer Funktionen.
  Acta Math. Acad. Sci. Hung. 19 (1968), 365-403.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/--
**The pointwise resonance inequality for a bounded real value.**  For `|g| \le 1`,
`\tfrac14(1 - \cos 2\theta) \le 1 - g\cos\theta`.
-/
@[category API, AMS 11]
theorem quarter_one_sub_cos_two_le_of_abs_le_one {g θ : ℝ} (hg : |g| ≤ 1) :
    (1 - Real.cos (2 * θ)) / 4 ≤ 1 - g * Real.cos θ := by
  have hg1 : g ≤ 1 := (abs_le.1 hg).2
  have hg2 : -1 ≤ g := (abs_le.1 hg).1
  have h := Real.cos_two_mul θ
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - g) (sq_nonneg (Real.cos θ + 1)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + g) (sq_nonneg (Real.cos θ - 1))]

/--
**The sharp resonance defect for a bounded multiplicative `g`.**  For `t \ne 0`,
$$\sum_{p \le N}\frac{\log p}{p}\bigl(1 - g(p)\cos(t\log p)\bigr) \ge \frac{\log N}{8}
\qquad (N \text{ large}).$$
-/
@[category API, AMS 11]
theorem bdd_eventually_sum_primeWeight_one_sub_mul_cos_ge (g : ℕ → ℝ)
    (hg : IsBddMultiplicative g) {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ N : ℕ in atTop, Real.log N / 8 ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / p * (1 - g p * Real.cos (t * Real.log p)) := by
  classical
  have h2t : 2 * t ≠ 0 := by simpa using ht
  have hlim := tendsto_sum_primeWeight_one_sub_cos_div_log h2t
  have hev := hlim.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  filter_upwards [hev, eventually_ge_atTop 2] with N hN hN2
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hhalf : Real.log N / 2 ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / p * (1 - Real.cos (2 * t * Real.log p)) := by
    have := (lt_div_iff₀ hlogpos).1 hN
    linarith
  have hstep : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / p * (1 - Real.cos (2 * t * Real.log p)) / 4
        ≤ Real.log p / p * (1 - g p * Real.cos (t * Real.log p)) := by
    intro p hp
    obtain ⟨_, hpp⟩ := Finset.mem_filter.1 hp
    have hwnn : 0 ≤ Real.log p / p := by
      have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg _
      positivity
    have hq := quarter_one_sub_cos_two_le_of_abs_le_one (g := g p) (θ := t * Real.log p)
      (hg.abs_le_one p hpp.one_lt.le)
    have hcos : Real.cos (2 * (t * Real.log p)) = Real.cos (2 * t * Real.log p) := by ring_nf
    rw [hcos] at hq
    nlinarith [hq, hwnn]
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.sum_div] at hsum
  linarith

/-- **A bounded real multiplicative `g` is pretentious to no `n^{it}` with `t \ne 0`.** -/
@[category API, AMS 11]
theorem bdd_not_summable_one_sub_mul_cos (g : ℕ → ℝ) (hg : IsBddMultiplicative g) {t : ℝ}
    (ht : t ≠ 0) :
    ¬ Summable fun p : Nat.Primes ↦ (1 - g p * Real.cos (t * Real.log p)) / p := by
  intro hS
  refine not_summable_one_sub_cos (t := 2 * t) (by simpa using ht) ?_
  have hppos : ∀ p : Nat.Primes, (0 : ℝ) < (p : ℝ) := fun p ↦ by exact_mod_cast p.2.pos
  refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_) (hS.mul_left 4)
  · have := Real.cos_le_one (2 * t * Real.log (p : ℝ))
    have := hppos p
    positivity
  · have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
    have hkey := quarter_one_sub_cos_two_le_of_abs_le_one (g := g (p : ℕ))
      (θ := t * Real.log (p : ℝ)) (hg.abs_le_one _ hp1)
    rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring] at hkey
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (hppos p)]
    linarith

/-- Each term of `Wirsing.primeDefect` is nonnegative, for a bounded multiplicative `g`. -/
@[category API, AMS 11]
theorem bdd_primeDefect_term_nonneg {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {p : ℕ}
    (hp : p.Prime) (t : ℝ) : 0 ≤ (1 - g p * Real.cos (t * Real.log p)) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc := Real.neg_one_le_cos (t * Real.log p)
  have hc' := Real.cos_le_one (t * Real.log p)
  have hb := abs_le.1 (hg.abs_le_one p hp.one_lt.le)
  refine div_nonneg ?_ hpR.le
  nlinarith [hb.1, hb.2, hc, hc']

/-- `Wirsing.primeDefect` is nondecreasing in the cut-off, for a bounded multiplicative `g`. -/
@[category API, AMS 11]
theorem bdd_primeDefect_mono {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {M N : ℕ} (hMN : M ≤ N)
    (t : ℝ) : primeDefect g M t ≤ primeDefect g N t := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ ↦ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hMN⟩, hp.2⟩
  · exact bdd_primeDefect_term_nonneg hg (Finset.mem_filter.1 hp).2 t

/--
**Uniform non-pretentiousness for a bounded multiplicative `g`.**  For every `T` and every `M`
there is an `N₀` beyond which `D_N(t) \ge M` *simultaneously* for all `|t| \le T`.

This is the input Halász's theorem needs, and the only place the compactness of the twist range
is used.  Compare `Wirsing.exists_forall_primeDefect_ge`, which assumes `f` is `±1`-valued.
-/
@[category API, AMS 11]
theorem bdd_exists_forall_primeDefect_ge {g : ℕ → ℝ} (hg : IsBddMultiplicative g)
    (hdiv : ∀ t : ℝ, ¬ Summable fun p : Nat.Primes ↦ (1 - g p * Real.cos (t * Real.log p)) / p)
    (T M : ℝ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ t ∈ Set.Icc (-T) T, M ≤ primeDefect g N t := by
  classical
  have key : ∀ t : ℝ, ∃ n : ℕ, M < primeDefect g n t := by
    intro t
    have hd := tendsto_sum_primes_atTop
      (g := fun p ↦ (1 - g p * Real.cos (t * Real.log p)) / p)
      (fun p hp ↦ bdd_primeDefect_term_nonneg hg hp t) (hdiv t)
    exact ((hd.eventually_gt_atTop M).exists).imp fun n hn ↦ hn
  choose Nt hNt using key
  set U : ℝ → Set ℝ := fun t ↦ {u : ℝ | M < primeDefect g (Nt t) u} with hU
  have hUmem : ∀ t ∈ Set.Icc (-T) T, U t ∈ 𝓝 t := by
    intro t _
    exact (isOpen_lt continuous_const (continuous_primeDefect g (Nt t))).mem_nhds (hNt t)
  obtain ⟨F, hFsub, hFcov⟩ := isCompact_Icc.elim_nhds_subcover U hUmem
  refine ⟨F.sup Nt, fun N hN t ht ↦ ?_⟩
  obtain ⟨t', ht'F, ht'⟩ : ∃ t' ∈ F, t ∈ U t' := by simpa using hFcov ht
  have h2 : primeDefect g (Nt t') t ≤ primeDefect g N t :=
    bdd_primeDefect_mono hg (le_trans (Finset.le_sup ht'F) hN) t
  exact le_of_lt (lt_of_lt_of_le ht' h2)

end Wirsing
