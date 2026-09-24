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
# Uniform non-pretentiousness on a compact range of twists

`Wirsing.not_summable_one_sub_mul_cos_of_not_summable` says that, under the divergence
hypothesis, the *pretentious distance*
$$D_N(t) = \sum_{p \le N} \frac{1 - f(p)\cos(t\log p)}{p}$$
tends to `∞` for each fixed `t`.  Halász's theorem needs more: that
`\min_{|t| \le T} D_N(t) \to \infty` for each fixed `T`.

This file supplies that upgrade.  Every term of `D_N(t)` is nonnegative, so `D_N(t)` is
nondecreasing in `N`; it is continuous in `t`; and `[-T, T]` is compact.  A finite subcover
therefore turns pointwise divergence into uniform divergence — the Dini argument.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-- The pretentious distance of `f` to `n^{it}`, truncated at `N`. -/
noncomputable def primeDefect (f : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 - f p * Real.cos (t * Real.log p)) / p

/-- Each term of `Wirsing.primeDefect` is nonnegative. -/
@[category API, AMS 11]
theorem primeDefect_term_nonneg {f : ℕ → ℝ} (hf : IsPMOneMultiplicative f) {p : ℕ}
    (hp : p.Prime) (t : ℝ) : 0 ≤ (1 - f p * Real.cos (t * Real.log p)) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc := Real.neg_one_le_cos (t * Real.log p)
  have hc' := Real.cos_le_one (t * Real.log p)
  refine div_nonneg ?_ hpR.le
  rcases hf.pmOne p hp.pos with h | h <;> rw [h] <;> linarith

/-- `Wirsing.primeDefect` is nondecreasing in the cut-off. -/
@[category API, AMS 11]
theorem primeDefect_mono {f : ℕ → ℝ} (hf : IsPMOneMultiplicative f) {M N : ℕ} (hMN : M ≤ N)
    (t : ℝ) : primeDefect f M t ≤ primeDefect f N t := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hMN)
  · intro p hp _
    exact primeDefect_term_nonneg hf (Finset.mem_filter.1 hp).2 t

/-- `Wirsing.primeDefect` is continuous in the twist. -/
@[category API, AMS 11]
theorem continuous_primeDefect (f : ℕ → ℝ) (N : ℕ) :
    Continuous (primeDefect f N) := by
  classical
  refine continuous_finsetSum _ fun p _ ↦ ?_
  fun_prop

/-- Partial sums over the primes `≤ N` of a nonnegative non-summable prime family tend to
infinity. -/
@[category API, AMS 11]
theorem tendsto_sum_primes_atTop {g : ℕ → ℝ} (hg : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hns : ¬ Summable (fun p : Nat.Primes ↦ g p)) :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, g p) atTop atTop := by
  classical
  set G : ℕ → ℝ := fun n ↦ if n.Prime then g n else 0 with hG
  have hGnn : ∀ n, 0 ≤ G n := by
    intro n
    rw [hG]
    by_cases hn : n.Prime
    · simpa [hn] using hg n hn
    · simp [hn]
  have hinj : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ)) := Subtype.coe_injective
  have hzero : ∀ x ∉ Set.range (fun p : Nat.Primes ↦ (p : ℕ)), G x = 0 := by
    intro x hx
    rw [hG]
    exact if_neg fun hp ↦ hx ⟨⟨x, hp⟩, rfl⟩
  have hcomp : G ∘ (fun p : Nat.Primes ↦ (p : ℕ)) = fun p : Nat.Primes ↦ g p := by
    funext p
    simp [hG, p.2]
  have hnsG : ¬ Summable G := by
    rw [← Function.Injective.summable_iff hinj hzero, hcomp]
    exact hns
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hGnn).1 hnsG
  have hshift : Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range (N + 1), G i) atTop atTop :=
    hdiv.comp (Filter.tendsto_add_atTop_nat 1)
  refine hshift.congr fun N ↦ ?_
  rw [Finset.sum_filter]
  rw [show Finset.Icc 1 N = (Finset.range (N + 1)).filter (fun n ↦ 1 ≤ n) by
    ext n; simp [and_comm]]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hn : n.Prime
  · simp [hG, hn, hn.one_lt.le.trans' (by norm_num : (1:ℕ) ≤ 1)]
  · simp [hG, hn]

/--
**Uniform non-pretentiousness.**  If `f` is at infinite pretentious distance from `n^{it}`
for every real `t`, then for every `T` and every `M` there is an `N₀` beyond which
`D_N(t) ≥ M` *simultaneously* for all `|t| ≤ T`.

This is the input that Halász's theorem needs, and it is the only place where the compactness
of the twist range is used.
-/
@[category API, AMS 11]
theorem exists_forall_primeDefect_ge {f : ℕ → ℝ} (hf : IsPMOneMultiplicative f)
    (hdiv : ∀ t : ℝ, ¬ Summable fun p : Nat.Primes ↦ (1 - f p * Real.cos (t * Real.log p)) / p)
    (T M : ℝ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ t ∈ Set.Icc (-T) T, M ≤ primeDefect f N t := by
  classical
  have key : ∀ t : ℝ, ∃ n : ℕ, M < primeDefect f n t := by
    intro t
    have hd := tendsto_sum_primes_atTop
      (g := fun p ↦ (1 - f p * Real.cos (t * Real.log p)) / p)
      (fun p hp ↦ primeDefect_term_nonneg hf hp t) (hdiv t)
    exact ((hd.eventually_gt_atTop M).exists).imp fun n hn ↦ hn
  choose Nt hNt using key
  set U : ℝ → Set ℝ := fun t ↦ {u : ℝ | M < primeDefect f (Nt t) u} with hU
  have hUmem : ∀ t ∈ Set.Icc (-T) T, U t ∈ 𝓝 t := by
    intro t _
    exact (isOpen_lt continuous_const (continuous_primeDefect f (Nt t))).mem_nhds (hNt t)
  obtain ⟨F, hFsub, hFcov⟩ := isCompact_Icc.elim_nhds_subcover U hUmem
  refine ⟨F.sup Nt, fun N hN t ht ↦ ?_⟩
  obtain ⟨t', ht'F, ht'⟩ : ∃ t' ∈ F, t ∈ U t' := by simpa using hFcov ht
  have h2 : primeDefect f (Nt t') t ≤ primeDefect f N t :=
    primeDefect_mono hf (le_trans (Finset.le_sup ht'F) hN) t
  exact le_of_lt (lt_of_lt_of_le ht' h2)

end Wirsing
