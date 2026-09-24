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
public import FormalConjectures.ErdosProblems.Wirsing.Rigidity

/-!
# Choosing the extremal point so that the bad weight is bounded

`Wirsing.sum_bad_weight_le` bounds the Mertens weight of the primes at which the functional
relation loses more than `ρ` by
$$\frac{2\delta\log N + c(M_0)}{\rho + \delta},$$
where `δ` measures how far `|σ(N)|` is from the supremum `B = \sup_{M \ge M_0}|σ(M)|`.  Used
naively — pick `δ` first, then `N` — the term `2δ\log N` is only `o(\log N)`, so the bad set
can have weight `ε\log N`.  That is too weak for every later step: the primes are then only
`ε\log N`-dense in the logarithmic scale, and `σ` is Lipschitz with constant `2`, so nothing
can be said at a fixed scale.

The fix is to choose `N` and `δ` *together*, minimising the product.  Set
$$\operatorname{def}(N) = (B - |σ(N)|)\log N \ \ge 0 .$$
This is a nonnegative real number for every `N ≥ M_0`, so its infimum `D` over `N ≥ M_0` is a
finite real, and some `N` comes within `ε` of it.  At that `N`,
`δ = B - |σ(N)|` satisfies `δ\log N ≤ D + ε`, and the bad weight is at most
$$\frac{2(D + \varepsilon) + c(M_0)}{\rho},$$
a bound **independent of `N`**.  Nothing is assumed about `f` beyond `|σ| ≤ 1`; the
variational choice is what removes the `\log N`.

This is the quantitative form of the trivial observation that `\limsup|σ|` cannot be
approached at *every* rate: whatever the rate is, the deficit measured against `\log N` has a
finite infimum.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The values `|σ(M)|` for `M ≥ M₀`. -/
def meanAbsSet (M₀ : ℕ) : Set ℝ := {x | ∃ M, M₀ ≤ M ∧ |mean f M| = x}

@[category API, AMS 11]
theorem meanAbsSet_nonempty (M₀ : ℕ) : (meanAbsSet f M₀).Nonempty :=
  ⟨|mean f M₀|, M₀, le_rfl, rfl⟩

@[category API, AMS 11]
theorem meanAbsSet_bddAbove (hf : IsPMOneMultiplicative f) (M₀ : ℕ) :
    BddAbove (meanAbsSet f M₀) := by
  refine ⟨1, ?_⟩
  rintro x ⟨M, -, rfl⟩
  exact abs_mean_le_one f hf M

/-- `B = \sup_{M \ge M_0}|σ(M)|`, the supremum that the extremal point approaches. -/
noncomputable def meanSup (M₀ : ℕ) : ℝ := sSup (meanAbsSet f M₀)

@[category API, AMS 11]
theorem abs_mean_le_meanSup (hf : IsPMOneMultiplicative f) {M₀ M : ℕ} (hM : M₀ ≤ M) :
    |mean f M| ≤ meanSup f M₀ :=
  le_csSup (meanAbsSet_bddAbove f hf M₀) ⟨M, hM, rfl⟩

@[category API, AMS 11]
theorem meanSup_nonneg (hf : IsPMOneMultiplicative f) (M₀ : ℕ) : 0 ≤ meanSup f M₀ :=
  le_trans (abs_nonneg _) (abs_mean_le_meanSup f hf (M := M₀) le_rfl)

@[category API, AMS 11]
theorem meanSup_le_one (hf : IsPMOneMultiplicative f) (M₀ : ℕ) : meanSup f M₀ ≤ 1 :=
  csSup_le (meanAbsSet_nonempty f M₀) (by rintro x ⟨M, -, rfl⟩; exact abs_mean_le_one f hf M)

/-- The deficit of `N` against the supremum, weighted by `\log N`. -/
noncomputable def deficit (M₀ N : ℕ) : ℝ := (meanSup f M₀ - |mean f N|) * Real.log N

@[category API, AMS 11]
theorem deficit_nonneg (hf : IsPMOneMultiplicative f) {M₀ N : ℕ} (hN1 : 1 ≤ N)
    (hN : M₀ ≤ N) : 0 ≤ deficit f M₀ N := by
  have h1 : 0 ≤ meanSup f M₀ - |mean f N| := by
    linarith [abs_mean_le_meanSup f hf hN]
  have h2 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hN1)
  exact mul_nonneg h1 h2

/-- The values of the weighted deficit over the admissible range. -/
def deficitSet (M₀ : ℕ) : Set ℝ := {x | ∃ N, M₀ ≤ N ∧ deficit f M₀ N = x}

/-- `D`, the infimum of the weighted deficit.  Finite because the set is a nonempty set of
nonnegative reals. -/
noncomputable def deficitInf (M₀ : ℕ) : ℝ := sInf (deficitSet f M₀)

@[category API, AMS 11]
theorem deficitSet_nonempty (M₀ : ℕ) : (deficitSet f M₀).Nonempty :=
  ⟨deficit f M₀ M₀, M₀, le_rfl, rfl⟩

@[category API, AMS 11]
theorem deficitSet_bddBelow (hf : IsPMOneMultiplicative f) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    BddBelow (deficitSet f M₀) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, hN, rfl⟩
  exact deficit_nonneg f hf (le_trans hM₀ hN) hN

@[category API, AMS 11]
theorem deficitInf_nonneg (hf : IsPMOneMultiplicative f) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    0 ≤ deficitInf f M₀ :=
  le_csInf (deficitSet_nonempty f M₀) (by
    rintro x ⟨N, hN, rfl⟩
    exact deficit_nonneg f hf (le_trans hM₀ hN) hN)

/--
**The variational choice of the extremal point.**  For every `ε > 0` there is `N ≥ M₀` whose
weighted deficit is within `ε` of the infimum.
-/
@[category API, AMS 11]
theorem exists_deficit_le {M₀ : ℕ} {ε : ℝ} (hε : 0 < ε) : ∃ N, M₀ ≤ N ∧ deficit f M₀ N ≤ deficitInf f M₀ + ε := by
  obtain ⟨x, hx, hlt⟩ := Real.lt_sInf_add_pos (deficitSet_nonempty f M₀) hε
  obtain ⟨N, hN, rfl⟩ := hx
  exact ⟨N, hN, hlt.le⟩

/--
**The bad weight is bounded, with no `\log N`.**

At the variationally chosen point the primes at which the functional relation loses more than
`ρ` carry Mertens weight at most `(2(D + ε) + c(M_0))/ρ`, a constant independent of `N`.
The sign `s` is the sign of `σ(N)`, and `|σ(M)| ≤ B` holds for *every* `M ≥ M_0`, with no
slack: that is what makes the later Lipschitz arguments usable at a fixed scale.
-/
@[category API, AMS 11]
theorem exists_sum_bad_weight_le_const (hf : IsPMOneMultiplicative f) {M₀ : ℕ} (hM₀ : 1 ≤ M₀)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ (N : ℕ) (s : ℝ), M₀ ≤ N ∧ |s| = 1 ∧ 0 ≤ meanSup f M₀ - s * mean f N ∧
      (meanSup f M₀ - s * mean f N) * Real.log N ≤ deficitInf f M₀ + ε ∧
      ∑ p ∈ (rigidityPrimes M₀ N).filter
          (fun p ↦ s * (f p * mean f (N / p)) < meanSup f M₀ - ρ), Real.log p / p
        ≤ (2 * (deficitInf f M₀ + ε) + rigidityConst M₀) / ρ := by
  classical
  obtain ⟨N, hN, hdef⟩ := exists_deficit_le f hε
  have hN1 : 1 ≤ N := le_trans hM₀ hN
  set s : ℝ := if 0 ≤ mean f N then 1 else -1 with hsdef
  have hs : |s| = 1 := by
    rw [hsdef]; split <;> norm_num
  have hsmean : s * mean f N = |mean f N| := by
    rw [hsdef]
    split
    · rw [one_mul, abs_of_nonneg ‹_›]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge ‹_›)]
  set A : ℝ := meanSup f M₀ with hA
  set δ : ℝ := A - |mean f N| with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]; linarith [abs_mean_le_meanSup f hf hN]
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    linarith [meanSup_le_one f hf M₀, abs_nonneg (mean f N)]
  have hA0 : 0 ≤ A := meanSup_nonneg f hf M₀
  have hA1 : A ≤ 1 := meanSup_le_one f hf M₀
  have hdef' : δ * Real.log N ≤ deficitInf f M₀ + ε := by
    rw [hδ]; exact hdef
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hub : ∀ M, M₀ ≤ M → |mean f M| ≤ A + δ := fun M hM ↦ by
    have := abs_mean_le_meanSup f hf hM
    rw [hA]; linarith
  have hsN : A - δ ≤ s * mean f N := by rw [hsmean, hδ]; ring_nf; rfl
  have hmain := sum_bad_weight_le f hf hA0 hA1 hδ0 hδ1 hρ hM₀ hN hs hub hsN
  have hC : 0 ≤ rigidityConst M₀ := by
    have h2 : (1 : ℝ) ≤ 2 * (M₀ : ℝ) := by
      have : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
      linarith
    have := Real.log_nonneg h2
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [rigidityConst]
    linarith
  refine ⟨N, s, hN, hs, by rw [hsmean, ← hδ]; linarith, by rw [hsmean, ← hδ]; exact hdef', ?_⟩
  refine hmain.trans ?_
  have hD : 0 ≤ deficitInf f M₀ := deficitInf_nonneg f hf hM₀
  have hnum : 2 * δ * Real.log N + rigidityConst M₀
      ≤ 2 * (deficitInf f M₀ + ε) + rigidityConst M₀ := by
    have : 2 * (δ * Real.log N) ≤ 2 * (deficitInf f M₀ + ε) := by linarith
    linarith [this]
  have hnum0 : (0 : ℝ) ≤ 2 * (deficitInf f M₀ + ε) + rigidityConst M₀ := by linarith
  have hstep1 : (2 * δ * Real.log N + rigidityConst M₀) / (ρ + δ)
      ≤ (2 * (deficitInf f M₀ + ε) + rigidityConst M₀) / (ρ + δ) :=
    div_le_div_of_nonneg_right hnum (by linarith)
  have hstep2 : (2 * (deficitInf f M₀ + ε) + rigidityConst M₀) / (ρ + δ)
      ≤ (2 * (deficitInf f M₀ + ε) + rigidityConst M₀) / ρ :=
    div_le_div_of_nonneg_left hnum0 hρ (by linarith)
  linarith

end Wirsing
