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
public import FormalConjectures.ErdosProblems.Wirsing.Mean

/-!
# Rigidity at a near-extremal point

The first step of the Tauberian half of Wirsing's theorem.  Write `σ(N) = mean f N` and
`A = \limsup |σ|`.  The functional relation
`Wirsing.abs_mean_mul_log_sub_sum_prime_le`,
$$\sigma(N)\log N = \sum_{p \le N} \frac{\log p}{p} f(p)\,\sigma(\lfloor N/p\rfloor) + O(1),$$
has the shape "`σ(N)` is a weighted average of `± σ(\lfloor N/p\rfloor)`", with total weight
`\log N + O(1)` by Mertens.  Taken alone this only gives `A \le A`.  But *at a point where
`|σ(N)|` is within `δ` of the maximum `A`* the average must be nearly extremal in every term,
and that is a genuine constraint: with `s = \pm 1` the sign of `σ(N)`, the **deficit**
$$\Delta = \sum_{p \le N/M_0} \frac{\log p}{p}\bigl(A + \delta - s f(p)\sigma(\lfloor N/p\rfloor)\bigr)$$
has nonnegative terms and satisfies `\Delta \le 2\delta\log N + O_{M_0}(1)`.

Two consequences, both used in the Tauberian step:

* `|σ(\lfloor N/p\rfloor)| \ge A - \rho` for all but a set of primes of weight
  `O(\delta \log N/\rho)`: **the near-maximum is attained at almost every quotient**, which is
  what rules out an oscillating `σ` such as `\cos(\theta\log N)`;
* `f(p) = s \cdot \operatorname{sign}\sigma(\lfloor N/p\rfloor)` for almost every prime, which
  is the relation that forces `f` to be "character-like" and is where `f` being real-valued
  finally enters.

*References:*
- [Hi86] Hildebrand, A., On Wirsing's mean value theorem for multiplicative functions.
  Bull. London Math. Soc. 18 (1986), 147-152.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The additive constant in `Wirsing.sum_deficit_le`, as a function of the cut-off `M₀`. -/
noncomputable def rigidityConst (M₀ : ℕ) : ℝ :=
  Real.log (2 * M₀) + 4 * (Real.log 4 + 8) + (9 + Real.log 4)

/-- The primes `p` for which the quotient `⌊N/p⌋` is still at least the cut-off `M₀`. -/
noncomputable def rigidityPrimes (M₀ N : ℕ) : Finset ℕ :=
  (Icc 1 (N / M₀)).filter Nat.Prime

@[category API, AMS 11]
theorem mem_rigidityPrimes {M₀ N p : ℕ} (hM₀ : 1 ≤ M₀) :
    p ∈ rigidityPrimes M₀ N ↔ p.Prime ∧ M₀ ≤ N / p := by
  rw [rigidityPrimes, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hp⟩
    refine ⟨hp, ?_⟩
    rw [Nat.le_div_iff_mul_le hp.pos]
    calc M₀ * p ≤ (N / M₀) * M₀ := by
          rw [Nat.mul_comm M₀ p]
          exact Nat.mul_le_mul_right _ hp2
      _ ≤ N := Nat.div_mul_le_self _ _
  · rintro ⟨hp, hq⟩
    refine ⟨⟨hp.one_lt.le.trans' (by omega), ?_⟩, hp⟩
    rw [Nat.le_div_iff_mul_le (by omega)]
    rw [Nat.le_div_iff_mul_le hp.pos] at hq
    rwa [Nat.mul_comm]

/-- `rigidityPrimes M₀ N` is contained in the full range of primes of the functional relation. -/
@[category API, AMS 11]
theorem rigidityPrimes_subset {M₀ N : ℕ} (hM₀ : 1 ≤ M₀) :
    rigidityPrimes M₀ N ⊆ (Icc 1 N).filter Nat.Prime := by
  intro p hp
  obtain ⟨hp, hq⟩ := (mem_rigidityPrimes hM₀).1 hp
  rw [mem_filter, mem_Icc]
  refine ⟨⟨hp.pos, ?_⟩, hp⟩
  rw [Nat.le_div_iff_mul_le hp.pos] at hq
  have : 1 * p ≤ M₀ * p := Nat.mul_le_mul_right _ hM₀
  omega

/--
**Rigidity at a near-extremal point.**  If `|σ(M)| ≤ A + δ` for every `M ≥ M₀` and
`|σ(N)| ≥ A - δ`, then the deficit of the functional relation at `N` is `≤ 2δ log N + O(1)`.

Every term of the sum is nonnegative (`Wirsing.rigidity_term_nonneg`), so this says that
`s f(p) σ(⌊N/p⌋)` is within `O(δ)` of the maximum `A` for almost every prime `p`, in the
Mertens weight `log p / p`.
-/
@[category API, AMS 11]
theorem sum_deficit_le (hf : IsPMOneMultiplicative f) {A δ s : ℝ} {M₀ N : ℕ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM₀ : 1 ≤ M₀) (hMN : M₀ ≤ N)
    (hs : |s| = 1)
    (hsN : A - δ ≤ s * mean f N) :
    ∑ p ∈ rigidityPrimes M₀ N, Real.log p / p * (A + δ - s * (f p * mean f (N / p)))
      ≤ 2 * δ * Real.log N + rigidityConst M₀ := by
  classical
  set c₁ : ℝ := Real.log 4 + 8 with hc₁
  set C₀ : ℝ := 9 + Real.log 4 with hC₀
  have hN1 : 1 ≤ N := le_trans hM₀ hMN
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  set P := (Icc 1 N).filter Nat.Prime with hP
  set T := rigidityPrimes M₀ N with hT
  set w : ℕ → ℝ := fun p ↦ Real.log p / p with hw
  set g : ℕ → ℝ := fun p ↦ s * (f p * mean f (N / p)) with hg
  have hwnn : ∀ p ∈ P, 0 ≤ w p := by
    intro p hp
    have hpp : p.Prime := (mem_filter.1 hp).2
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    rw [hw]
    positivity
  have hgabs : ∀ p ∈ P, |g p| ≤ 1 := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    rw [hg, abs_mul, hs, one_mul, abs_mul, abs_eq_one_of_one_le f hf hp1, one_mul]
    exact abs_mean_le_one f hf _
  have hsub : T ⊆ P := rigidityPrimes_subset hM₀
  -- the functional relation, signed by `s`
  have hrel := abs_mean_mul_log_sub_sum_prime_le f hf hN1
  have hkey : (A - δ) * Real.log N ≤ ∑ p ∈ P, w p * g p + C₀ := by
    have h1 : s * (mean f N * Real.log N) ≤ s * (∑ p ∈ P, w p * (f p * mean f (N / p))) + C₀ := by
      have habs := abs_le.1 hrel
      have hmul : s * (mean f N * Real.log N - ∑ p ∈ P, w p * (f p * mean f (N / p))) ≤ C₀ := by
        rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hs with rfl | rfl
        · linarith [habs.2]
        · nlinarith [habs.1]
      linarith [hmul]
    have h2 : (A - δ) * Real.log N ≤ s * (mean f N * Real.log N) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hsN hlogN
    have h3 : s * (∑ p ∈ P, w p * (f p * mean f (N / p))) = ∑ p ∈ P, w p * g p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ ↦ by rw [hg]; ring
    rw [h3] at h1
    linarith
  -- Mertens: the total weight, and the weight of the primes above the cut-off
  have hmer1 := Mertens.abs_sum_log_prime_div_sub_log_le hN1
  have hdiv1 : 1 ≤ N / M₀ := Nat.one_le_div_iff (by omega) |>.2 hMN
  have hmer2 := Mertens.abs_sum_log_prime_div_sub_log_le hdiv1
  have hWP : ∑ p ∈ P, w p ≤ Real.log N + c₁ := by
    have := (abs_le.1 hmer1).2
    rw [hP, hw]
    linarith
  have hlow : Real.log N - Real.log (2 * M₀) ≤ Real.log ((N / M₀ : ℕ) : ℝ) := by
    have hM₀R : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
    have hcast : (N : ℝ) / (2 * M₀) ≤ ((N / M₀ : ℕ) : ℝ) := by
      have hnat : N ≤ 2 * (M₀ * (N / M₀)) := by
        have h1 := Nat.div_add_mod N M₀
        have h2 : N % M₀ < M₀ := Nat.mod_lt _ (by omega)
        have h3 : M₀ ≤ M₀ * (N / M₀) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have : (N : ℝ) ≤ 2 * (M₀ * ((N / M₀ : ℕ) : ℝ)) := by exact_mod_cast hnat
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hpos : (0 : ℝ) < (N : ℝ) / (2 * M₀) := by positivity
    calc Real.log N - Real.log (2 * M₀) = Real.log ((N : ℝ) / (2 * M₀)) := by
          rw [Real.log_div (by linarith) (by positivity)]
      _ ≤ _ := Real.log_le_log hpos hcast
  have hWT : Real.log N - Real.log (2 * M₀) - c₁ ≤ ∑ p ∈ T, w p := by
    have := (abs_le.1 hmer2).1
    rw [hT, rigidityPrimes, hw]
    linarith
  have hWTle : ∑ p ∈ T, w p ≤ Real.log N + c₁ := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ hwnn p hp) hWP
  -- split off the primes above the cut-off
  have hsplit : ∑ p ∈ P \ T, w p * g p + ∑ p ∈ T, w p * g p = ∑ p ∈ P, w p * g p :=
    Finset.sum_sdiff hsub
  have htail : ∑ p ∈ P \ T, w p * g p ≤ Real.log (2 * M₀) + 2 * c₁ := by
    have hle : ∑ p ∈ P \ T, w p * g p ≤ ∑ p ∈ P \ T, w p := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      have hpP : p ∈ P := (Finset.mem_sdiff.1 hp).1
      have := (abs_le.1 (hgabs p hpP)).2
      nlinarith [hwnn p hpP]
    have hsum : ∑ p ∈ P \ T, w p + ∑ p ∈ T, w p = ∑ p ∈ P, w p := Finset.sum_sdiff hsub
    linarith
  -- the deficit
  have hdef : ∑ p ∈ T, w p * (A + δ - g p) = (A + δ) * ∑ p ∈ T, w p - ∑ p ∈ T, w p * g p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  have hc₁pos : 0 < c₁ := by
    rw [hc₁]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hAδ : (A + δ) * ∑ p ∈ T, w p ≤ (A + δ) * (Real.log N + c₁) :=
    mul_le_mul_of_nonneg_left hWTle (by linarith)
  have hfinal : ∑ p ∈ T, w p * (A + δ - g p)
      ≤ 2 * δ * Real.log N + Real.log (2 * M₀) + 4 * c₁ + C₀ := by
    rw [hdef]
    nlinarith [hkey, hsplit, htail, hAδ]
  rw [rigidityConst, hT] at *
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_)) (by linarith [hfinal])
  rw [hw, hg]

/-- Every term of the deficit of `Wirsing.sum_deficit_le` is nonnegative. -/
@[category API, AMS 11]
theorem rigidity_term_nonneg (hf : IsPMOneMultiplicative f) {A δ s : ℝ} {M₀ N p : ℕ}
    (hM₀ : 1 ≤ M₀) (hs : |s| = 1) (hub : ∀ M, M₀ ≤ M → |mean f M| ≤ A + δ)
    (hp : p ∈ rigidityPrimes M₀ N) :
    0 ≤ Real.log p / p * (A + δ - s * (f p * mean f (N / p))) := by
  obtain ⟨hpp, hq⟩ := (mem_rigidityPrimes hM₀).1 hp
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
  have hw : 0 ≤ Real.log p / p := by positivity
  refine mul_nonneg hw ?_
  have h1 : |s * (f p * mean f (N / p))| ≤ A + δ := by
    rw [abs_mul, hs, one_mul, abs_mul, abs_eq_one_of_one_le f hf hpp.pos, one_mul]
    exact hub _ hq
  linarith [(abs_le.1 h1).2]

/--
**Almost every quotient is near-extremal.**  The primes at which the functional relation
loses more than `ρ` carry weight `O((\delta\log N + 1)/\rho)`.

Applied at a point `N` where `|σ(N)|` is within `δ` of `A = \limsup|σ|`, and with `ρ`
of order `\sqrt δ`, this says that `s f(p)σ(\lfloor N/p\rfloor) \ge A - \rho` — hence both
`|σ(\lfloor N/p\rfloor)| \ge A - \rho` and `f(p) = s\cdot\operatorname{sign}
\sigma(\lfloor N/p\rfloor)` — for all primes outside a set of Mertens weight
`O(\sqrt\delta\log N)`.
-/
@[category API, AMS 11]
theorem sum_bad_weight_le (hf : IsPMOneMultiplicative f) {A δ s ρ : ℝ} {M₀ N : ℕ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hM₀ : 1 ≤ M₀) (hMN : M₀ ≤ N) (hs : |s| = 1)
    (hub : ∀ M, M₀ ≤ M → |mean f M| ≤ A + δ)
    (hsN : A - δ ≤ s * mean f N) :
    ∑ p ∈ (rigidityPrimes M₀ N).filter (fun p ↦ s * (f p * mean f (N / p)) < A - ρ),
        Real.log p / p
      ≤ (2 * δ * Real.log N + rigidityConst M₀) / (ρ + δ) := by
  classical
  set B := (rigidityPrimes M₀ N).filter (fun p ↦ s * (f p * mean f (N / p)) < A - ρ) with hB
  have hBsub : B ⊆ rigidityPrimes M₀ N := Finset.filter_subset _ _
  have hlow : (ρ + δ) * ∑ p ∈ B, Real.log p / p
      ≤ ∑ p ∈ B, Real.log p / p * (A + δ - s * (f p * mean f (N / p))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hpT, hplt⟩ := mem_filter.1 hp
    obtain ⟨hpp, -⟩ := (mem_rigidityPrimes hM₀).1 hpT
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hw : 0 ≤ Real.log p / p := by positivity
    rw [mul_comm (ρ + δ)]
    refine mul_le_mul_of_nonneg_left (by linarith) hw
  have hrest : ∑ p ∈ B, Real.log p / p * (A + δ - s * (f p * mean f (N / p)))
      ≤ ∑ p ∈ rigidityPrimes M₀ N,
          Real.log p / p * (A + δ - s * (f p * mean f (N / p))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBsub fun p hp _ ↦
      rigidity_term_nonneg f hf hM₀ hs hub hp
  have hmain := sum_deficit_le f hf hA0 hA1 hδ0 hδ1 hM₀ hMN hs hsN
  rw [le_div_iff₀ (by linarith), mul_comm]
  linarith

end Wirsing
