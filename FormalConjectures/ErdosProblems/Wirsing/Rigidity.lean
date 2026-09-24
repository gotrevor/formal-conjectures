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

/--
**Step 4 of the Tauberian route: sign stability contradicts `L(N) = o(\log N)`.**

If `s σ(⌊N/k⌋) ≥ A - ρ` for every `k` outside a set of harmonic weight `η`, then the
logarithmic average is large:
$$|L(N)| \ge (A - \rho)(\log N - \eta) - \eta - 2.$$

Together with `L(N) = o(\log N)` this forces `A = \rho`, which is the contradiction that
closes `Wirsing.tendsto_mean_atTop_zero_of_logMean` once steps 2 and 3 produce the good set.
The only inputs are `Wirsing.abs_sum_mean_div_sub_logMean_le` (an `O(1)` identity) and
`Wirsing.log_le_harmonicSum`.
-/
@[category API, AMS 11]
theorem le_abs_logMean_of_sign_stable (hf : IsPMOneMultiplicative f) {A ρ η s : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hs : |s| = 1) (hAρ : 0 ≤ A - ρ) {G : Finset ℕ} (hG : G ⊆ Icc 1 N)
    (hgood : ∀ k ∈ G, A - ρ ≤ s * mean f (N / k))
    (hbad : ∑ k ∈ Icc 1 N \ G, (1 : ℝ) / k ≤ η) :
    (A - ρ) * (Real.log N - η) - η - 2 ≤ |logMean f N| := by
  classical
  set T : ℝ := ∑ k ∈ Icc 1 N, mean f (N / k) / k with hT
  have hknn : ∀ k ∈ Icc 1 N, (0 : ℝ) ≤ 1 / k := fun k _ ↦ by positivity
  have hsplit : ∑ k ∈ Icc 1 N \ G, (1 : ℝ) / k + ∑ k ∈ G, (1 : ℝ) / k = harmonicSum N :=
    Finset.sum_sdiff hG
  have hsplitT : ∑ k ∈ Icc 1 N \ G, s * (mean f (N / k) / k)
      + ∑ k ∈ G, s * (mean f (N / k) / k) = s * T := by
    rw [hT, Finset.mul_sum]
    exact Finset.sum_sdiff hG
  -- the good part
  have hgoodsum : (A - ρ) * ∑ k ∈ G, (1 : ℝ) / k
      ≤ ∑ k ∈ G, s * (mean f (N / k) / k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 (hG hk)).1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hknn' : (0 : ℝ) ≤ 1 / k := by positivity
    have hrw : s * (mean f (N / k) / k) = (s * mean f (N / k)) * (1 / k) := by ring
    rw [hrw, mul_comm (A - ρ), mul_comm (s * mean f (N / k))]
    exact mul_le_mul_of_nonneg_left (hgood k hk) hknn'
  -- the bad part
  have hbadsum : -∑ k ∈ Icc 1 N \ G, (1 : ℝ) / k
      ≤ ∑ k ∈ Icc 1 N \ G, s * (mean f (N / k) / k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 (Finset.mem_sdiff.1 hk).1).1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hknn' : (0 : ℝ) ≤ 1 / k := by positivity
    have habs : |s * (mean f (N / k) / k)| ≤ 1 / k := by
      rw [abs_mul, hs, one_mul, abs_div, Nat.abs_cast]
      have := abs_mean_le_one f hf (N / k)
      rw [div_le_div_iff_of_pos_right (by linarith)]
      exact this
    linarith [(abs_le.1 habs).1]
  have hbadnn : (0 : ℝ) ≤ ∑ k ∈ Icc 1 N \ G, (1 : ℝ) / k :=
    Finset.sum_nonneg fun k hk ↦ hknn k (Finset.mem_sdiff.1 hk).1
  have hlogN : Real.log N ≤ harmonicSum N := log_le_harmonicSum N
  have hlower : (A - ρ) * (Real.log N - η) - η ≤ s * T := by
    have h1 : (A - ρ) * (Real.log N - η) ≤ (A - ρ) * ∑ k ∈ G, (1 : ℝ) / k := by
      refine mul_le_mul_of_nonneg_left ?_ hAρ
      linarith
    linarith [hsplitT, hgoodsum, hbadsum]
  have hTabs : s * T ≤ |T| := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hs with rfl | rfl
    · rw [one_mul]; exact le_abs_self T
    · rw [neg_one_mul]; exact neg_le_abs T
  have hclose := abs_sum_mean_div_sub_logMean_le f hf hN
  rw [← hT] at hclose
  have := abs_sub_abs_le_abs_sub T (logMean f N)
  rw [abs_sub_comm] at hclose
  have h2 : |T| - |logMean f N| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub T (logMean f N)
    rw [abs_sub_comm T (logMean f N)] at this
    linarith
  linarith

/--
**The mean is log-Lipschitz.**  For `1 ≤ M ≤ N`,
$$|\sigma(N) - \sigma(M)| \le \frac{2(N - M)}{N}.$$

In the variable `u = \log N` this makes `σ` Lipschitz with constant `2`, which is the
regularity that turns the rigidity relation into a constraint on `f` itself: two quotients
that are multiplicatively close carry almost the same value of `σ`.
-/
@[category API, AMS 11]
theorem abs_mean_sub_mean_le (hf : IsPMOneMultiplicative f) {M N : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) : |mean f N - mean f M| ≤ 2 * ((N : ℝ) - M) / N := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMNR : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hM1 hMNR
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- the increment of the partial sums
  have hinc : |partialSum f N - partialSum f M| ≤ (N : ℝ) - M := by
    have hsplit : partialSum f N - partialSum f M = ∑ n ∈ Ioc M N, f n := by
      rw [partialSum, partialSum, (by rfl : Icc 1 N = Ioc 0 N), (by rfl : Icc 1 M = Ioc 0 M),
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]
      ring
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcard : ∑ n ∈ Ioc M N, |f n| = ((N - M : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl fun n hn ↦ abs_eq_one_of_one_le f hf
        (by have := (Finset.mem_Ioc.1 hn).1; omega)]
      simp [Nat.card_Ioc]
    rw [hcard]
    have : ((N - M : ℕ) : ℝ) = (N : ℝ) - M := by
      have : (M : ℝ) ≤ (N : ℝ) := hMNR
      push_cast [Nat.cast_sub hMN]
      ring
    rw [this]
  have hSM : |partialSum f M| ≤ (M : ℝ) := abs_partialSum_le f hf M
  -- split the difference of the means
  have hrw : mean f N - mean f M
      = (partialSum f N - partialSum f M) / N - partialSum f M * (((N : ℝ) - M) / (N * M)) := by
    rw [mean_eq_partialSum_div, mean_eq_partialSum_div]
    field_simp
    ring
  rw [hrw]
  have h1 : |(partialSum f N - partialSum f M) / N| ≤ ((N : ℝ) - M) / N := by
    rw [abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hinc hNpos.le
  have h2 : |partialSum f M * (((N : ℝ) - M) / (N * M))| ≤ ((N : ℝ) - M) / N := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((N : ℝ) - M) / (N * M))]
    calc |partialSum f M| * (((N : ℝ) - M) / (N * M))
        ≤ (M : ℝ) * (((N : ℝ) - M) / (N * M)) := by
          refine mul_le_mul_of_nonneg_right hSM (by positivity)
      _ = ((N : ℝ) - M) / N := by field_simp
  have := abs_sub ((partialSum f N - partialSum f M) / N)
    (partialSum f M * (((N : ℝ) - M) / (N * M)))
  have hgoal : 2 * ((N : ℝ) - M) / N = ((N : ℝ) - M) / N + ((N : ℝ) - M) / N := by ring
  rw [hgoal]
  linarith

/--
**A good prime's quotient is itself near-extremal**, with sign `s f(p)`.

This is what licenses iterating `Wirsing.sum_bad_weight_le` at the point `⌊N/p⌋`, and it is
the relation `σ(⌊N/p⌋) \approx s A f(p)` in its usable one-sided form: the rigid structure
along the quotients is a *character*, not a fixed sign.
-/
@[category API, AMS 11]
theorem mean_quotient_near_extremal (hf : IsPMOneMultiplicative f) {A ρ s : ℝ} {N p : ℕ}
    (hp : p.Prime) (hs : |s| = 1) (hgood : A - ρ ≤ s * (f p * mean f (N / p))) :
    |s * f p| = 1 ∧ A - ρ ≤ (s * f p) * mean f (N / p) := by
  refine ⟨?_, by rw [mul_assoc]; exact hgood⟩
  rw [abs_mul, hs, one_mul, abs_eq_one_of_one_le f hf hp.pos]

/--
**Rigidity, iterated once.**  At a near-extremal `N`, a good prime `p` produces a
near-extremal point `⌊N/p⌋` with sign `s f(p)`, so all but `O((\rho\log N + 1)/\rho')` of the
Mertens weight of primes `q` satisfies
`s f(p) f(q) σ(⌊N/(pq)⌋) \ge A - \rho'` — that is, `σ(⌊N/n⌋) \approx s A f(n)` for
`n = pq`, by multiplicativity of `f`.
-/
@[category API, AMS 11]
theorem sum_bad_weight_le_step (hf : IsPMOneMultiplicative f) {A ρ ρ' s : ℝ} {M₀ N p : ℕ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ' : 0 < ρ')
    (hM₀ : 1 ≤ M₀) (hs : |s| = 1)
    (hub : ∀ M, M₀ ≤ M → |mean f M| ≤ A + ρ)
    (hp : p ∈ rigidityPrimes M₀ N)
    (hgood : A - ρ ≤ s * (f p * mean f (N / p))) :
    ∑ q ∈ (rigidityPrimes M₀ (N / p)).filter
        (fun q ↦ s * (f p * (f q * mean f (N / (p * q)))) < A - ρ'), Real.log q / q
      ≤ (2 * ρ * Real.log (N / p : ℕ) + rigidityConst M₀) / (ρ' + ρ) := by
  classical
  obtain ⟨hpp, hq⟩ := (mem_rigidityPrimes hM₀).1 hp
  obtain ⟨hs', hext⟩ := mean_quotient_near_extremal f hf hpp hs hgood
  have hmain := sum_bad_weight_le (A := A) (δ := ρ) (s := s * f p) (ρ := ρ') (M₀ := M₀)
    (N := N / p) f hf hA0 hA1 hρ0 hρ1 hρ' hM₀ hq hs' hub hext
  refine le_trans (le_of_eq (Finset.sum_congr ?_ fun q _ ↦ rfl)) hmain
  refine Finset.filter_congr fun q _ ↦ ?_
  rw [Nat.div_div_eq_div_mul, mul_assoc]

/--
**The window step.**  Two quotients that are multiplicatively close cannot carry opposite
signs of a near-extremal `σ`.

Concretely: if `x, y ∈ \{\pm1\}` and both `s x σ(M') \ge A - \rho` and `s y σ(M) \ge A - \rho`
with `M \le M'`, then `x = y` as soon as `(M' - M)/M' < A - \rho`.

With `x = f(p)`, `y = f(p')` and `M' = \lfloor N/p\rfloor`, `M = \lfloor N/p'\rfloor` this says
that `f` is constant on the good primes of any multiplicative window of ratio
`1/(1 - (A - \rho))`.  It is the mechanism that converts the character structure
`σ(\lfloor N/n\rfloor) \approx sAf(n)` into rigidity of `f` itself, and it uses no property of
the primes, hence no localised form of Mertens' theorem.
-/
@[category API, AMS 11]
theorem eq_of_mean_quotient_close (hf : IsPMOneMultiplicative f) {A ρ s x y : ℝ} {M M' : ℕ}
    (hM : 1 ≤ M) (hMM' : M ≤ M') (hs : |s| = 1) (hx : |x| = 1) (hy : |y| = 1)
    (h1 : A - ρ ≤ s * (x * mean f M')) (h2 : A - ρ ≤ s * (y * mean f M))
    (hclose : ((M' : ℝ) - M) / M' < A - ρ) : x = y := by
  by_contra hne
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMM'R : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hMM'
  have hM'pos : (0 : ℝ) < (M' : ℝ) := by linarith
  -- `y = -x`, since both are signs
  have hyx : y = -x := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hx with rfl | rfl <;>
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hy with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | norm_num
  rw [hyx] at h2
  -- the two bounds add up to a jump of `2(A - ρ)` between `σ(M)` and `σ(M')`
  have hsx : |s * x| = 1 := by rw [abs_mul, hs, hx, one_mul]
  have hjump : 2 * (A - ρ) ≤ (s * x) * (mean f M' - mean f M) := by
    have e1 : s * (x * mean f M') = (s * x) * mean f M' := by ring
    have e2 : s * (-x * mean f M) = -((s * x) * mean f M) := by ring
    rw [e1] at h1
    rw [e2] at h2
    have : (s * x) * (mean f M' - mean f M) = (s * x) * mean f M' - (s * x) * mean f M := by
      ring
    rw [this]
    linarith
  have hle : (s * x) * (mean f M' - mean f M) ≤ |mean f M' - mean f M| := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hsx with h | h
    · rw [h, one_mul]; exact le_abs_self _
    · rw [h, neg_one_mul]; exact neg_le_abs _
  have hlip := abs_mean_sub_mean_le f hf hM hMM'
  have hdiv : 2 * ((M' : ℝ) - M) / M' = 2 * (((M' : ℝ) - M) / M') := by ring
  rw [hdiv] at hlip
  have : ((M' : ℝ) - M) / M' < A - ρ := hclose
  linarith

end Wirsing
