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
# The Turán–Kubilius deficit

`Wirsing.exists_functional_relation` (the Turán–Kubilius route of `Wirsing/OmegaE.lean`) says
$$\Bigl|\sigma(N)E(N) + \sum_{p \in E,\ p \le N}\frac{\sigma(\lfloor N/p\rfloor)}{p}\Bigr|
  \le C\bigl(\sqrt{E(N)+1} + 1\bigr),\qquad E(N) = \sum_{p \le N,\ f(p) = -1}\frac1p .$$

The weights `1/p` on the right have total mass `E(N)`, and the error is `O(\sqrt{E(N)})`.  That
ratio — error over main term — tends to `0` as `E(N) \to \infty`, which is exactly what the
log-weighted relation of `Wirsing/Rigidity.lean` cannot achieve: there the error is `c(M_0)` or
`2\delta\log N` against a main term `\rho\log N`, and the bad primes may be far sparser than
`\log N`.

This file turns that into the *deficit* statement the rigidity argument needs: if `|\sigma(N)|`
is within `\delta` of its limsup `A`, then all but `O(\delta E + \sqrt E)` of the weight `E` sits
on primes `p` at which `\sigma(\lfloor N/p\rfloor)` is within `\rho` of `-s A`, where
`s = \mathrm{sign}\,\sigma(N)`: the sign of `\sigma` flips at almost every bad scale.

*References:*
- [Tu34] Turán, P., On a theorem of Hardy and Ramanujan. J. London Math. Soc. 9 (1934), 274-276.
- [Ku64] Kubilius, J., Probabilistic methods in the theory of numbers. AMS (1964).
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

open scoped Classical in
/-- The weight of the bad primes that are too large to be controlled by the cut-off `M₀`,
i.e. those with `⌊N/p⌋ < M₀`.  It tends to `0` for fixed `M₀`. -/
noncomputable def tailWeight (M₀ N : ℕ) : ℝ :=
  ∑ p ∈ (badPrimesLE f N).filter (fun p ↦ N / p < M₀), (1 : ℝ) / p

open scoped Classical in
@[category API, AMS 11]
theorem tailWeight_nonneg (M₀ N : ℕ) : 0 ≤ tailWeight f M₀ N :=
  Finset.sum_nonneg fun p _ ↦ by positivity

open scoped Classical in
/--
**The Turán–Kubilius deficit.**  Let `A ≥ 0`, let `|σ(M)| ≤ A + δ` for every `M ≥ M₀`, let
`s = ±1` and let `A - δ ≤ s σ(N)`.  Then the `1/p`-weight of the bad primes at which
`-s σ(⌊N/p⌋)` fails to be within `ρ` of `A` is at most
$$\frac{2\delta E(N) + C(\sqrt{E(N)+1}+1) + \mathrm{tail}}{\rho + \delta} + \mathrm{tail}.$$

`C` is the constant of `Wirsing.exists_functional_relation`, so it depends only on `f`.  The
point is the shape: at `\delta \le \varepsilon^2` and `E(N)` large the bound is `\le 3\varepsilon
E(N)`, a small *fraction* of the total weight, with no reference to `\log N`.
-/
@[category API, AMS 11]
theorem exists_sum_tk_deficit_le (hf : IsPMOneMultiplicative f) :
    ∃ C : ℝ, ∀ (A δ s ρ : ℝ) (M₀ N : ℕ), 1 ≤ N → 0 ≤ A → 0 ≤ δ → 0 < ρ → |s| = 1 →
      (∀ M, M₀ ≤ M → |mean f M| ≤ A + δ) → A - δ ≤ s * mean f N →
      ∑ p ∈ (badPrimesLE f N).filter (fun p ↦ -(s * mean f (N / p)) < A - ρ), (1 : ℝ) / p
        ≤ (2 * δ * badPrimeSum f N + C * (Real.sqrt (badPrimeSum f N + 1) + 1)
            + tailWeight f M₀ N) / (ρ + δ) + tailWeight f M₀ N := by
  classical
  obtain ⟨C, hC⟩ := exists_functional_relation f hf
  refine ⟨C, fun A δ s ρ M₀ N hN hA hδ hρ hs hub hsN ↦ ?_⟩
  set B := badPrimesLE f N with hB
  set E := badPrimeSum f N with hE
  set R := C * (Real.sqrt (badPrimeSum f N + 1) + 1) with hR
  set u : ℕ → ℝ := fun p ↦ -(s * mean f (N / p)) with hu
  set w : ℕ → ℝ := fun p ↦ (1 : ℝ) / p with hw
  have hwnn : ∀ p : ℕ, 0 ≤ w p := fun p ↦ by simp only [hw]; positivity
  have hEsum : E = ∑ p ∈ B, w p := by rw [hE, hB, badPrimeSum]
  -- the functional relation, rotated by `s`
  have hrel : (A - δ) * E - R ≤ ∑ p ∈ B, u p * w p := by
    have h := hC N hN
    rw [abs_le] at h
    have hsq : s * s = 1 := by
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hs with h' | h' <;> rw [h'] <;> norm_num
    have hexp : ∑ p ∈ B, u p * w p
        = -(s * ∑ p ∈ B, mean f (N / p) / p) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ ↦ by simp only [hu, hw]; ring
    have hmul : s * (mean f N * E + ∑ p ∈ B, mean f (N / p) / p)
        ≤ |mean f N * E + ∑ p ∈ B, mean f (N / p) / p| := by
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hs with h' | h'
      · rw [h', one_mul]; exact le_abs_self _
      · rw [h', neg_one_mul]; exact neg_le_abs _
    have hmul' : -|mean f N * E + ∑ p ∈ B, mean f (N / p) / p|
        ≤ s * (mean f N * E + ∑ p ∈ B, mean f (N / p) / p) := by
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hs with h' | h'
      · rw [h', one_mul]; exact neg_abs_le _
      · rw [h', neg_one_mul]
        exact neg_le_neg (le_abs_self _)
    have habs : |mean f N * E + ∑ p ∈ B, mean f (N / p) / p| ≤ R := by
      rw [hR, hE, hB]
      exact hC N hN
    have hEnn : 0 ≤ E := by rw [hE]; exact badPrimeSum_nonneg f N
    have hsmean : (A - δ) * E ≤ s * (mean f N * E) := by
      have := mul_le_mul_of_nonneg_right hsN hEnn
      calc (A - δ) * E ≤ s * mean f N * E := this
      _ = s * (mean f N * E) := by ring
    rw [hexp]
    nlinarith [habs, hmul, hmul', hsmean]
  -- the deficit bookkeeping
  set T := B.filter (fun p ↦ N / p < M₀) with hT
  set G := B.filter (fun p ↦ ¬ (N / p < M₀)) with hG
  set F := B.filter (fun p ↦ u p < A - ρ) with hF
  set FG := F.filter (fun p ↦ ¬ (N / p < M₀)) with hFG
  have hTw : tailWeight f M₀ N = ∑ p ∈ T, w p := by
    simp only [tailWeight, hT, hB, hw]
  have hEnn : 0 ≤ E := by rw [hE]; exact badPrimeSum_nonneg f N
  have hTwnn : (0 : ℝ) ≤ ∑ p ∈ T, w p := Finset.sum_nonneg fun p _ ↦ hwnn p
  have hu1 : ∀ p : ℕ, u p ≤ 1 := by
    intro p
    have h1 := abs_mean_le_one f hf (N / p)
    have h2 : |s * mean f (N / p)| ≤ 1 := by rw [abs_mul, hs, one_mul]; exact h1
    simp only [hu]
    linarith [neg_abs_le (s * mean f (N / p))]
  have huG : ∀ p ∈ G, u p ≤ A + δ := by
    intro p hp
    have hmem : M₀ ≤ N / p := by
      simp only [hG, Finset.mem_filter] at hp
      omega
    have h1 := hub (N / p) hmem
    have h2 : |s * mean f (N / p)| ≤ A + δ := by rw [abs_mul, hs, one_mul]; exact h1
    simp only [hu]
    linarith [neg_abs_le (s * mean f (N / p))]
  have hFGG : FG ⊆ G := by
    intro p hp
    simp only [hFG, hF, hG, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  -- the two splittings of `B`
  have hsplitu : ∑ p ∈ B, u p * w p = ∑ p ∈ T, u p * w p + ∑ p ∈ G, u p * w p := by
    rw [hT, hG]
    exact (Finset.sum_filter_add_sum_filter_not B _ (fun p ↦ u p * w p)).symm
  have hsplitw : E = ∑ p ∈ T, w p + ∑ p ∈ G, w p := by
    rw [hEsum, hT, hG]
    exact (Finset.sum_filter_add_sum_filter_not B _ w).symm
  -- the tail contributes at most its weight
  have hTle : ∑ p ∈ T, u p * w p ≤ ∑ p ∈ T, w p := by
    refine Finset.sum_le_sum fun p _ ↦ ?_
    have := mul_le_mul_of_nonneg_right (hu1 p) (hwnn p)
    linarith [this]
  -- the deficit over `G` is small
  have hdefG : ∑ p ∈ G, ((A + δ) * w p - u p * w p) ≤ 2 * δ * E + R + ∑ p ∈ T, w p := by
    have e1 : ∑ p ∈ G, ((A + δ) * w p - u p * w p)
        = (A + δ) * (∑ p ∈ G, w p) - ∑ p ∈ G, u p * w p := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e1]
    have hATw : 0 ≤ (A + δ) * ∑ p ∈ T, w p := by positivity
    nlinarith [hrel, hTle, hsplitu, hsplitw, hATw]
  -- the bad set inside `G`
  have hFGle : (ρ + δ) * ∑ p ∈ FG, w p ≤ 2 * δ * E + R + ∑ p ∈ T, w p := by
    refine le_trans ?_ hdefG
    have hstep : ∑ p ∈ FG, (ρ + δ) * w p ≤ ∑ p ∈ FG, ((A + δ) * w p - u p * w p) := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      have hlt : u p < A - ρ := by
        simp only [hFG, hF, Finset.mem_filter] at hp
        exact hp.1.2
      have := hwnn p
      nlinarith [this, hlt]
    have hmono : ∑ p ∈ FG, ((A + δ) * w p - u p * w p)
        ≤ ∑ p ∈ G, ((A + δ) * w p - u p * w p) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hFGG fun p hp _ ↦ ?_
      have := huG p hp
      nlinarith [hwnn p, this]
    rw [← Finset.mul_sum] at hstep
    linarith [hstep, hmono]
  -- and the whole bad set
  have hFsplit : ∑ p ∈ F, w p = ∑ p ∈ F.filter (fun p ↦ N / p < M₀), w p + ∑ p ∈ FG, w p := by
    rw [hFG]
    exact (Finset.sum_filter_add_sum_filter_not F _ w).symm
  have hFTle : ∑ p ∈ F.filter (fun p ↦ N / p < M₀), w p ≤ ∑ p ∈ T, w p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ ↦ hwnn p
    intro p hp
    simp only [hF, hT, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  have hfinal : ∑ p ∈ FG, w p ≤ (2 * δ * E + R + ∑ p ∈ T, w p) / (ρ + δ) := by
    rw [le_div_iff₀ (by linarith)]
    linarith [hFGle]
  rw [hTw]
  simp only [hw] at hFsplit hFTle hfinal ⊢
  linarith [hFsplit, hFTle, hfinal]

end Wirsing
