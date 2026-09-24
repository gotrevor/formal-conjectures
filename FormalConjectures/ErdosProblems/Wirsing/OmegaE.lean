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
public import FormalConjectures.ErdosProblems.Wirsing.Identity

/-!
# The `ω_E` route to the divergent case of Wirsing's theorem

Let `f : ℕ → ℝ` be multiplicative with values in `{±1}` and let
`E = {p prime : f p = -1}`.  The hypothesis `∑_p (1 - f p)/p = ∞` of the hard half of
Wirsing's theorem says exactly that `E(N) = ∑_{p ∈ E, p ≤ N} 1/p → ∞`.

Writing `ω_E n` for the number of primes of `E` dividing `n`, two elementary estimates
combine into a functional relation for the normalised partial sums `σ(N) = S(N)/N`:

* the Turán–Kubilius inequality `∑_{n≤N} (ω_E n - E(N))² ≪ N · E(N)`;
* the hyperbola identity `∑_{n≤N} f(n) ω_E(n) = ∑_{p ∈ E, p ≤ N} f(p) S(N/p) + O(N)`.

Since `f p = -1` on `E`, Cauchy–Schwarz turns these into
`σ(N) + E(N)⁻¹ ∑_{p ∈ E, p ≤ N} σ(N/p)/p = O(E(N)^{-1/2})`, from which `σ(N) → 0`.

This route needs no Mertens asymptotic, which is why it is preferred over Wirsing's
log-weighted integral equation.  See `PENDING_WORK.md`.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The partial sums `S(N) = ∑_{n ≤ N} f(n)`. -/
noncomputable def partialSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, f n

@[category API, AMS 11]
theorem mean_eq_partialSum_div (N : ℕ) : mean f N = partialSum f N / N := rfl

open scoped Classical in
/-- The primes `p ≤ N` with `f p = -1`. -/
noncomputable def badPrimesLE (N : ℕ) : Finset ℕ :=
  {p ∈ Finset.range (N + 1) | p.Prime ∧ f p = -1}

open scoped Classical in
/-- `ω_E n`: the number of primes `p ∣ n` with `f p = -1`. -/
noncomputable def omegaBad (n : ℕ) : ℕ := #{p ∈ n.primeFactors | f p = -1}

/-- `E(N) = ∑_{p ≤ N, f p = -1} 1/p`. -/
noncomputable def badPrimeSum (N : ℕ) : ℝ := ∑ p ∈ badPrimesLE f N, (1 : ℝ) / p

open scoped Classical in
/-- The `ℕ`-indexed extension of `pretentiousSeries f` by zero off the primes. -/
noncomputable def pretentiousTerm (n : ℕ) : ℝ := if n.Prime then (1 - f n) / n else 0

open scoped Classical in
@[category API, AMS 11]
theorem pretentiousTerm_nonneg (hf : IsPMOneMultiplicative f) (n : ℕ) :
    0 ≤ pretentiousTerm f n := by
  rw [pretentiousTerm]
  split
  · rename_i hp
    rcases hf.pmOne n hp.one_lt.le with h1 | h1 <;> rw [h1] <;> positivity
  · exact le_rfl

open scoped Classical in
@[category API, AMS 11]
theorem sum_range_pretentiousTerm (hf : IsPMOneMultiplicative f) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), pretentiousTerm f i = 2 * badPrimeSum f N := by
  have key : ∀ i ∈ Finset.range (N + 1),
      pretentiousTerm f i = if i.Prime ∧ f i = -1 then 2 / (i : ℝ) else 0 := by
    intro i _
    rw [pretentiousTerm]
    by_cases hp : i.Prime
    · rcases hf.pmOne i hp.one_lt.le with h1 | h1
      · rw [if_pos hp, if_neg (by rintro ⟨-, h2⟩; rw [h1] at h2; norm_num at h2), h1]
        simp
      · rw [if_pos hp, if_pos ⟨hp, h1⟩, h1]
        norm_num
    · rw [if_neg hp, if_neg (by tauto)]
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter, badPrimeSum, badPrimesLE,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/--
The divergence hypothesis of the hard half of Wirsing's theorem says exactly that
`E(N) → ∞`, because `1 - f p ∈ {0, 2}` for a `±1`-valued `f`.
-/
@[category API, AMS 11]
theorem tendsto_badPrimeSum_atTop_of_not_summable (hf : IsPMOneMultiplicative f)
    (h : ¬ Summable (pretentiousSeries f)) :
    Tendsto (badPrimeSum f) atTop atTop := by
  classical
  have hinj : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ)) := Subtype.coe_injective
  have hzero : ∀ x ∉ Set.range (fun p : Nat.Primes ↦ (p : ℕ)), pretentiousTerm f x = 0 := by
    intro x hx
    rw [pretentiousTerm, if_neg]
    exact fun hp ↦ hx ⟨⟨x, hp⟩, rfl⟩
  have hcomp : pretentiousTerm f ∘ (fun p : Nat.Primes ↦ (p : ℕ)) = pretentiousSeries f := by
    funext p
    simp [pretentiousTerm, pretentiousSeries, p.2]
  have hns : ¬ Summable (pretentiousTerm f) := by
    rw [← Function.Injective.summable_iff hinj hzero, hcomp]
    exact h
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (pretentiousTerm_nonneg f hf)).1 hns
  have hstep : Tendsto (fun N : ℕ ↦ N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hshift : Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range (N + 1), pretentiousTerm f i)
      atTop atTop := hdiv.comp hstep
  have h2 : Tendsto (fun N : ℕ ↦ 2 * badPrimeSum f N) atTop atTop :=
    hshift.congr fun N ↦ sum_range_pretentiousTerm f hf N
  exact (Filter.Tendsto.const_mul_atTop (r := (2 : ℝ)⁻¹) (by norm_num) h2).congr
    fun N ↦ by ring

/--
The Turán–Kubilius inequality for the prime set `E = {p : f p = -1}`:
`∑_{n ≤ N} (ω_E n - E(N))² ≪ N (E(N) + 1)`.

Elementary second moment computation: expand the square and count multiples of `p` and of
`p q` using `⌊N/p⌋ = N/p + O(1)`.
-/
@[category API, AMS 11]
theorem exists_turan_kubilius :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Icc 1 N, ((omegaBad f n : ℝ) - badPrimeSum f N) ^ 2
      ≤ C * N * (badPrimeSum f N + 1) := by
  sorry

/--
The hyperbola estimate: `∑_{n ≤ N} f(n) ω_E(n) = ∑_{p ∈ E, p ≤ N} f(p) S(N/p) + O(N)`.

The error comes only from the `n ≤ N` divisible by `p²`, of which there are at most `N/p²`,
and `∑_p 1/p² < ∞`.
-/
@[category API, AMS 11]
theorem exists_sum_mul_omegaBad (hf : IsPMOneMultiplicative f) :
    ∃ C : ℝ, ∀ N : ℕ, |(∑ n ∈ Icc 1 N, f n * omegaBad f n)
      - ∑ p ∈ badPrimesLE f N, f p * partialSum f (N / p)| ≤ C * N := by
  sorry

/--
The functional relation: with `σ(N) = S(N)/N`,
`|σ(N) · E(N) + ∑_{p ∈ E, p ≤ N} σ(N/p)/p| ≪ √(E(N) + 1) + 1`.

Obtained from `exists_turan_kubilius` by Cauchy–Schwarz together with
`exists_sum_mul_omegaBad` and `f p = -1` on `E`.
-/
@[category API, AMS 11]
theorem exists_functional_relation (hf : IsPMOneMultiplicative f) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |mean f N * badPrimeSum f N
        + ∑ p ∈ badPrimesLE f N, mean f (N / p) / p|
        ≤ C * (Real.sqrt (badPrimeSum f N + 1) + 1) := by
  sorry

end Wirsing
