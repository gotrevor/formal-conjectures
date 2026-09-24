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

open scoped Classical in
/--
For `n ≤ N`, every prime factor of `n` is at most `N`, so `ω_E n` counts the divisors of `n`
among the primes of `E` up to `N`.
-/
@[category API, AMS 11]
theorem omegaBad_eq_card_filter_badPrimesLE {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    omegaBad f n = #{p ∈ badPrimesLE f N | p ∣ n} := by
  rw [omegaBad, badPrimesLE, Finset.filter_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨hp, hdvd, -⟩, hfp⟩
    exact ⟨(Nat.le_of_dvd (by omega) hdvd).trans hnN, ⟨hp, hfp⟩, hdvd⟩
  · rintro ⟨-, ⟨hp, hfp⟩, hdvd⟩
    exact ⟨⟨hp, hdvd, by omega⟩, hfp⟩

open scoped Classical in
/-- Double counting: `∑_{n ≤ N} ω_E(n) = ∑_{p ∈ E, p ≤ N} ⌊N/p⌋`. -/
@[category API, AMS 11]
theorem sum_omegaBad_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, omegaBad f n = ∑ p ∈ badPrimesLE f N, N / p := by
  have h1 : ∀ n ∈ Icc 1 N, omegaBad f n = ∑ p ∈ badPrimesLE f N, if p ∣ n then 1 else 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [omegaBad_eq_card_filter_badPrimesLE f hn.1 hn.2, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]

open scoped Classical in
@[category API, AMS 11]
theorem mem_badPrimesLE_iff {p N : ℕ} :
    p ∈ badPrimesLE f N ↔ p ≤ N ∧ p.Prime ∧ f p = -1 := by
  rw [badPrimesLE]
  simp

open scoped Classical in
@[category API, AMS 11]
theorem sum_omegaBad_cast (N : ℕ) :
    ∑ n ∈ Icc 1 N, (omegaBad f n : ℝ) = ∑ p ∈ badPrimesLE f N, ((N / p : ℕ) : ℝ) := by
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_omegaBad_eq f N]

open scoped Classical in
/-- `N · E(N)` is an upper bound for `∑_{n ≤ N} ω_E(n)`. -/
@[category API, AMS 11]
theorem sum_omegaBad_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (omegaBad f n : ℝ) ≤ N * badPrimeSum f N := by
  rw [sum_omegaBad_cast, badPrimeSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp0 : 0 < p := (mem_badPrimesLE_iff f |>.1 hp).2.1.pos
  calc ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    _ = N * (1 / p) := by ring

open scoped Classical in
/-- `N · E(N)` exceeds `∑_{n ≤ N} ω_E(n)` by at most the number of primes involved. -/
@[category API, AMS 11]
theorem le_sum_omegaBad (N : ℕ) :
    N * badPrimeSum f N - #(badPrimesLE f N) ≤ ∑ n ∈ Icc 1 N, (omegaBad f n : ℝ) := by
  rw [sum_omegaBad_cast, badPrimeSum, Finset.mul_sum, sub_le_iff_le_add,
    Finset.card_eq_sum_ones (badPrimesLE f N), Nat.cast_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp0 : 0 < p := (mem_badPrimesLE_iff f |>.1 hp).2.1.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hltN : N < (N / p + 1) * p := by
    have h1 := Nat.div_add_mod N p
    have h2 := Nat.mod_lt N hp0
    calc N = p * (N / p) + N % p := h1.symm
      _ < p * (N / p) + p := by omega
      _ = (N / p + 1) * p := by ring
  have hlt : (N : ℝ) < ((N / p : ℕ) + 1 : ℝ) * p := by exact_mod_cast hltN
  rw [mul_one_div, div_le_iff₀ hpR]
  push_cast
  nlinarith [hlt]

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
