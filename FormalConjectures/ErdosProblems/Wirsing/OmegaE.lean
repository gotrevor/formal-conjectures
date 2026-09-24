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

open scoped Classical in
@[category API, AMS 11]
theorem card_filter_dvd_Icc (N d : ℕ) : #{n ∈ Icc 1 N | d ∣ n} = N / d := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

open scoped Classical in
/--
The number of `n ≤ N` divisible by both of the primes `p` and `q` is at most `N/(pq)`, plus
`N/p` on the diagonal `p = q`.
-/
@[category API, AMS 11]
theorem sum_indicator_dvd_le {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Icc 1 N, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      ≤ (if p = q then (N : ℝ) / p else 0) + (N : ℝ) / (p * q) := by
  have hmul : ∀ n : ℕ, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      = if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
    intro n
    by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun n _ ↦ hmul n, Finset.sum_boole]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  by_cases hpq : p = q
  · subst hpq
    have : {n ∈ Icc 1 N | p ∣ n ∧ p ∣ n} = {n ∈ Icc 1 N | p ∣ n} := by
      simp
    rw [this, card_filter_dvd_Icc, if_pos rfl]
    have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have h2 : (0 : ℝ) ≤ (N : ℝ) / (p * p) := by positivity
    linarith
  · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
    have : {n ∈ Icc 1 N | p ∣ n ∧ q ∣ n} = {n ∈ Icc 1 N | p * q ∣ n} := by
      refine Finset.filter_congr fun n _ ↦ ?_
      exact ⟨fun h ↦ hcop.mul_dvd_of_dvd_of_dvd h.1 h.2,
        fun h ↦ ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩⟩
    rw [this, card_filter_dvd_Icc, if_neg hpq]
    have h1 : ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / (p * q) := by
      rw [← Nat.cast_mul]; exact Nat.cast_div_le
    simpa using h1

open scoped Classical in
/-- The second moment `∑_{n ≤ N} ω_E(n)² ≤ N·E(N) + N·E(N)²`. -/
@[category API, AMS 11]
theorem sum_omegaBad_sq_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((omegaBad f n : ℝ)) ^ 2
      ≤ N * badPrimeSum f N + N * badPrimeSum f N ^ 2 := by
  set P := badPrimesLE f N with hP
  have hexp : ∀ n ∈ Icc 1 N, ((omegaBad f n : ℝ)) ^ 2
      = ∑ p ∈ P, ∑ q ∈ P, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hcard : ((omegaBad f n : ℕ) : ℝ) = ∑ p ∈ P, (if p ∣ n then (1 : ℝ) else 0) := by
      rw [omegaBad_eq_card_filter_badPrimesLE f hn.1 hn.2, Finset.sum_boole]
    rw [sq, hcard, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hswap : ∀ p ∈ P, ∑ n ∈ Icc 1 N, ∑ q ∈ P,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      = ∑ q ∈ P, ∑ n ∈ Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) :=
    fun p _ ↦ Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  have hbound : ∀ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      ≤ ∑ q ∈ P, ((if p = q then (N : ℝ) / p else 0) + (N : ℝ) / (p * q)) := by
    intro p hp
    refine Finset.sum_le_sum fun q hq ↦ ?_
    exact sum_indicator_dvd_le (mem_badPrimesLE_iff f |>.1 hp).2.1
      (mem_badPrimesLE_iff f |>.1 hq).2.1
  refine (Finset.sum_le_sum hbound).trans ?_
  have hsplit : ∀ p ∈ P, ∑ q ∈ P, ((if p = q then (N : ℝ) / p else 0) + (N : ℝ) / (p * q))
      = (N : ℝ) / p + (N : ℝ) / p * ∑ q ∈ P, (1 : ℝ) / q := by
    intro p hp
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq P p (fun _ ↦ (N : ℝ) / p), if_pos hp,
      Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun q _ ↦ ?_)
    rw [div_mul_eq_div_div]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hE : ∑ p ∈ P, (N : ℝ) / p = N * badPrimeSum f N := by
    rw [badPrimeSum, ← hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [mul_one_div]
  rw [hE, badPrimeSum, ← hP]
  ring_nf
  rfl

/--
The Turán–Kubilius inequality for the prime set `E = {p : f p = -1}`:
`∑_{n ≤ N} (ω_E n - E(N))² ≪ N (E(N) + 1)`.

Elementary second moment computation: expand the square and count multiples of `p` and of
`p q` using `⌊N/p⌋ = N/p + O(1)`.
-/
@[category API, AMS 11]
theorem badPrimeSum_nonneg (N : ℕ) : 0 ≤ badPrimeSum f N :=
  Finset.sum_nonneg fun p _ ↦ by positivity

open scoped Classical in
@[category API, AMS 11]
theorem card_badPrimesLE_le (N : ℕ) : (#(badPrimesLE f N) : ℝ) ≤ N := by
  have hsub : badPrimesLE f N ⊆ Icc 1 N := by
    intro p hp
    rw [mem_badPrimesLE_iff] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.1.one_lt.le, hp.1⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  exact_mod_cast this.trans_eq (by omega)

open scoped Classical in
@[category API, AMS 11]
theorem turan_kubilius (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((omegaBad f n : ℝ) - badPrimeSum f N) ^ 2
      ≤ 3 * N * (badPrimeSum f N + 1) := by
  have hcardIcc : ((#(Icc 1 N) : ℕ) : ℝ) = N := by rw [Nat.card_Icc]; simp
  have hexp : ∑ n ∈ Icc 1 N, ((omegaBad f n : ℝ) - badPrimeSum f N) ^ 2
      = (∑ n ∈ Icc 1 N, (omegaBad f n : ℝ) ^ 2)
        - 2 * badPrimeSum f N * (∑ n ∈ Icc 1 N, (omegaBad f n : ℝ))
        + N * badPrimeSum f N ^ 2 := by
    have : ∀ n ∈ Icc 1 N, ((omegaBad f n : ℝ) - badPrimeSum f N) ^ 2
        = (omegaBad f n : ℝ) ^ 2 - badPrimeSum f N * (2 * (omegaBad f n : ℝ))
          + badPrimeSum f N ^ 2 := fun n _ ↦ by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcardIcc]
    ring
  have h1 := sum_omegaBad_sq_le f N
  have h2 := le_sum_omegaBad f N
  have hE := badPrimeSum_nonneg f N
  have hcard := card_badPrimesLE_le f N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * badPrimeSum f N),
    mul_nonneg hE hN, mul_nonneg hE hE]

/--
The Turán–Kubilius inequality for the prime set `E = {p : f p = -1}`.
-/
@[category API, AMS 11]
theorem exists_turan_kubilius :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Icc 1 N, ((omegaBad f n : ℝ) - badPrimeSum f N) ^ 2
      ≤ C * N * (badPrimeSum f N + 1) :=
  ⟨3, turan_kubilius f⟩

/-- Telescoping bound `∑_{2 ≤ k ≤ N} 1/k² ≤ 1 - 1/N`. -/
@[category API, AMS 11]
theorem sum_Icc_one_div_sq_le : ∀ N : ℕ, 1 ≤ N →
    ∑ k ∈ Icc 2 N, (1 : ℝ) / k ^ 2 ≤ 1 - 1 / N := by
  intro N
  induction N with
  | zero => omega
  | succ n ih =>
    intro _
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n
      norm_num
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h
      have hstep := ih h
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
      push_cast
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

open scoped Classical in
/-- Reindexing the multiples of `p` in `[1, N]` as `p * m` with `m ∈ [1, ⌊N/p⌋]`. -/
@[category API, AMS 11]
theorem sum_filter_dvd_eq {N p : ℕ} (hp : 0 < p) (g : ℕ → ℝ) :
    ∑ n ∈ {n ∈ Icc 1 N | p ∣ n}, g n = ∑ m ∈ Icc 1 (N / p), g (p * m) := by
  refine (Finset.sum_nbij' (i := fun m ↦ p * m) (j := fun n ↦ n / p) ?_ ?_ ?_ ?_ ?_).symm
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
    · simpa using Nat.mul_le_mul hp hm.1
    · rw [mul_comm, ← Nat.le_div_iff_mul_le hp]
      exact hm.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    simp only [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hnN⟩
    exact Nat.one_le_div_iff hp |>.2 (Nat.le_of_dvd (by omega) hdvd)
  · intro m _
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    rfl

open scoped Classical in
/-- `∑_{n ≤ N} f(n) ω_E(n) = ∑_{p ∈ E, p ≤ N} ∑_{m ≤ N/p} f(p m)`. -/
@[category API, AMS 11]
theorem sum_mul_omegaBad_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n * omegaBad f n
      = ∑ p ∈ badPrimesLE f N, ∑ m ∈ Icc 1 (N / p), f (p * m) := by
  have hexp : ∀ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ)
      = ∑ p ∈ badPrimesLE f N, if p ∣ n then f n else 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [omegaBad_eq_card_filter_badPrimesLE f hn.1 hn.2, ← Finset.sum_boole, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by split <;> simp
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.sum_filter]
  exact sum_filter_dvd_eq (mem_badPrimesLE_iff f |>.1 hp).2.1.pos f

@[category API, AMS 11]
theorem abs_eq_one_of_one_le (hf : IsPMOneMultiplicative f) {n : ℕ} (hn : 1 ≤ n) :
    |f n| = 1 := by
  rcases hf.pmOne n hn with h | h <;> rw [h] <;> norm_num

open scoped Classical in
@[category API, AMS 11]
theorem sum_badPrimesLE_one_div_sq_le (N : ℕ) :
    ∑ p ∈ badPrimesLE f N, (1 : ℝ) / p ^ 2 ≤ 1 := by
  have hsub : badPrimesLE f N ⊆ Icc 2 N := by
    intro p hp
    rw [mem_badPrimesLE_iff] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.1.two_le, hp.1⟩
  have h1 : ∑ p ∈ badPrimesLE f N, (1 : ℝ) / p ^ 2 ≤ ∑ k ∈ Icc 2 N, (1 : ℝ) / k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by omega : ¬ (2 : ℕ) ≤ 0), Finset.sum_empty] at h1
    linarith
  · have h2 := sum_Icc_one_div_sq_le N hN
    have h3 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith

open scoped Classical in
/--
The hyperbola estimate: `∑_{n ≤ N} f(n) ω_E(n) = ∑_{p ∈ E, p ≤ N} f(p) S(N/p) + O(N)`.

The error comes only from the `m ≤ N/p` divisible by `p`, of which there are at most `N/p²`,
and `∑_p 1/p² ≤ 1`.
-/
@[category API, AMS 11]
theorem sum_mul_omegaBad_approx (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, f n * omegaBad f n)
      - ∑ p ∈ badPrimesLE f N, f p * partialSum f (N / p)| ≤ 2 * N := by
  rw [sum_mul_omegaBad_eq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ p ∈ badPrimesLE f N,
      |∑ m ∈ Icc 1 (N / p), f (p * m) - f p * partialSum f (N / p)|
        ≤ 2 * (N : ℝ) * ((1 : ℝ) / p ^ 2) := by
    intro p hp
    obtain ⟨hpN, hprime, hfp⟩ := mem_badPrimesLE_iff f |>.1 hp
    have hppos : 0 < p := hprime.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hppos
    rw [partialSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ Icc 1 (N / p),
        |f (p * m) - f p * f m| ≤ if p ∣ m then (2 : ℝ) else 0 := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      by_cases hd : p ∣ m
      · rw [if_pos hd]
        rcases hf.pmOne (p * m) (Nat.mul_pos hppos (by omega)) with h1 | h1 <;>
          rcases hf.pmOne p hppos with h2 | h2 <;>
            rcases hf.pmOne m hm.1 with h3 | h3 <;> rw [h1, h2, h3] <;> norm_num
      · rw [if_neg hd, hf.map_mul_of_coprime p m ((Nat.Prime.coprime_iff_not_dvd hprime).2 hd)]
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcount : ∑ m ∈ Icc 1 (N / p), (if p ∣ m then (2 : ℝ) else 0)
        = 2 * ((N / p / p : ℕ) : ℝ) := by
      have hsplit : ∀ m : ℕ, (if p ∣ m then (2 : ℝ) else 0)
          = 2 * (if p ∣ m then (1 : ℝ) else 0) := by
        intro m; split <;> simp
      rw [Finset.sum_congr rfl fun m _ ↦ hsplit m, ← Finset.mul_sum, Finset.sum_boole,
        card_filter_dvd_Icc]
    rw [hcount, Nat.div_div_eq_div_mul]
    have h4 : ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / (p * p) := by
      rw [← Nat.cast_mul]; exact Nat.cast_div_le
    have : (N : ℝ) / (p * p) = N * (1 / p ^ 2) := by ring
    nlinarith [h4]
  refine (Finset.sum_le_sum key).trans ?_
  rw [← Finset.mul_sum]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [sum_badPrimesLE_one_div_sq_le f N, hN]

/-- The hyperbola estimate, in existential form. -/
@[category API, AMS 11]
theorem exists_sum_mul_omegaBad (hf : IsPMOneMultiplicative f) :
    ∃ C : ℝ, ∀ N : ℕ, |(∑ n ∈ Icc 1 N, f n * omegaBad f n)
      - ∑ p ∈ badPrimesLE f N, f p * partialSum f (N / p)| ≤ C * N :=
  ⟨2, sum_mul_omegaBad_approx f hf⟩

@[category API, AMS 11]
theorem sum_sq_eq (hf : IsPMOneMultiplicative f) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n ^ 2 = N := by
  have : ∀ n ∈ Icc 1 N, f n ^ 2 = 1 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rcases hf.pmOne n hn.1 with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

@[category API, AMS 11]
theorem abs_partialSum_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |partialSum f N| ≤ N := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ n ∈ Icc 1 N, |f n| = 1 := fun n hn ↦
    abs_eq_one_of_one_le f hf (Finset.mem_Icc.1 hn).1
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

@[category API, AMS 11]
theorem abs_mean_le_one (hf : IsPMOneMultiplicative f) (N : ℕ) : |mean f N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mean]
  · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [mean_eq_partialSum_div, abs_div, abs_of_nonneg hNR.le, div_le_one hNR]
    exact abs_partialSum_le f hf N

open scoped Classical in
/-- Cauchy–Schwarz applied to `∑_{n ≤ N} f(n) (ω_E(n) - E(N))`. -/
@[category API, AMS 11]
theorem abs_sum_mul_omegaBad_sub_le (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |∑ n ∈ Icc 1 N, f n * ((omegaBad f n : ℝ) - badPrimeSum f N)|
      ≤ 3 * N * Real.sqrt (badPrimeSum f N + 1) := by
  have hE := badPrimeSum_nonneg f N
  have hB : (0 : ℝ) ≤ badPrimeSum f N + 1 := by linarith
  have hBsq : Real.sqrt (badPrimeSum f N + 1) ^ 2 = badPrimeSum f N + 1 := Real.sq_sqrt hB
  have hB0 : (0 : ℝ) ≤ Real.sqrt (badPrimeSum f N + 1) := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) f
    (fun n ↦ (omegaBad f n : ℝ) - badPrimeSum f N)
  rw [sum_sq_eq f hf] at hCS
  have hTK := turan_kubilius f N
  have hkey : (∑ n ∈ Icc 1 N, f n * ((omegaBad f n : ℝ) - badPrimeSum f N)) ^ 2
      ≤ (3 * N * Real.sqrt (badPrimeSum f N + 1)) ^ 2 := by
    refine hCS.trans ?_
    have : (3 * (N : ℝ) * Real.sqrt (badPrimeSum f N + 1)) ^ 2
        = 9 * N ^ 2 * (badPrimeSum f N + 1) := by
      rw [mul_pow, mul_pow, hBsq]; ring
    rw [this]
    nlinarith [hTK, hN, hE]
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((∑ n ∈ Icc 1 N, f n * ((omegaBad f n : ℝ) - badPrimeSum f N)) ^ 2)
      ≤ Real.sqrt ((3 * N * Real.sqrt (badPrimeSum f N + 1)) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = 3 * N * Real.sqrt (badPrimeSum f N + 1) := Real.sqrt_sq (by positivity)

/--
The functional relation: with `σ(N) = S(N)/N`,
`|σ(N)·E(N) + ∑_{p ∈ E, p ≤ N} σ(⌊N/p⌋)/p| ≤ C (√(E(N)+1) + 1)`.

Obtained from `exists_turan_kubilius` by Cauchy–Schwarz together with
`exists_sum_mul_omegaBad` and `f p = -1` on `E`.
-/
@[category API, AMS 11]
theorem exists_functional_relation (hf : IsPMOneMultiplicative f) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |mean f N * badPrimeSum f N
        + ∑ p ∈ badPrimesLE f N, mean f (N / p) / p|
        ≤ C * (Real.sqrt (badPrimeSum f N + 1) + 1) := by
  classical
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b ↦ by
    rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])
  refine ⟨3, fun N hN ↦ ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set B := Real.sqrt (badPrimeSum f N + 1) with hBdef
  have hB0 : (0 : ℝ) ≤ B := Real.sqrt_nonneg _
  have hexp : ∑ n ∈ Icc 1 N, f n * ((omegaBad f n : ℝ) - badPrimeSum f N)
      = (∑ n ∈ Icc 1 N, f n * omegaBad f n) - badPrimeSum f N * partialSum f N := by
    rw [partialSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  have hA := abs_sum_mul_omegaBad_sub_le f hf N
  rw [hexp] at hA
  have hC := sum_mul_omegaBad_approx f hf N
  have hfp : ∀ p ∈ badPrimesLE f N,
      f p * partialSum f (N / p) = -partialSum f (N / p) := fun p hp ↦ by
    rw [(mem_badPrimesLE_iff f |>.1 hp).2.2]; ring
  rw [Finset.sum_congr rfl hfp, Finset.sum_neg_distrib, sub_neg_eq_add] at hC
  -- Step 1: combine the two estimates at the level of the partial sums `S`.
  have h1 : |badPrimeSum f N * partialSum f N
      + ∑ p ∈ badPrimesLE f N, partialSum f (N / p)| ≤ 3 * N * B + 2 * N := by
    have heq : badPrimeSum f N * partialSum f N
        + ∑ p ∈ badPrimesLE f N, partialSum f (N / p)
        = ((∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            + ∑ p ∈ badPrimesLE f N, partialSum f (N / p))
          - ((∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            - badPrimeSum f N * partialSum f N) := by ring
    rw [heq]
    calc |((∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            + ∑ p ∈ badPrimesLE f N, partialSum f (N / p))
          - ((∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            - badPrimeSum f N * partialSum f N)|
        ≤ |(∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            + ∑ p ∈ badPrimesLE f N, partialSum f (N / p)|
          + |(∑ n ∈ Icc 1 N, f n * (omegaBad f n : ℝ))
            - badPrimeSum f N * partialSum f N| := habs _ _
      _ ≤ 2 * N + 3 * N * B := add_le_add hC hA
      _ = 3 * N * B + 2 * N := by ring
  -- Step 2: divide by `N`.
  have h2 : |mean f N * badPrimeSum f N
      + ∑ p ∈ badPrimesLE f N, partialSum f (N / p) / N| ≤ 3 * B + 2 := by
    have hdiv : mean f N * badPrimeSum f N
        + ∑ p ∈ badPrimesLE f N, partialSum f (N / p) / N
        = (badPrimeSum f N * partialSum f N
          + ∑ p ∈ badPrimesLE f N, partialSum f (N / p)) / N := by
      rw [add_div, Finset.sum_div, mean_eq_partialSum_div]; ring
    rw [hdiv, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
    calc |badPrimeSum f N * partialSum f N
        + ∑ p ∈ badPrimesLE f N, partialSum f (N / p)| ≤ 3 * N * B + 2 * N := h1
      _ = (3 * B + 2) * N := by ring
  -- Step 3: replace `S(⌊N/p⌋)/N` by `σ(⌊N/p⌋)/p`.
  have h3 : |∑ p ∈ badPrimesLE f N,
      (partialSum f (N / p) / N - mean f (N / p) / p)| ≤ 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ p ∈ badPrimesLE f N,
        |partialSum f (N / p) / N - mean f (N / p) / p| ≤ 1 / N := by
      intro p hp
      obtain ⟨hpN, hprime, -⟩ := mem_badPrimesLE_iff f |>.1 hp
      have hppos : 0 < p := hprime.pos
      have hpR : (0 : ℝ) < p := by exact_mod_cast hppos
      rcases Nat.eq_zero_or_pos (N / p) with hk | hk
      · rw [hk]
        simp [partialSum, mean]
      · have hkR : (0 : ℝ) < ((N / p : ℕ) : ℝ) := by exact_mod_cast hk
        have hpos : (0 : ℝ) < (N : ℝ) * (((N / p : ℕ) : ℝ) * p) := by positivity
        have hkey : partialSum f (N / p) / N - mean f (N / p) / p
            = partialSum f (N / p) * (((N / p : ℕ) : ℝ) * p - N)
              / ((N : ℝ) * (((N / p : ℕ) : ℝ) * p)) := by
          rw [mean_eq_partialSum_div, div_div]
          field_simp
        have hle : ((N / p : ℕ) : ℝ) * p ≤ N := by exact_mod_cast Nat.div_mul_le_self N p
        have hgt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          have hnat : N < (N / p + 1) * p := by
            have h1' := Nat.div_add_mod N p
            have h2' := Nat.mod_lt N hppos
            calc N = p * (N / p) + N % p := h1'.symm
              _ < p * (N / p) + p := by omega
              _ = (N / p + 1) * p := by ring
          have := (Nat.cast_lt (α := ℝ)).2 hnat
          push_cast at this
          linarith
        have habsS : |partialSum f (N / p)| ≤ ((N / p : ℕ) : ℝ) :=
          abs_partialSum_le f hf _
        have hfac : |((N / p : ℕ) : ℝ) * p - N| ≤ p := by
          rw [abs_le]; constructor <;> linarith
        have h5 : |partialSum f (N / p) * (((N / p : ℕ) : ℝ) * p - N)|
            ≤ ((N / p : ℕ) : ℝ) * p := by
          rw [abs_mul]
          exact mul_le_mul habsS hfac (abs_nonneg _) hkR.le
        rw [hkey, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hNR]
        nlinarith [h5, hNR, hkR, hpR]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := card_badPrimesLE_le f N
    have hmul : (#(badPrimesLE f N) : ℝ) * (1 / N) ≤ (N : ℝ) * (1 / N) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    have hone : (N : ℝ) * (1 / N) = 1 := by field_simp
    linarith [hmul, hone]
  -- Combine.
  have hsplit : mean f N * badPrimeSum f N
      + ∑ p ∈ badPrimesLE f N, mean f (N / p) / p
      = (mean f N * badPrimeSum f N
        + ∑ p ∈ badPrimesLE f N, partialSum f (N / p) / N)
      - ∑ p ∈ badPrimesLE f N, (partialSum f (N / p) / N - mean f (N / p) / p) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  calc |(mean f N * badPrimeSum f N
      + ∑ p ∈ badPrimesLE f N, partialSum f (N / p) / N)
      - ∑ p ∈ badPrimesLE f N, (partialSum f (N / p) / N - mean f (N / p) / p)|
      ≤ |mean f N * badPrimeSum f N
        + ∑ p ∈ badPrimesLE f N, partialSum f (N / p) / N|
        + |∑ p ∈ badPrimesLE f N, (partialSum f (N / p) / N - mean f (N / p) / p)| :=
        habs _ _
    _ ≤ (3 * B + 2) + 1 := add_le_add h2 h3
    _ = 3 * (B + 1) := by ring

end Wirsing
