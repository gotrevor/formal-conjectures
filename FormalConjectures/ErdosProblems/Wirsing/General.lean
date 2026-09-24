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
public import FormalConjectures.ErdosProblems.Wirsing.OmegaE

/-!
# The Wirsing functional relation for an arbitrary set of primes

`FormalConjectures.ErdosProblems.Wirsing.OmegaE` runs the Turán–Kubilius argument for the
specific prime set `E = {p : f p = -1}`.  Nothing in that argument uses the value of `f` on
`E` until the very last rewrite, so the same estimates hold for an **arbitrary** finite set
`S` of primes, with `f p` kept symbolic:
$$\left|\sigma(N)\sum_{p \in S}\frac1p - \sum_{p \in S} f(p)\frac{\sigma(\lfloor N/p\rfloor)}{p}\right|
  \le 3\left(\sqrt{1 + \sum_{p \in S}\frac1p} + 1\right).$$

This extra freedom is what an attack on the remaining analytic core needs.  Taking `S` to be
a **fixed** finite set (independent of `N`) turns the relation into a statement about the
bounded sequence `σ` alone, which can then be iterated; taking `S` inside `{p : f p = 1}`
says that `σ` varies slowly along `S`.

See `PENDING_WORK.md`.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ) (S : Finset ℕ)

/-- `ω_S n` counts the elements of `S` dividing `n`. -/
noncomputable def omegaOn (n : ℕ) : ℕ := #{p ∈ S | p ∣ n}

/-- `∑_{p ∈ S} 1/p`. -/
noncomputable def recipSum : ℝ := ∑ p ∈ S, (1 : ℝ) / p

@[category API, AMS 11]
theorem recipSum_nonneg : 0 ≤ recipSum S :=
  Finset.sum_nonneg fun p _ ↦ by positivity

@[category API, AMS 11]
theorem sum_omegaOn_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, omegaOn S n = ∑ p ∈ S, N / p := by
  have h1 : ∀ n ∈ Icc 1 N, omegaOn S n = ∑ p ∈ S, if p ∣ n then 1 else 0 := fun n _ ↦ by
    rw [omegaOn, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← card_filter_dvd_Icc, Finset.card_filter]

@[category API, AMS 11]
theorem sum_omegaOn_cast (N : ℕ) :
    ∑ n ∈ Icc 1 N, (omegaOn S n : ℝ) = ∑ p ∈ S, ((N / p : ℕ) : ℝ) := by
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_omegaOn_eq]

@[category API, AMS 11]
theorem sum_omegaOn_le (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (omegaOn S n : ℝ) ≤ N * recipSum S := by
  rw [sum_omegaOn_cast, recipSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp0 : 0 < p := (hS p hp).pos
  calc ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    _ = N * (1 / p) := by ring

@[category API, AMS 11]
theorem le_sum_omegaOn (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    N * recipSum S - #S ≤ ∑ n ∈ Icc 1 N, (omegaOn S n : ℝ) := by
  rw [sum_omegaOn_cast, recipSum, Finset.mul_sum, sub_le_iff_le_add,
    Finset.card_eq_sum_ones S, Nat.cast_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp0 : 0 < p := (hS p hp).pos
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

@[category API, AMS 11]
theorem sum_omegaOn_sq_le (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((omegaOn S n : ℝ)) ^ 2
      ≤ N * recipSum S + N * recipSum S ^ 2 := by
  have hexp : ∀ n ∈ Icc 1 N, ((omegaOn S n : ℝ)) ^ 2
      = ∑ p ∈ S, ∑ q ∈ S, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n _
    have hcard : ((omegaOn S n : ℕ) : ℝ) = ∑ p ∈ S, (if p ∣ n then (1 : ℝ) else 0) := by
      rw [omegaOn, Finset.sum_boole]
    rw [sq, hcard, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hswap : ∀ p ∈ S, ∑ n ∈ Icc 1 N, ∑ q ∈ S,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      = ∑ q ∈ S, ∑ n ∈ Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) :=
    fun p _ ↦ Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  have hbound : ∀ p ∈ S, ∑ q ∈ S, ∑ n ∈ Icc 1 N,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      ≤ ∑ q ∈ S, ((if p = q then (N : ℝ) / p else 0) + (N : ℝ) / (p * q)) := fun p hp ↦
    Finset.sum_le_sum fun q hq ↦ sum_indicator_dvd_le (hS p hp) (hS q hq)
  refine (Finset.sum_le_sum hbound).trans ?_
  have hsplit : ∀ p ∈ S, ∑ q ∈ S, ((if p = q then (N : ℝ) / p else 0) + (N : ℝ) / (p * q))
      = (N : ℝ) / p + (N : ℝ) / p * ∑ q ∈ S, (1 : ℝ) / q := by
    intro p hp
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq S p (fun _ ↦ (N : ℝ) / p), if_pos hp,
      Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun q _ ↦ ?_)
    rw [div_mul_eq_div_div]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hE : ∑ p ∈ S, (N : ℝ) / p = N * recipSum S := by
    rw [recipSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [mul_one_div]
  rw [hE, recipSum]
  ring_nf
  rfl

/-- Turán–Kubilius for an arbitrary finite set `S` of primes, all at most `N`. -/
@[category API, AMS 11]
theorem turan_kubilius_on (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    ∑ n ∈ Icc 1 N, ((omegaOn S n : ℝ) - recipSum S) ^ 2
      ≤ 3 * N * (recipSum S + 1) := by
  have hcardIcc : ((#(Icc 1 N) : ℕ) : ℝ) = N := by rw [Nat.card_Icc]; simp
  have hcard : (#S : ℝ) ≤ N := by
    have hsub : S ⊆ Icc 1 N := fun p hp ↦ Finset.mem_Icc.2 ⟨(hS p hp).one_lt.le, hSN p hp⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans_eq (by omega)
  have hexp : ∑ n ∈ Icc 1 N, ((omegaOn S n : ℝ) - recipSum S) ^ 2
      = (∑ n ∈ Icc 1 N, (omegaOn S n : ℝ) ^ 2)
        - 2 * recipSum S * (∑ n ∈ Icc 1 N, (omegaOn S n : ℝ))
        + N * recipSum S ^ 2 := by
    have : ∀ n ∈ Icc 1 N, ((omegaOn S n : ℝ) - recipSum S) ^ 2
        = (omegaOn S n : ℝ) ^ 2 - recipSum S * (2 * (omegaOn S n : ℝ))
          + recipSum S ^ 2 := fun n _ ↦ by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcardIcc]
    ring
  have h1 := sum_omegaOn_sq_le S hS N
  have h2 := le_sum_omegaOn S hS N
  have hE := recipSum_nonneg S
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * recipSum S),
    mul_nonneg hE hN, mul_nonneg hE hE]

@[category API, AMS 11]
theorem sum_mul_omegaOn_eq (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n * omegaOn S n
      = ∑ p ∈ S, ∑ m ∈ Icc 1 (N / p), f (p * m) := by
  have hexp : ∀ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ)
      = ∑ p ∈ S, if p ∣ n then f n else 0 := by
    intro n _
    rw [omegaOn, ← Finset.sum_boole, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by split <;> simp
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.sum_filter]
  exact sum_filter_dvd_eq (hS p hp).pos f

@[category API, AMS 11]
theorem sum_recipSq_le (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    ∑ p ∈ S, (1 : ℝ) / p ^ 2 ≤ 1 := by
  have hsub : S ⊆ Icc 2 N := fun p hp ↦ Finset.mem_Icc.2 ⟨(hS p hp).two_le, hSN p hp⟩
  have h1 : ∑ p ∈ S, (1 : ℝ) / p ^ 2 ≤ ∑ k ∈ Icc 2 N, (1 : ℝ) / k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by omega : ¬ (2 : ℕ) ≤ 0), Finset.sum_empty] at h1
    linarith
  · have h2 := sum_Icc_one_div_sq_le N hN
    have h3 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith

/-- The hyperbola estimate for an arbitrary finite set `S` of primes, all at most `N`. -/
@[category API, AMS 11]
theorem sum_mul_omegaOn_approx (hf : IsPMOneMultiplicative f) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    |(∑ n ∈ Icc 1 N, f n * omegaOn S n)
      - ∑ p ∈ S, f p * partialSum f (N / p)| ≤ 2 * N := by
  rw [sum_mul_omegaOn_eq f S hS, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ p ∈ S,
      |∑ m ∈ Icc 1 (N / p), f (p * m) - f p * partialSum f (N / p)|
        ≤ 2 * (N : ℝ) * ((1 : ℝ) / p ^ 2) := by
    intro p hp
    have hprime := hS p hp
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
  nlinarith [sum_recipSq_le S hS hSN, hN]

/-- Cauchy–Schwarz applied to `∑_{n ≤ N} f(n) (ω_S(n) - L_S)`. -/
@[category API, AMS 11]
theorem abs_sum_mul_omegaOn_sub_le (hf : IsPMOneMultiplicative f) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hSN : ∀ p ∈ S, p ≤ N) :
    |∑ n ∈ Icc 1 N, f n * ((omegaOn S n : ℝ) - recipSum S)|
      ≤ 3 * N * Real.sqrt (recipSum S + 1) := by
  have hE := recipSum_nonneg S
  have hB : (0 : ℝ) ≤ recipSum S + 1 := by linarith
  have hBsq : Real.sqrt (recipSum S + 1) ^ 2 = recipSum S + 1 := Real.sq_sqrt hB
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) f
    (fun n ↦ (omegaOn S n : ℝ) - recipSum S)
  rw [sum_sq_eq f hf] at hCS
  have hTK := turan_kubilius_on S hS hSN
  have hkey : (∑ n ∈ Icc 1 N, f n * ((omegaOn S n : ℝ) - recipSum S)) ^ 2
      ≤ (3 * N * Real.sqrt (recipSum S + 1)) ^ 2 := by
    refine hCS.trans ?_
    have heq : (3 * (N : ℝ) * Real.sqrt (recipSum S + 1)) ^ 2
        = 9 * N ^ 2 * (recipSum S + 1) := by
      rw [mul_pow, mul_pow, hBsq]; ring
    rw [heq]
    nlinarith [hTK, hN, hE]
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((∑ n ∈ Icc 1 N, f n * ((omegaOn S n : ℝ) - recipSum S)) ^ 2)
      ≤ Real.sqrt ((3 * N * Real.sqrt (recipSum S + 1)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = 3 * N * Real.sqrt (recipSum S + 1) := Real.sqrt_sq (by positivity)

/--
**The Wirsing functional relation for an arbitrary finite set of primes.**

For every finite set `S` of primes with `p ≤ N` for all `p ∈ S`,
`|σ(N)·L_S - ∑_{p ∈ S} f(p) σ(⌊N/p⌋)/p| ≤ 3(√(L_S + 1) + 1)`,
where `σ = mean f` and `L_S = ∑_{p ∈ S} 1/p`.

Taking `S = {p ≤ N : f p = -1}` recovers `Wirsing.exists_functional_relation`.  Taking `S`
fixed and letting `N → ∞` gives a relation for the sequence `σ` alone.
-/
@[category API, AMS 11]
theorem functional_relation_on (hf : IsPMOneMultiplicative f) (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ} (hN : 1 ≤ N) (hSN : ∀ p ∈ S, p ≤ N) :
    |mean f N * recipSum S - ∑ p ∈ S, f p * mean f (N / p) / p|
      ≤ 3 * (Real.sqrt (recipSum S + 1) + 1) := by
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b ↦ by
    rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set B := Real.sqrt (recipSum S + 1) with hBdef
  have hB0 : (0 : ℝ) ≤ B := Real.sqrt_nonneg _
  have hcard : (#S : ℝ) ≤ N := by
    have hsub : S ⊆ Icc 1 N := fun p hp ↦ Finset.mem_Icc.2 ⟨(hS p hp).one_lt.le, hSN p hp⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans_eq (by omega)
  have hexp : ∑ n ∈ Icc 1 N, f n * ((omegaOn S n : ℝ) - recipSum S)
      = (∑ n ∈ Icc 1 N, f n * omegaOn S n) - recipSum S * partialSum f N := by
    rw [partialSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  have hA := abs_sum_mul_omegaOn_sub_le f S hf hS hSN
  rw [hexp] at hA
  have hC := sum_mul_omegaOn_approx f S hf hS hSN
  -- Step 1: at the level of the partial sums `S`.
  have h1 : |recipSum S * partialSum f N - ∑ p ∈ S, f p * partialSum f (N / p)|
      ≤ 3 * N * B + 2 * N := by
    have heq : recipSum S * partialSum f N - ∑ p ∈ S, f p * partialSum f (N / p)
        = ((∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, f p * partialSum f (N / p))
          - ((∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - recipSum S * partialSum f N) := by ring
    rw [heq]
    calc |((∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, f p * partialSum f (N / p))
          - ((∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - recipSum S * partialSum f N)|
        ≤ |(∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - ∑ p ∈ S, f p * partialSum f (N / p)|
          + |(∑ n ∈ Icc 1 N, f n * (omegaOn S n : ℝ))
            - recipSum S * partialSum f N| := habs _ _
      _ ≤ 2 * N + 3 * N * B := add_le_add hC hA
      _ = 3 * N * B + 2 * N := by ring
  -- Step 2: divide by `N`.
  have h2 : |mean f N * recipSum S - ∑ p ∈ S, f p * partialSum f (N / p) / N|
      ≤ 3 * B + 2 := by
    have hdiv : mean f N * recipSum S - ∑ p ∈ S, f p * partialSum f (N / p) / N
        = (recipSum S * partialSum f N - ∑ p ∈ S, f p * partialSum f (N / p)) / N := by
      rw [sub_div, Finset.sum_div, mean_eq_partialSum_div]
      ring
    rw [hdiv, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
    calc |recipSum S * partialSum f N - ∑ p ∈ S, f p * partialSum f (N / p)|
        ≤ 3 * N * B + 2 * N := h1
      _ = (3 * B + 2) * N := by ring
  -- Step 3: replace `S(⌊N/p⌋)/N` by `σ(⌊N/p⌋)/p`.
  have h3 : |∑ p ∈ S, (f p * partialSum f (N / p) / N - f p * mean f (N / p) / p)| ≤ 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ p ∈ S,
        |f p * partialSum f (N / p) / N - f p * mean f (N / p) / p| ≤ 1 / N := by
      intro p hp
      have hprime := hS p hp
      have hppos : 0 < p := hprime.pos
      have hpR : (0 : ℝ) < p := by exact_mod_cast hppos
      have hfabs : |f p| = 1 := abs_eq_one_of_one_le f hf hppos
      have hfac : f p * partialSum f (N / p) / N - f p * mean f (N / p) / p
          = f p * (partialSum f (N / p) / N - mean f (N / p) / p) := by ring
      rw [hfac, abs_mul, hfabs, one_mul]
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
        have habsS : |partialSum f (N / p)| ≤ ((N / p : ℕ) : ℝ) := abs_partialSum_le f hf _
        have hfac2 : |((N / p : ℕ) : ℝ) * p - N| ≤ p := by
          rw [abs_le]; constructor <;> linarith
        have h5 : |partialSum f (N / p) * (((N / p : ℕ) : ℝ) * p - N)|
            ≤ ((N / p : ℕ) : ℝ) * p := by
          rw [abs_mul]
          exact mul_le_mul habsS hfac2 (abs_nonneg _) hkR.le
        rw [hkey, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hNR]
        nlinarith [h5, hNR, hkR, hpR]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hmul : (#S : ℝ) * (1 / N) ≤ (N : ℝ) * (1 / N) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have hone : (N : ℝ) * (1 / N) = 1 := by field_simp
    linarith [hmul, hone]
  have hsplit : mean f N * recipSum S - ∑ p ∈ S, f p * mean f (N / p) / p
      = (mean f N * recipSum S - ∑ p ∈ S, f p * partialSum f (N / p) / N)
      + ∑ p ∈ S, (f p * partialSum f (N / p) / N - f p * mean f (N / p) / p) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  calc |(mean f N * recipSum S - ∑ p ∈ S, f p * partialSum f (N / p) / N)
      + ∑ p ∈ S, (f p * partialSum f (N / p) / N - f p * mean f (N / p) / p)|
      ≤ |mean f N * recipSum S - ∑ p ∈ S, f p * partialSum f (N / p) / N|
        + |∑ p ∈ S, (f p * partialSum f (N / p) / N - f p * mean f (N / p) / p)| :=
        abs_add_le _ _
    _ ≤ (3 * B + 2) + 1 := add_le_add h2 h3
    _ = 3 * (B + 1) := by ring

end Wirsing
