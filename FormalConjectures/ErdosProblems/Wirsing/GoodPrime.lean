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
public import FormalConjectures.ErdosProblems.Wirsing.Newman
public import FormalConjectures.ErdosProblems.Wirsing.Extremal

/-!
# Good primes in a multiplicative window

The rigidity step (`Wirsing.sum_bad_weight_le`, `Wirsing.exists_sum_bad_weight_le_const`)
produces an *exceptional* set of primes of bounded Mertens weight `K`, and says that at every
other prime the functional relation is nearly extremal.  To use that one needs a prime that is
**not** exceptional and whose position is controlled, because the window step
`Wirsing.eq_of_mean_quotient_close` compares two quotients of bounded ratio.

This file supplies exactly that: a multiplicative window whose prime weight exceeds `K` — the
prime number theorem, through `Newman.tendsto_sum_log_prime_div_window` — and the pigeonhole
that extracts a non-exceptional prime from it.  The window ratio is `e^{|K|+1}`, which depends
only on `K`.

*References:*
- [Me74] Mertens, F., Ein Beitrag zur analytischen Zahlentheorie. J. Reine Angew. Math. 78
  (1874), 46-62.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/--
**A multiplicative window of prime weight more than `K`.**  For every `K` and every `X₀` there
is an `X ≥ X₀` with
$$\sum_{X < p \le \lfloor e^{|K|+1}X\rfloor} \frac{\log p}{p} > K.$$

The ratio `e^{|K|+1}` depends only on `K`; this is where the prime number theorem enters, via
`Newman.tendsto_sum_log_prime_div_window`.  Mertens' first theorem with its `O(1)` error cannot
give it: a window carries weight `\log c`, which an `O(1)` error swamps.
-/
@[category API, AMS 11]
theorem exists_window_weight_gt (K : ℝ) (X₀ : ℕ) :
    ∃ X : ℕ, X₀ ≤ X ∧
      K < ∑ p ∈ (Ioc X ⌊Real.exp (|K| + 1) * X⌋₊).filter Nat.Prime, Real.log p / p := by
  classical
  set c : ℝ := Real.exp (|K| + 1) with hcdef
  have hc : 1 < c := by
    rw [hcdef, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.2 (by positivity)
  have hlogc : Real.log c = |K| + 1 := by rw [hcdef, Real.log_exp]
  have h := Newman.tendsto_sum_log_prime_div_window hc
  obtain ⟨X₁, hX₁⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  refine ⟨max X₁ X₀, le_max_right _ _, ?_⟩
  have hd := hX₁ (max X₁ X₀) (le_max_left _ _)
  rw [Real.dist_eq, abs_lt, hlogc] at hd
  linarith [hd.1, le_abs_self K]

/--
The pigeonhole: a set of primes of weight more than `K` is not contained in a set of weight at
most `K`.
-/
@[category API, AMS 11]
theorem exists_prime_notMem {T S : Finset ℕ} {K : ℝ}
    (hS : ∑ p ∈ S, Real.log p / p ≤ K)
    (hT : K < ∑ p ∈ T.filter Nat.Prime, Real.log p / p) :
    ∃ p ∈ T, p.Prime ∧ p ∉ S := by
  classical
  by_contra hcon
  have hsub : T.filter Nat.Prime ⊆ S := by
    intro p hp
    rw [Finset.mem_filter] at hp
    by_contra hnot
    exact hcon ⟨p, hp.1, hp.2, hnot⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ ↦ div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg i))
  linarith

/-- A non-exceptional prime in a multiplicative window of ratio `e^{|K|+1}`. -/
@[category API, AMS 11]
theorem exists_prime_window_notMem (S : Finset ℕ) (X₀ : ℕ) {K : ℝ}
    (hS : ∑ p ∈ S, Real.log p / p ≤ K) :
    ∃ X p : ℕ, X₀ ≤ X ∧ X < p ∧ p ≤ ⌊Real.exp (|K| + 1) * X⌋₊ ∧ p.Prime ∧ p ∉ S := by
  obtain ⟨X, hX, hw⟩ := exists_window_weight_gt K X₀
  obtain ⟨p, hpT, hpp, hpS⟩ := exists_prime_notMem hS hw
  exact ⟨X, p, hX, (mem_Ioc.1 hpT).1, (mem_Ioc.1 hpT).2, hpp, hpS⟩

variable (f : ℕ → ℝ)

open scoped Classical in
/--
**A near-extremal prime in every window.**  If the primes at which the functional relation
loses more than `\rho` carry Mertens weight at most `K` — which is
`Wirsing.exists_sum_bad_weight_le_const`, with `K` independent of `N` — then every
multiplicative window of prime weight more than `K` whose primes are all in
`Wirsing.rigidityPrimes M₀ N` contains a prime `p` with
$$s\,f(p)\,\sigma(\lfloor N/p\rfloor) \ge A - \rho .$$

The window ratio `e^{|K|+1}` is a constant, so `Wirsing.eq_of_mean_quotient_close` can be
applied to two such primes as soon as `e^{|K|+1} < 1/(1 - (A - \rho))`; that comparison is what
turns the rigidity of the *values* `\sigma(\lfloor N/p\rfloor)` into rigidity of `f` itself.
-/
@[category API, AMS 11]
theorem exists_near_extremal_prime {M₀ N : ℕ} {A ρ s K : ℝ} {X : ℕ}
    (hbad : ∑ p ∈ (rigidityPrimes M₀ N).filter (fun p ↦ s * (f p * mean f (N / p)) < A - ρ),
        Real.log p / p ≤ K)
    (hw : K < ∑ p ∈ (Ioc X ⌊Real.exp (|K| + 1) * X⌋₊).filter Nat.Prime, Real.log p / p)
    (hsub : ∀ p ∈ Ioc X ⌊Real.exp (|K| + 1) * X⌋₊, p.Prime → p ∈ rigidityPrimes M₀ N) :
    ∃ p, p.Prime ∧ X < p ∧ p ≤ ⌊Real.exp (|K| + 1) * X⌋₊ ∧
      A - ρ ≤ s * (f p * mean f (N / p)) := by
  classical
  obtain ⟨p, hpT, hpp, hpS⟩ := exists_prime_notMem hbad hw
  refine ⟨p, hpp, (mem_Ioc.1 hpT).1, (mem_Ioc.1 hpT).2, ?_⟩
  by_contra hlt
  exact hpS (mem_filter.2 ⟨hsub p hpT hpp, by linarith [not_le.1 hlt]⟩)

end Wirsing
