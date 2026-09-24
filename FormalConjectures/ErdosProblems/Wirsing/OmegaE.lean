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

/--
The divergence hypothesis of the hard half of Wirsing's theorem is equivalent to
`E(N) → ∞`, because `1 - f p ∈ {0, 2}` for a `±1`-valued `f`.
-/
@[category API, AMS 11]
theorem tendsto_badPrimeSum_atTop_of_not_summable (hf : IsPMOneMultiplicative f)
    (h : ¬ Summable (pretentiousSeries f)) :
    Tendsto (badPrimeSum f) atTop atTop := by
  sorry

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
