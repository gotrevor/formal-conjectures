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
public import FormalConjectures.ErdosProblems.Wirsing.Split
public import FormalConjectures.ErdosProblems.Wirsing.OmegaE

/-!
# The bad-prime contraction

The coprime splitting identity of `Wirsing/Split.lean` turns one bad prime `p` into a definite
contraction of `\limsup_N |\text{mean } f\ N|` by the Euler factor
`|\sum_k f(p^k)p^{-k}| \le 1 - 1/p + 1/(p(p-1)) \le 1 - 1/(2p)`, **provided** the mean of the
coprime restriction is asymptotically invariant under dilation by a fixed integer.  That last
input is `Wirsing.DilationInvariant`, Elliott's Lipschitz estimate, and it is the only thing
this file assumes.

Iterating over a finite set `T` of bad primes `\ge 5` gives
`\limsup_N|\text{mean } f\ N| \le \prod_{p \in T}(1 - 1/(2p)) \le \exp(-\tfrac12\sum_{p\in T}1/p)`,
and `\sum_{p \text{ bad}} 1/p = \infty` drives the right-hand side to `0`.  So the crux of
Wirsing's theorem reduces to `DilationInvariant` and to nothing else.

*References:*
- [El79] Elliott, P.D.T.A., Probabilistic number theory II.
- [GHS19] Granville, A., Harper, A.J., Soundararajan, K., A new proof of Halász's theorem, and
  its consequences. Compositio Math. 155 (2019), 126-163.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/--
**Elliott's Lipschitz estimate**, in the weak qualitative form needed here: for every real
multiplicative `g` with `|g| \le 1` and every fixed `a \ge 1`,
`\text{mean } g\ N - \text{mean } g\ \lfloor N/a\rfloor \to 0`.

This fails for complex `g` (take `g(n) = n^{i\theta}`), but holds for real `g`.
-/
def DilationInvariant : Prop :=
  ∀ g : ℕ → ℝ, IsBddMultiplicative g → ∀ a : ℕ, 1 ≤ a →
    Tendsto (fun N : ℕ ↦ mean g N - mean g (N / a)) atTop (𝓝 0)

/--
**The Euler factor of a bad prime.**  If `g(p) = -1` and `K \ge 1` then
`|\sum_{k \le K} g(p^k)p^{-k}| \le 1 - 1/p + 1/(p(p-1))`.

Only `g(p^0) = 1`, `g(p) = -1` and `|g(p^k)| \le 1` are used; `g` need not be completely
multiplicative.
-/
@[category API, AMS 11]
theorem abs_sum_euler_le {g : ℕ → ℝ} (hg : IsBddMultiplicative g) {p : ℕ} (hp : p.Prime)
    (hgp : g p = -1) {K : ℕ} (hK : 1 ≤ K) :
    |∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k|
      ≤ 1 - 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  -- split off `k = 0` and `k = 1`
  have hsplit : ∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k
      = (1 - 1 / (p : ℝ)) + ∑ k ∈ Finset.Ico 2 (K + 1), g (p ^ k) / (p : ℝ) ^ k := by
    have h2K : 2 ≤ K + 1 := by omega
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) h2K]
    have h01 : ∑ k ∈ Finset.Ico 0 2, g (p ^ k) / (p : ℝ) ^ k = 1 - 1 / (p : ℝ) := by
      rw [show Finset.Ico 0 2 = ({0, 1} : Finset ℕ) by decide]
      rw [Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [hg.map_one, hgp]
      ring
    rw [h01]
  have htail : |∑ k ∈ Finset.Ico 2 (K + 1), g (p ^ k) / (p : ℝ) ^ k|
      ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hterm : ∀ k ∈ Finset.Ico 2 (K + 1),
        |g (p ^ k) / (p : ℝ) ^ k| ≤ ((p : ℝ)⁻¹) ^ k := by
      intro k _
      have hgk : |g (p ^ k)| ≤ 1 := hg.abs_le_one _ (Nat.one_le_pow _ _ hp.pos)
      have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
      rw [abs_div, abs_of_pos hpk, inv_pow, ← one_div, div_le_div_iff_of_pos_right hpk]
      exact hgk
    have hgeo := sum_Ico_pow_le (r := (p : ℝ)⁻¹) (by positivity) (by
      rw [inv_lt_one_iff₀]; right; linarith) 2 (K + 1)
    have hval : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp
    calc |∑ k ∈ Finset.Ico 2 (K + 1), g (p ^ k) / (p : ℝ) ^ k|
        ≤ ∑ k ∈ Finset.Ico 2 (K + 1), |g (p ^ k) / (p : ℝ) ^ k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico 2 (K + 1), ((p : ℝ)⁻¹) ^ k := Finset.sum_le_sum hterm
      _ ≤ ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) := hgeo
      _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := hval
  have hnn : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hp0]; linarith
  rw [hsplit]
  calc |(1 - 1 / (p : ℝ)) + ∑ k ∈ Finset.Ico 2 (K + 1), g (p ^ k) / (p : ℝ) ^ k|
      ≤ |1 - 1 / (p : ℝ)| + |∑ k ∈ Finset.Ico 2 (K + 1), g (p ^ k) / (p : ℝ) ^ k| :=
        abs_add_le _ _
    _ ≤ (1 - 1 / (p : ℝ)) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [abs_of_nonneg hnn]; linarith

/-- For `p \ge 5`, `1 - 1/p + 1/(p(p-1)) \le 1 - 1/(2p)`. -/
@[category API, AMS 11]
theorem euler_bound_le {p : ℕ} (hp : 5 ≤ p) :
    1 - 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 - 1 / (2 * (p : ℝ)) := by
  have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h1 : 1 / ((p : ℝ) * ((p : ℝ) - 1)) = 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
    field_simp
    ring
  have h2 : 1 / ((p : ℝ) - 1) ≤ 3 * (1 / (p : ℝ)) / 2 := by
    rw [div_le_div_iff₀ hp1 (by norm_num)]
    field_simp
    linarith
  have h3 : 1 / (2 * (p : ℝ)) = (1 / (p : ℝ)) / 2 := by ring
  rw [h1, h3]
  linarith

/--
**The one-step contraction.**  Assume Elliott's Lipschitz estimate.  If `p \ge 5` is a bad
prime for `g` and the coprime restriction `v = g\cdot 1_{p \nmid \cdot}` eventually has
`|\text{mean } v\ N| \le A`, then `g` eventually has
`|\text{mean } g\ N| \le (1 - 1/(2p))A + \varepsilon`.
-/
@[category API, AMS 11]
theorem eventually_abs_mean_le (hDI : DilationInvariant) {g : ℕ → ℝ}
    (hg : IsBddMultiplicative g) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hgp : g p = -1)
    {A ε : ℝ} (hε : 0 < ε)
    (hv : ∀ᶠ N in atTop, |mean (coprimeRestrict g p) N| ≤ A) :
    ∀ᶠ N in atTop, |mean g N| ≤ (1 - 1 / (2 * (p : ℝ))) * A + ε := by
  set v := coprimeRestrict g p with hvdef
  have hvm : IsBddMultiplicative v := isBddMultiplicative_coprimeRestrict hg hp
  have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hp0 : (0 : ℝ) < p := by linarith
  have hθ0 : (0 : ℝ) ≤ 1 - 1 / (2 * (p : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  -- choose the truncation level `K`
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε / 4)
    (show 1 / (p : ℝ) < 1 by rw [div_lt_one hp0]; linarith)
  set K := max K₀ 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have htailK : 1 / (p : ℝ) ^ K ≤ ε / 4 := by
    rw [← one_div_pow]
    refine le_trans ?_ hK₀.le
    exact pow_le_pow_of_le_one (by positivity)
      (by rw [div_le_one hp0]; linarith) (le_max_left _ _)
  -- the Euler factor
  have hE : |∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k| ≤ 1 - 1 / (2 * (p : ℝ)) :=
    (abs_sum_euler_le hg hp hgp hK1).trans (euler_bound_le hp5)
  -- the dilation defects
  have hk : ∀ k ∈ range (K + 1),
      Tendsto (fun N : ℕ ↦ |mean v (N / p ^ k) - mean v N|) atTop (𝓝 0) := by
    intro k _
    have h := (hDI v hvm (p ^ k) (Nat.one_le_pow _ _ hp.pos)).abs
    rw [abs_zero] at h
    exact h.congr fun N ↦ abs_sub_comm _ _
  have hsum0 : Tendsto (fun N : ℕ ↦ ∑ k ∈ range (K + 1), |mean v (N / p ^ k) - mean v N|)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range (K + 1)) hk
  have hdef : ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ range (K + 1), |mean v (N / p ^ k) - mean v N| < ε / 4 :=
    hsum0.eventually_lt_const (by positivity)
  have hfloor : ∀ᶠ N : ℕ in atTop, ((K : ℝ) + 1) / N < ε / 4 :=
    (tendsto_const_div_atTop_nhds_zero_nat ((K : ℝ) + 1)).eventually_lt_const (by positivity)
  filter_upwards [hv, hdef, hfloor, eventually_ge_atTop (p ^ K)] with N hvN hdefN hfloorN hNK
  have hmain := abs_mean_sub_sum_mul_mean_le g hg hp (K := K) (N := N) hNK
  have hprod : |(∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k) * mean v N|
      ≤ (1 - 1 / (2 * (p : ℝ))) * A := by
    rw [abs_mul]
    exact mul_le_mul hE hvN (abs_nonneg _) hθ0
  calc |mean g N|
      ≤ |mean g N - (∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k) * mean v N|
        + |(∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k) * mean v N| := by
        simpa using abs_add_le (mean g N - (∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k)
          * mean v N) ((∑ k ∈ range (K + 1), g (p ^ k) / (p : ℝ) ^ k) * mean v N)
    _ ≤ (1 - 1 / (2 * (p : ℝ))) * A + ε := by
        have := hmain
        rw [← hvdef] at this
        linarith

/--
**Iterating the contraction over a finite set of bad primes.**  Assume Elliott's Lipschitz
estimate.  For a finite set `T` of primes `\ge 5` on which `g` takes the value `-1`,
`\limsup_N |\text{mean } g\ N| \le \prod_{q \in T}(1 - 1/(2q))`.

The induction removes one prime at a time: `Wirsing.coprimeRestrict g q` is again bounded
multiplicative, and it still takes the value `-1` at the primes of `T` not yet removed.
-/
@[category API, AMS 11]
theorem eventually_abs_mean_le_prod (hDI : DilationInvariant) (T : Finset ℕ) :
    ∀ g : ℕ → ℝ, IsBddMultiplicative g → (∀ q ∈ T, q.Prime ∧ 5 ≤ q ∧ g q = -1) →
      ∀ ε > 0, ∀ᶠ N in atTop, |mean g N| ≤ (∏ q ∈ T, (1 - 1 / (2 * (q : ℝ)))) + ε := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg _ ε hε
    filter_upwards with N
    simpa using (abs_mean_le_one_of_bdd hg N).trans (by linarith)
  | insert p T' hpT ih =>
    intro g hg hq ε hε
    obtain ⟨hp, hp5, hgp⟩ := hq p (Finset.mem_insert_self _ _)
    have h5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    have hθ0 : (0 : ℝ) ≤ 1 - 1 / (2 * (p : ℝ)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hθ1 : 1 - 1 / (2 * (p : ℝ)) ≤ 1 := by
      have : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by positivity
      linarith
    have hvm : IsBddMultiplicative (coprimeRestrict g p) :=
      isBddMultiplicative_coprimeRestrict hg hp
    have hq' : ∀ q ∈ T', q.Prime ∧ 5 ≤ q ∧ coprimeRestrict g p q = -1 := by
      intro q hqT
      obtain ⟨hqp, hq5, hgq⟩ := hq q (Finset.mem_insert_of_mem hqT)
      have hne : p ≠ q := fun h ↦ hpT (h ▸ hqT)
      have hnd : ¬ p ∣ q := fun hd ↦ hne ((Nat.prime_dvd_prime_iff_eq hp hqp).1 hd)
      exact ⟨hqp, hq5, by rw [coprimeRestrict_of_not_dvd hnd, hgq]⟩
    have hv := ih (coprimeRestrict g p) hvm hq' (ε / 2) (by linarith)
    have hstep := eventually_abs_mean_le hDI hg hp hp5 hgp (A := (∏ q ∈ T',
      (1 - 1 / (2 * (q : ℝ)))) + ε / 2) (ε := ε / 2) (by linarith) hv
    rw [Finset.prod_insert hpT]
    filter_upwards [hstep] with N hN
    nlinarith [hN, hθ0, hθ1]

/-- `\prod_{q \in T}(1 - 1/(2q)) \le \exp(-\sum_{q \in T} 1/(2q))`. -/
@[category API, AMS 11]
theorem prod_le_exp_neg_sum (T : Finset ℕ) (hT : ∀ q ∈ T, 5 ≤ q) :
    ∏ q ∈ T, (1 - 1 / (2 * (q : ℝ))) ≤ Real.exp (-∑ q ∈ T, 1 / (2 * (q : ℝ))) := by
  have hnn : ∀ q ∈ T, (0 : ℝ) ≤ 1 - 1 / (2 * (q : ℝ)) := by
    intro q hqT
    have h5 : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hT q hqT
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  calc ∏ q ∈ T, (1 - 1 / (2 * (q : ℝ)))
      ≤ ∏ q ∈ T, Real.exp (-(1 / (2 * (q : ℝ)))) :=
        Finset.prod_le_prod hnn (fun q _ ↦ by
          have := Real.add_one_le_exp (-(1 / (2 * (q : ℝ))))
          linarith)
    _ = Real.exp (-∑ q ∈ T, 1 / (2 * (q : ℝ))) := by
        rw [← Real.exp_sum, ← Finset.sum_neg_distrib]

/--
**From divergence to an arbitrarily contracting set of primes.**  For every bound `B` there is
a finite set `T` of primes `\ge 5` with `f q = -1` on `T` and `\sum_{q \in T} 1/q \ge B`.
-/
@[category API, AMS 11]
theorem exists_finset_badPrimes (f : ℕ → ℝ) (hdiv : Tendsto (badPrimeSum f) atTop atTop)
    (B : ℝ) : ∃ T : Finset ℕ, (∀ q ∈ T, q.Prime ∧ 5 ≤ q ∧ f q = -1) ∧
      B ≤ ∑ q ∈ T, 1 / (q : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (B + 1)).exists
  refine ⟨{q ∈ badPrimesLE f N | 5 ≤ q}, ?_, ?_⟩
  · intro q hqT
    simp only [Finset.mem_filter, badPrimesLE, Finset.mem_range] at hqT
    exact ⟨hqT.1.2.1, hqT.2, hqT.1.2.2⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not (badPrimesLE f N) (fun q ↦ 5 ≤ q)
      (fun q ↦ 1 / (q : ℝ))
    have hsub : {q ∈ badPrimesLE f N | ¬ 5 ≤ q} ⊆ ({2, 3} : Finset ℕ) := by
      intro q hqT
      simp only [Finset.mem_filter, badPrimesLE, Finset.mem_range] at hqT
      have hqp : q.Prime := hqT.1.2.1
      have hq5 : q < 5 := by omega
      have hq2 : 2 ≤ q := hqp.two_le
      interval_cases q <;> revert hqp <;> decide
    have hsmall : ∑ q ∈ {q ∈ badPrimesLE f N | ¬ 5 ≤ q}, 1 / (q : ℝ) ≤ 1 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ ↦ by positivity)) ?_
      norm_num
    have hBP : badPrimeSum f N = ∑ q ∈ badPrimesLE f N, 1 / (q : ℝ) := rfl
    rw [hBP] at hN
    linarith [hsplit, hsmall, hN]

/--
**The crux, modulo Elliott's Lipschitz estimate.**  If the bad primes have divergent reciprocal
sum then `\text{mean } f\ N \to 0`.
-/
@[category API, AMS 11]
theorem tendsto_mean_atTop_zero_of_dilationInvariant (hDI : DilationInvariant) (f : ℕ → ℝ)
    (hf : IsPMOneMultiplicative f) (hdiv : Tendsto (badPrimeSum f) atTop atTop) :
    Tendsto (mean f) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set B : ℝ := -2 * Real.log (ε / 4) with hB
  obtain ⟨T, hT, hTB⟩ := exists_finset_badPrimes f hdiv B
  have hexp : Real.exp (-∑ q ∈ T, 1 / (2 * (q : ℝ))) ≤ ε / 4 := by
    have hhalf : ∑ q ∈ T, 1 / (2 * (q : ℝ)) = (∑ q ∈ T, 1 / (q : ℝ)) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun q _ ↦ by ring
    have hge : B / 2 ≤ ∑ q ∈ T, 1 / (2 * (q : ℝ)) := by rw [hhalf]; linarith
    calc Real.exp (-∑ q ∈ T, 1 / (2 * (q : ℝ))) ≤ Real.exp (-(B / 2)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ε / 4 := by
          rw [hB]
          rw [show -(-2 * Real.log (ε / 4) / 2) = Real.log (ε / 4) by ring]
          exact Real.exp_log (by linarith)
  have hprod : (∏ q ∈ T, (1 - 1 / (2 * (q : ℝ)))) ≤ ε / 4 :=
    (prod_le_exp_neg_sum T fun q hqT ↦ (hT q hqT).2.1).trans hexp
  filter_upwards [eventually_abs_mean_le_prod hDI T f hf.isBddMultiplicative hT (ε / 4)
    (by linarith)] with N hN
  rw [Real.norm_eq_abs]
  linarith

end Wirsing
