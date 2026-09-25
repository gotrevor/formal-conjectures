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
# The coprime splitting of a bounded multiplicative function

Every `n ≥ 1` factors uniquely as `n = p^k m` with `p ∤ m`.  For a multiplicative `f` this gives
the **exact** identity
$$\sum_{n \le N} f(n) = \sum_{k \ge 0} f(p^k) \sum_{\substack{m \le N/p^k \\ p \nmid m}} f(m),$$
`Wirsing.sum_Icc_eq_sum_range_mul`, with no error term whatsoever.

The point of the identity is that dividing by `N` turns it into
`mean f N = ∑_k (f(p^k)/p^k)·mean v (N/p^k) + O(1/N)` with `v = f·1_{p \nmid ·}`, so if `mean v`
is asymptotically invariant under dilation by a fixed integer then
`limsup |mean f| ≤ |∑_k f(p^k)p^{-k}| · limsup |mean v|`.  When `f(p) = -1` the Euler factor
`∑_k f(p^k)p^{-k}` is at most `1 - 1/p + 1/(p(p-1)) < 1`, so each bad prime contracts the
`limsup` by a definite factor, and `∑_{p \text{ bad}} 1/p = \infty` drives it to `0`.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
- [El79] Elliott, P.D.T.A., Probabilistic number theory II (the Lipschitz estimate for mean
  values of multiplicative functions).
- [GHS19] Granville, A., Harper, A.J., Soundararajan, K., A new proof of Halász's theorem, and
  its consequences. Compositio Math. 155 (2019), 126-163.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/--
`f` is multiplicative and bounded by `1` on the positive integers.  This is the class the
coprime splitting lives in: `Wirsing.IsPMOneMultiplicative` is not closed under removing the
multiples of a prime, because the restricted function takes the value `0`.
-/
structure IsBddMultiplicative (f : ℕ → ℝ) : Prop where
  /-- `|f n| ≤ 1` for `n ≥ 1`. -/
  abs_le_one : ∀ n ≥ 1, |f n| ≤ 1
  /-- `f` is multiplicative on coprime arguments. -/
  map_mul_of_coprime : ∀ m n, m.Coprime n → f (m * n) = f m * f n
  /-- `f 1 = 1`. -/
  map_one : f 1 = 1

@[category API, AMS 11]
theorem IsPMOneMultiplicative.isBddMultiplicative {f : ℕ → ℝ} (hf : IsPMOneMultiplicative f) :
    IsBddMultiplicative f where
  abs_le_one n hn := by rcases hf.pmOne n hn with h | h <;> simp [h]
  map_mul_of_coprime := hf.map_mul_of_coprime
  map_one := hf.map_one

/-- `f` with the multiples of `p` removed: `coprimeRestrict f p n = f n` when `p ∤ n`, and `0`
otherwise. -/
noncomputable def coprimeRestrict (f : ℕ → ℝ) (p n : ℕ) : ℝ := if p ∣ n then 0 else f n

@[category API, AMS 11]
theorem coprimeRestrict_of_not_dvd {f : ℕ → ℝ} {p n : ℕ} (h : ¬ p ∣ n) :
    coprimeRestrict f p n = f n := by simp [coprimeRestrict, h]

@[category API, AMS 11]
theorem coprimeRestrict_of_dvd {f : ℕ → ℝ} {p n : ℕ} (h : p ∣ n) :
    coprimeRestrict f p n = 0 := by simp [coprimeRestrict, h]

@[category API, AMS 11]
theorem isBddMultiplicative_coprimeRestrict {f : ℕ → ℝ} (hf : IsBddMultiplicative f) {p : ℕ}
    (hp : p.Prime) : IsBddMultiplicative (coprimeRestrict f p) where
  abs_le_one n hn := by
    by_cases h : p ∣ n
    · simp [coprimeRestrict_of_dvd h]
    · simpa [coprimeRestrict_of_not_dvd h] using hf.abs_le_one n hn
  map_mul_of_coprime m n h := by
    by_cases hm : p ∣ m
    · rw [coprimeRestrict_of_dvd hm, coprimeRestrict_of_dvd (hm.mul_right n), zero_mul]
    · by_cases hn : p ∣ n
      · rw [coprimeRestrict_of_dvd hn, coprimeRestrict_of_dvd (hn.mul_left m), mul_zero]
      · have hmn : ¬ p ∣ m * n := fun hd ↦ (hp.dvd_mul.1 hd).elim hm hn
        rw [coprimeRestrict_of_not_dvd hmn, coprimeRestrict_of_not_dvd hm,
          coprimeRestrict_of_not_dvd hn, hf.map_mul_of_coprime m n h]
  map_one := by
    rw [coprimeRestrict_of_not_dvd (by simpa using hp.one_lt.ne'), hf.map_one]

/--
**The coprime splitting identity.**  Grouping `n ≤ N` by the exponent of `p` in `n`,
$$\sum_{n \le N} f(n)
  = \sum_{k = 0}^{\lfloor \log_p N\rfloor} f(p^k)
      \sum_{\substack{m \le N/p^k \\ p \nmid m}} f(m) .$$
This is exact: no error term, no hypothesis beyond multiplicativity of `f` on coprime
arguments.
-/
@[category API, AMS 11]
theorem sum_Icc_eq_sum_range_mul (f : ℕ → ℝ) (hf : IsBddMultiplicative f) {p : ℕ}
    (hp : p.Prime) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n
      = ∑ k ∈ range (Nat.log p N + 1),
          f (p ^ k) * ∑ m ∈ Icc 1 (N / p ^ k), coprimeRestrict f p m := by
  classical
  have hp0 : 0 < p := hp.pos
  have hmaps : ∀ n ∈ Icc 1 N, n.factorization p ∈ range (Nat.log p N + 1) := by
    intro n hn
    simp only [mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hN0 : N ≠ 0 := by omega
    rw [mem_range, Nat.lt_succ_iff, Nat.le_log_iff_pow_le hp.one_lt hN0]
    exact le_trans (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)) hn.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpk : 0 < p ^ k := pow_pos hp0 k
  have hinner : ∑ m ∈ Icc 1 (N / p ^ k), coprimeRestrict f p m
      = ∑ m ∈ {m ∈ Icc 1 (N / p ^ k) | ¬ p ∣ m}, f m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases h : p ∣ m
    · simp [coprimeRestrict_of_dvd h, h]
    · simp [coprimeRestrict_of_not_dvd h, h]
  rw [hinner, Finset.mul_sum]
  refine Finset.sum_nbij' (fun n ↦ n / p ^ k) (fun m ↦ p ^ k * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, hnk⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hpkn : p ^ k = p ^ n.factorization p := by rw [hnk]
    have hsplit : p ^ k * (n / p ^ k) = n := by
      rw [hpkn]; exact Nat.ordProj_mul_ordCompl_eq_self n p
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (n / p ^ k) with h | h
      · rw [h, mul_zero] at hsplit; omega
      · exact h
    · rw [Nat.le_div_iff_mul_le hpk, mul_comm]; omega
    · rw [hpkn]; exact Nat.not_dvd_ordCompl hp hn0
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm ⊢
    obtain ⟨⟨hm1, hm2⟩, hmp⟩ := hm
    have hm0 : m ≠ 0 := by omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · rw [Nat.le_div_iff_mul_le hpk, mul_comm] at hm2; exact hm2
    · rw [Nat.factorization_mul (by positivity) hm0]
      simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hmp]
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hnk⟩ := hn
    have hpkn : p ^ k = p ^ n.factorization p := by rw [hnk]
    rw [hpkn]; exact Nat.ordProj_mul_ordCompl_eq_self n p
  · intro m _
    exact Nat.mul_div_cancel_left m hpk
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hnk⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hpkn : p ^ k = p ^ n.factorization p := by rw [hnk]
    have hsplit : p ^ k * (n / p ^ k) = n := by
      rw [hpkn]; exact Nat.ordProj_mul_ordCompl_eq_self n p
    have hcop : (p ^ k).Coprime (n / p ^ k) := by
      rw [hpkn]
      exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
    conv_lhs => rw [← hsplit]
    exact hf.map_mul_of_coprime _ _ hcop

/-- `|mean f N| ≤ 1` for a bounded multiplicative `f`. -/
@[category API, AMS 11]
theorem abs_mean_le_one_of_bdd {f : ℕ → ℝ} (hf : IsBddMultiplicative f) (N : ℕ) :
    |mean f N| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN, mean]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mean, abs_div, abs_of_nonneg hNR.le, div_le_one hNR]
  calc |∑ n ∈ Icc 1 N, f n| ≤ ∑ n ∈ Icc 1 N, |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum fun n hn ↦ hf.abs_le_one n (Finset.mem_Icc.1 hn).1
    _ = (N : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- The geometric tail bound `∑_{a ≤ k < b} r^k ≤ r^a/(1-r)`. -/
@[category API, AMS 11]
theorem sum_Ico_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ k ∈ Finset.Ico a b, r ^ k ≤ r ^ a / (1 - r) := by
  have hsum : Summable fun k : ℕ ↦ r ^ k := summable_geometric_of_lt_one hr0 hr1
  have htl : ∑ i ∈ Finset.range (b - a), r ^ i ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact Summable.sum_le_tsum _ (fun i _ ↦ pow_nonneg hr0 i) hsum
  rw [Finset.sum_Ico_eq_sum_range]
  have hpull : ∑ i ∈ Finset.range (b - a), r ^ (a + i)
      = r ^ a * ∑ i ∈ Finset.range (b - a), r ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]
  rw [hpull, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left htl (pow_nonneg hr0 a)

/--
**The splitting identity in mean form.**  For `N ≥ 1`, with `v = f·1_{p ∤ ·}`,
$$\text{mean } f\ N
   = \sum_{k=0}^{\lfloor\log_p N\rfloor} f(p^k)\,
       \frac{\lfloor N/p^k\rfloor}{N}\,\text{mean } v\ \lfloor N/p^k\rfloor .$$
-/
@[category API, AMS 11]
theorem mean_eq_sum_range_mul (f : ℕ → ℝ) (hf : IsBddMultiplicative f) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (hN : 1 ≤ N) :
    mean f N = ∑ k ∈ range (Nat.log p N + 1),
      f (p ^ k) * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) *
        mean (coprimeRestrict f p) (N / p ^ k) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mean_eq_partialSum_div, partialSum, sum_Icc_eq_sum_range_mul f hf hp N, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hps : (∑ m ∈ Icc 1 (N / p ^ k), coprimeRestrict f p m)
      = ((N / p ^ k : ℕ) : ℝ) * mean (coprimeRestrict f p) (N / p ^ k) :=
    partialSum_eq_mul_mean (coprimeRestrict f p) (N / p ^ k)
  rw [hps]
  field_simp

/--
Pure bookkeeping for the one-step estimate: if `|A k - B k| ≤ d k` for `k ≤ K` and
`|A k| ≤ c^k` beyond `K`, then `∑_{k \le M} A - ∑_{k \le K} B` is within
`∑_{k \le K} d k + c^{K+1}/(1-c)`.
-/
@[category API, AMS 11]
theorem abs_sum_range_sub_sum_range_le {A B d : ℕ → ℝ} {K M : ℕ} (hKM : K + 1 ≤ M + 1)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hAB : ∀ k ∈ range (K + 1), |A k - B k| ≤ d k)
    (hA : ∀ k ∈ Finset.Ico (K + 1) (M + 1), |A k| ≤ c ^ k) :
    |∑ k ∈ range (M + 1), A k - ∑ k ∈ range (K + 1), B k|
      ≤ (∑ k ∈ range (K + 1), d k) + c ^ (K + 1) / (1 - c) := by
  have hsplit : ∑ k ∈ range (M + 1), A k
      = (∑ k ∈ range (K + 1), A k) + ∑ k ∈ Finset.Ico (K + 1) (M + 1), A k := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive A (Nat.zero_le (K + 1)) hKM]
  rw [hsplit, add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hAB)
  · exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hA)).trans
      (sum_Ico_pow_le hc0 hc1 _ _)

/--
**The one-step splitting estimate.**  With `v = f·1_{p ∤ ·}` and `p^K ≤ N`,
$$\Big|\text{mean } f\ N
   - \Big(\sum_{k \le K}\frac{f(p^k)}{p^k}\Big)\cdot \text{mean } v\ N\Big|
 \le \sum_{k \le K}\big|\text{mean } v\ \lfloor N/p^k\rfloor - \text{mean } v\ N\big|
     + \frac{K+1}{N} + \frac{1}{p^K} .$$
Every error term is explicit: `(K+1)/N` is the floor loss, `p^{-K}` the geometric tail of the
`k`-sum, and the first sum is the **dilation defect** of `mean v` — the only term that is not
visibly small, and the whole remaining content of Wirsing's theorem.
-/
@[category API, AMS 11]
theorem abs_mean_sub_sum_mul_mean_le (f : ℕ → ℝ) (hf : IsBddMultiplicative f) {p : ℕ}
    (hp : p.Prime) {K N : ℕ} (hKN : p ^ K ≤ N) :
    |mean f N - (∑ k ∈ range (K + 1), f (p ^ k) / (p : ℝ) ^ k) *
        mean (coprimeRestrict f p) N|
      ≤ (∑ k ∈ range (K + 1),
            |mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N|)
          + (K + 1) / N + 1 / (p : ℝ) ^ K := by
  have hv : IsBddMultiplicative (coprimeRestrict f p) := isBddMultiplicative_coprimeRestrict hf hp
  have hp1 : 1 < p := hp.one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  have hN : 1 ≤ N := le_trans (Nat.one_le_pow _ _ hp.pos) hKN
  have hN0 : N ≠ 0 := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKL : K ≤ Nat.log p N := (Nat.le_log_iff_pow_le hp1 hN0).2 hKN
  rw [mean_eq_sum_range_mul f hf hp hN, Finset.sum_mul]
  have hAB : ∀ k ∈ range (K + 1),
      |f (p ^ k) * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) * mean (coprimeRestrict f p) (N / p ^ k)
        - f (p ^ k) / (p : ℝ) ^ k * mean (coprimeRestrict f p) N|
      ≤ |mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N| + 1 / N := by
    intro k _
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    have hfk : |f (p ^ k)| ≤ 1 := hf.abs_le_one _ (Nat.one_le_pow _ _ hp.pos)
    have hq0 : (0 : ℝ) ≤ ((N / p ^ k : ℕ) : ℝ) / (N : ℝ) := by positivity
    have hq1 : ((N / p ^ k : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNR]
      exact_mod_cast Nat.cast_le.2 (Nat.div_le_self N (p ^ k))
    have hfloor : |((N / p ^ k : ℕ) : ℝ) / (N : ℝ) - 1 / (p : ℝ) ^ k| ≤ 1 / N := by
      have hkey : ((N / p ^ k : ℕ) : ℝ) / (N : ℝ) - 1 / (p : ℝ) ^ k
          = (((N / p ^ k : ℕ) : ℝ) - (N : ℝ) / ((p ^ k : ℕ) : ℝ)) / (N : ℝ) := by
        push_cast
        field_simp
      rw [hkey, abs_div, abs_of_nonneg hNR.le, div_le_div_iff_of_pos_right hNR]
      simpa using abs_natDiv_sub_div_le_one (N := N) (m := p ^ k) (Nat.one_le_pow _ _ hp.pos)
    have hexp : f (p ^ k) * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) *
          mean (coprimeRestrict f p) (N / p ^ k)
        - f (p ^ k) / (p : ℝ) ^ k * mean (coprimeRestrict f p) N
        = f (p ^ k) * ((((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) *
            (mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N))
          + f (p ^ k) * ((((N / p ^ k : ℕ) : ℝ) / (N : ℝ) - 1 / (p : ℝ) ^ k) *
            mean (coprimeRestrict f p) N) := by
      field_simp
      ring
    rw [hexp]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      calc |f (p ^ k)| * (|((N / p ^ k : ℕ) : ℝ) / (N : ℝ)| *
              |mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N|)
          ≤ 1 * (1 * |mean (coprimeRestrict f p) (N / p ^ k)
              - mean (coprimeRestrict f p) N|) := by
            have hq1abs : |((N / p ^ k : ℕ) : ℝ) / (N : ℝ)| ≤ 1 := by
              rw [abs_of_nonneg hq0]; exact hq1
            exact mul_le_mul hfk (mul_le_mul_of_nonneg_right hq1abs (abs_nonneg _))
              (by positivity) zero_le_one
        _ = |mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N| := by ring
    · rw [abs_mul, abs_mul]
      calc |f (p ^ k)| * (|((N / p ^ k : ℕ) : ℝ) / (N : ℝ) - 1 / (p : ℝ) ^ k| *
              |mean (coprimeRestrict f p) N|)
          ≤ 1 * ((1 / N) * 1) := by
            exact mul_le_mul hfk
              (mul_le_mul hfloor (abs_mean_le_one_of_bdd hv N) (abs_nonneg _) (by positivity))
              (by positivity) zero_le_one
        _ = 1 / N := by ring
  have hA : ∀ k ∈ Finset.Ico (K + 1) (Nat.log p N + 1),
      |f (p ^ k) * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) * mean (coprimeRestrict f p) (N / p ^ k)|
        ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k _
    have hfk : |f (p ^ k)| ≤ 1 := hf.abs_le_one _ (Nat.one_le_pow _ _ hp.pos)
    have hq0 : (0 : ℝ) ≤ ((N / p ^ k : ℕ) : ℝ) / (N : ℝ) := by positivity
    have hq : ((N / p ^ k : ℕ) : ℝ) / (N : ℝ) ≤ ((p : ℝ)⁻¹) ^ k := by
      have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
      have h1 : ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; ring
      rw [h2] at h1
      rw [div_le_iff₀ hNR, inv_pow, inv_mul_eq_div, le_div_iff₀ hpk]
      calc ((N / p ^ k : ℕ) : ℝ) * (p : ℝ) ^ k ≤ ((N : ℝ) / (p : ℝ) ^ k) * (p : ℝ) ^ k := by
            gcongr
        _ = (N : ℝ) := by field_simp
    rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    calc |f (p ^ k)| * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) *
            |mean (coprimeRestrict f p) (N / p ^ k)|
        ≤ 1 * (((p : ℝ)⁻¹) ^ k) * 1 := by
          exact mul_le_mul (mul_le_mul hfk hq hq0 zero_le_one)
            (abs_mean_le_one_of_bdd hv _) (abs_nonneg _) (by positivity)
      _ = ((p : ℝ)⁻¹) ^ k := by ring
  have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2p
  have hc0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hc1 : (p : ℝ)⁻¹ < 1 := by linarith
  have hmain := abs_sum_range_sub_sum_range_le (A := fun k ↦
      f (p ^ k) * (((N / p ^ k : ℕ) : ℝ) / (N : ℝ)) * mean (coprimeRestrict f p) (N / p ^ k))
    (B := fun k ↦ f (p ^ k) / (p : ℝ) ^ k * mean (coprimeRestrict f p) N)
    (d := fun k ↦ |mean (coprimeRestrict f p) (N / p ^ k) - mean (coprimeRestrict f p) N|
      + 1 / N) (by omega : K + 1 ≤ Nat.log p N + 1) hc0 hc1 hAB hA
  have hd : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
  have htail : ((p : ℝ)⁻¹) ^ (K + 1) / (1 - (p : ℝ)⁻¹) ≤ 1 / (p : ℝ) ^ K := by
    have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
    rw [div_le_div_iff₀ hd hpK]
    have hlhs : ((p : ℝ)⁻¹) ^ (K + 1) * (p : ℝ) ^ K = (p : ℝ)⁻¹ := by
      rw [inv_pow, pow_succ, mul_inv]
      field_simp
    rw [hlhs, one_mul]
    linarith
  refine hmain.trans ?_
  have hconst : ∑ _k ∈ range (K + 1), (1 / (N : ℝ)) = ((K : ℝ) + 1) / N := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [Finset.sum_add_distrib, hconst]
  linarith

end Wirsing
