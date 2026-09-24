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
# Wintner's mean value theorem

The convergent case of Wirsing's theorem is elementary.  Write `g = f * μ` for the Dirichlet
convolution, so that `f = 1 * g`, that is `f(n) = ∑_{d ∣ n} g(d)`.  Then

$$S(N) = \sum_{n \le N} f(n) = \sum_{d \le N} g(d) \lfloor N/d \rfloor,$$

so `σ(N) = ∑_{d ≤ N} g(d)/d + O\big(\tfrac1N \sum_{d \le N} |g(d)|\big)`.  If
`∑_d |g(d)|/d < ∞` both error and main term converge, and the mean value is `∑_d g(d)/d`.

This file develops the identity and the error bound.  The two limits and the summability of
`∑_d |g(d)|/d` (an Euler product estimate, which is where `∑_{f(p) = -1} 1/p < ∞` enters) are
separate.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
-/

@[expose] public section

open Filter Finset ArithmeticFunction

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/-- The Möbius transform `g = f * μ` of `f`, so that `f(n) = ∑_{d ∣ n} g(d)`. -/
noncomputable def wintnerCoeff (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * f x.2

/-- `f = 1 * g`: the defining property of the Möbius transform. -/
@[category API, AMS 11]
theorem sum_divisors_wintnerCoeff {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, wintnerCoeff f d = f n :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := wintnerCoeff f) (g := f)).2
    (fun _ _ ↦ by rw [wintnerCoeff]) n hn

/-- The divisor swap: `∑_{n ≤ N} ∑_{d ∣ n} h(d) = ∑_{d ≤ N} h(d) ⌊N/d⌋`. -/
@[category API, AMS 11]
theorem sum_sum_divisors_eq (N : ℕ) (h : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, h d)
      = ∑ d ∈ Icc 1 N, h d * ((N / d : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_comm' (s := Icc 1 N) (t := fun n ↦ n.divisors) (t' := Icc 1 N)
    (s' := fun d ↦ {n ∈ Icc 1 N | d ∣ n})
    (by
      intro n d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdn, hn0⟩
        have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by
          rintro rfl
          exact hn0 (Nat.eq_zero_of_zero_dvd hdn))
        exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, le_trans (Nat.le_of_dvd (by omega) hdn) hnN⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, hdN⟩
        exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_const, card_filter_dvd_Icc, nsmul_eq_mul]
  ring

/-- **Wintner's identity.**  `S(N) = ∑_{d ≤ N} g(d) ⌊N/d⌋`. -/
@[category API, AMS 11]
theorem partialSum_eq_sum_wintnerCoeff (N : ℕ) :
    partialSum f N = ∑ d ∈ Icc 1 N, wintnerCoeff f d * ((N / d : ℕ) : ℝ) := by
  rw [← sum_sum_divisors_eq N (wintnerCoeff f), partialSum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
  exact (sum_divisors_wintnerCoeff f (by omega : 0 < n)).symm

/--
**Wintner's error bound.**
`|σ(N) - ∑_{d ≤ N} g(d)/d| ≤ (1/N) ∑_{d ≤ N} |g(d)|`.
-/
@[category API, AMS 11]
theorem abs_mean_sub_sum_wintnerCoeff_div_le {N : ℕ} (hN : 1 ≤ N) :
    |mean f N - ∑ d ∈ Icc 1 N, wintnerCoeff f d / d|
      ≤ (1 / (N : ℝ)) * ∑ d ∈ Icc 1 N, |wintnerCoeff f d| := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hexp : mean f N - ∑ d ∈ Icc 1 N, wintnerCoeff f d / d
      = ∑ d ∈ Icc 1 N, wintnerCoeff f d * (((N / d : ℕ) : ℝ) / N - 1 / d) := by
    rw [mean_eq_partialSum_div, partialSum_eq_sum_wintnerCoeff, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  rw [hexp, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d hd ↦ ?_)
  have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hfl : |((N / d : ℕ) : ℝ) / N - 1 / d| ≤ 1 / (N : ℝ) := by
    have hkey : ((N / d : ℕ) : ℝ) / N - 1 / d
        = (((N / d : ℕ) : ℝ) - (N : ℝ) / d) / N := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hNpos]
    rw [div_le_div_iff₀ hNpos hNpos]
    nlinarith [abs_natDiv_sub_div_le_one (N := N) hd1, hNpos]
  rw [abs_mul]
  calc |wintnerCoeff f d| * |((N / d : ℕ) : ℝ) / N - 1 / d|
      ≤ |wintnerCoeff f d| * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hfl (abs_nonneg _)
    _ = 1 / (N : ℝ) * |wintnerCoeff f d| := by ring

/--
**Kronecker's lemma, in the form needed.**  If `∑ a_d` converges with `a_d ≥ 0`, then
`(1/N) ∑_{d ≤ N} d\,a_d → 0`.
-/
@[category API, AMS 11]
theorem tendsto_div_sum_mul_atTop_zero {a : ℕ → ℝ} (hnn : ∀ n, 0 ≤ a n) (ha : Summable a) :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℝ)) * ∑ d ∈ Icc 1 N, (d : ℝ) * a d) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpart : Tendsto (fun n ↦ ∑ i ∈ range n, a i) atTop (𝓝 (∑' i, a i)) :=
    ha.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at hpart
  obtain ⟨y, hy⟩ := hpart (ε / 2) (by linarith)
  -- the tail past `y` is small
  have htail : ∀ N : ℕ, ∑ d ∈ Icc (y + 1) N, a d ≤ ε / 2 := by
    intro N
    have hdisj : Disjoint (range (y + 1)) (Icc (y + 1) N) := by
      rw [Finset.disjoint_left]
      intro d hd hd2
      rw [Finset.mem_range] at hd
      rw [mem_Icc] at hd2
      omega
    have hle : ∑ d ∈ range (y + 1) ∪ Icc (y + 1) N, a d ≤ ∑' i, a i :=
      sum_le_hasSum _ (fun i _ ↦ hnn i) ha.hasSum
    rw [Finset.sum_union hdisj] at hle
    have hd := hy (y + 1) (by omega)
    rw [Real.dist_eq, abs_lt] at hd
    linarith [hd.1, hd.2]
  set C : ℝ := ∑ d ∈ Icc 1 y, (d : ℝ) * a d with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun d _ ↦ mul_nonneg (by positivity) (hnn d)
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C / ε)
  refine ⟨max (max y 1) m, fun N hN ↦ ?_⟩
  have hNy : y ≤ N := le_trans (le_trans (le_max_left y 1) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right y 1) (le_max_left _ _)) hN
  have hNm : m ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNm
  have hCN : C / N < ε / 2 := by
    rw [div_lt_iff₀ hNpos]
    have : 2 * C / ε < (N : ℝ) := lt_of_lt_of_le hm hmR
    rw [div_lt_iff₀ hε] at this
    linarith
  -- split the sum at `y`
  have hsplit : ∑ d ∈ Icc 1 N, (d : ℝ) * a d
      = C + ∑ d ∈ Icc (y + 1) N, (d : ℝ) * a d := by
    rw [hC, ← Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro d hd hd2
      rw [mem_Icc] at hd hd2
      omega)]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext d
    simp only [Finset.mem_union, mem_Icc]
    omega
  have hbig : ∑ d ∈ Icc (y + 1) N, (d : ℝ) * a d ≤ (N : ℝ) * (ε / 2) := by
    calc ∑ d ∈ Icc (y + 1) N, (d : ℝ) * a d
        ≤ ∑ d ∈ Icc (y + 1) N, (N : ℝ) * a d := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          have hdN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast (mem_Icc.1 hd).2
          exact mul_le_mul_of_nonneg_right hdN (hnn d)
      _ = (N : ℝ) * ∑ d ∈ Icc (y + 1) N, a d := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * (ε / 2) := mul_le_mul_of_nonneg_left (htail N) (by linarith)
  have hnn' : 0 ≤ ∑ d ∈ Icc 1 N, (d : ℝ) * a d :=
    Finset.sum_nonneg fun d _ ↦ mul_nonneg (by positivity) (hnn d)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (by positivity) hnn')]
  rw [hsplit]
  have hfinal : (1 / (N : ℝ)) * (C + (N : ℝ) * (ε / 2)) = C / N + ε / 2 := by
    field_simp
  calc (1 / (N : ℝ)) * (C + ∑ d ∈ Icc (y + 1) N, (d : ℝ) * a d)
      ≤ (1 / (N : ℝ)) * (C + (N : ℝ) * (ε / 2)) := by
        refine mul_le_mul_of_nonneg_left (by linarith [hbig]) (by positivity)
    _ = C / N + ε / 2 := hfinal
    _ < ε := by linarith

/-- The averaged error term of Wintner's bound tends to `0`. -/
@[category API, AMS 11]
theorem tendsto_avg_abs_wintnerCoeff
    (hsum : Summable (fun d : ℕ ↦ |wintnerCoeff f d| / d)) :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℝ)) * ∑ d ∈ Icc 1 N, |wintnerCoeff f d|)
      atTop (𝓝 0) := by
  have h := tendsto_div_sum_mul_atTop_zero (a := fun d : ℕ ↦ |wintnerCoeff f d| / d)
    (fun d ↦ by positivity) hsum
  refine h.congr fun N ↦ ?_
  refine congrArg _ (Finset.sum_congr rfl fun d hd ↦ ?_)
  have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith
  field_simp

/--
**Wintner's mean value theorem.**  If `∑_d |g(d)|/d < ∞` for `g = f * μ`, then `f` has the
mean value `∑_d g(d)/d`.
-/
@[category API, AMS 11]
theorem hasMeanValue_of_summable_wintnerCoeff
    (hsum : Summable (fun d : ℕ ↦ |wintnerCoeff f d| / d)) :
    HasMeanValue f (∑' d : ℕ, wintnerCoeff f d / d) := by
  have habs : (fun d : ℕ ↦ |wintnerCoeff f d| / d) = fun d : ℕ ↦ |wintnerCoeff f d / d| := by
    funext d
    rw [abs_div, Nat.abs_cast]
  rw [habs] at hsum
  have hsum' : Summable (fun d : ℕ ↦ wintnerCoeff f d / d) := hsum.of_abs
  have hmain : Tendsto (fun N : ℕ ↦ ∑ d ∈ Icc 1 N, wintnerCoeff f d / d) atTop
      (𝓝 (∑' d : ℕ, wintnerCoeff f d / d)) := by
    have hnat := hsum'.hasSum.tendsto_sum_nat
    have hshift : Tendsto (fun N : ℕ ↦ N + 1) atTop atTop :=
      tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ by omega) fun b ↦ ⟨b, by omega⟩
    refine (hnat.comp hshift).congr fun N ↦ ?_
    simp only [Function.comp_apply]
    rw [Finset.range_eq_Ico, show Finset.Ico 0 (N + 1) = insert 0 (Icc 1 N) from by
      ext d; simp only [Finset.mem_Ico, Finset.mem_insert, mem_Icc]; omega,
      Finset.sum_insert (by simp)]
    simp
  have herr : Tendsto (fun N : ℕ ↦ mean f N - ∑ d ∈ Icc 1 N, wintnerCoeff f d / d)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_
      (tendsto_avg_abs_wintnerCoeff f (by rw [habs]; exact hsum))
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact abs_mean_sub_sum_wintnerCoeff_div_le f hN
  have := herr.add hmain
  rw [zero_add] at this
  exact this.congr fun N ↦ by ring

/-- `g(d) = ∑_{e ∣ d} μ(e) f(d/e)`. -/
@[category API, AMS 11]
theorem wintnerCoeff_eq_sum_divisors (n : ℕ) :
    wintnerCoeff f n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f (n / d) := by
  rw [wintnerCoeff, Nat.sum_divisorsAntidiagonal
    (f := fun a b ↦ (ArithmeticFunction.moebius a : ℝ) * f b)]

/-- **The Möbius transform on prime powers:** `g(p^k) = f(p^k) - f(p^{k-1})`. -/
@[category API, AMS 11]
theorem wintnerCoeff_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    wintnerCoeff f (p ^ k) = f (p ^ k) - f (p ^ (k - 1)) := by
  rw [wintnerCoeff_eq_sum_divisors, Nat.sum_divisors_prime_pow hp]
  have hkey : ∀ x ∈ range (k + 1),
      (ArithmeticFunction.moebius (p ^ x) : ℝ) * f (p ^ k / p ^ x)
        = if x = 0 then f (p ^ k) else if x = 1 then -f (p ^ (k - 1)) else 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    have hxk : x ≤ k := by omega
    rw [Nat.pow_div hxk hp.pos]
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rcases eq_or_ne x 1 with rfl | hx1
      · simp [ArithmeticFunction.moebius_apply_prime hp]
      · rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg hx1,
          if_neg (by omega : ¬ x = 0), if_neg hx1]
        simp
  rw [Finset.sum_congr rfl hkey,
    show range (k + 1) = insert 0 (insert 1 (Finset.Icc 2 k)) from by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  rw [Finset.sum_eq_zero (fun x hx ↦ by
    have hx2 : 2 ≤ x := (Finset.mem_Icc.1 hx).1
    rw [if_neg (by omega : ¬ x = 0), if_neg (by omega : ¬ x = 1)])]
  norm_num [sub_eq_add_neg]

/-- `|g(p)| = 1 - f(p)`, the term of `Wirsing.pretentiousSeries` at `p`. -/
@[category API, AMS 11]
theorem abs_wintnerCoeff_prime (hf : IsPMOneMultiplicative f) {p : ℕ} (hp : p.Prime) :
    |wintnerCoeff f p| = 1 - f p := by
  have h : wintnerCoeff f (p ^ 1) = f (p ^ 1) - f (p ^ 0) :=
    wintnerCoeff_prime_pow f hp le_rfl
  rw [pow_one, pow_zero, hf.map_one] at h
  rw [h]
  rcases hf.pmOne p hp.pos with hval | hval
  · rw [hval]; norm_num
  · rw [hval]; norm_num

/-- `|g(p^k)| ≤ 2` for every `k ≥ 1`. -/
@[category API, AMS 11]
theorem abs_wintnerCoeff_prime_pow_le (hf : IsPMOneMultiplicative f) {p k : ℕ} (hp : p.Prime)
    (hk : 1 ≤ k) : |wintnerCoeff f (p ^ k)| ≤ 2 := by
  rw [wintnerCoeff_prime_pow f hp hk]
  have h1 : |f (p ^ k)| = 1 :=
    abs_eq_one_of_one_le f hf (Nat.one_le_pow _ _ hp.pos)
  have h2 : |f (p ^ (k - 1))| = 1 :=
    abs_eq_one_of_one_le f hf (Nat.one_le_pow _ _ hp.pos)
  calc |f (p ^ k) - f (p ^ (k - 1))| ≤ |f (p ^ k)| + |f (p ^ (k - 1))| := abs_sub _ _
    _ = 2 := by rw [h1, h2]; norm_num

open ArithmeticFunction in
/-- **`g = f * μ` is multiplicative.** -/
@[category API, AMS 11]
theorem wintnerCoeff_mul_of_coprime (hf : IsPMOneMultiplicative f) {m n : ℕ}
    (hmn : m.Coprime n) :
    wintnerCoeff f (m * n) = wintnerCoeff f m * wintnerCoeff f n := by
  classical
  set F : ArithmeticFunction ℝ := ⟨fun k ↦ if k = 0 then 0 else f k, by simp⟩ with hF
  have hFapp : ∀ k, k ≠ 0 → F k = f k := fun k hk ↦ by simp [hF, hk]
  have hFmul : ArithmeticFunction.IsMultiplicative F := by
    constructor
    · rw [hFapp 1 (by omega), hf.map_one]
    · intro a b hab
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [Nat.coprime_zero_left] at hab
        subst hab
        rw [Nat.zero_mul, hFapp 1 (by omega), hf.map_one, mul_one]
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · rw [Nat.coprime_zero_right] at hab
          subst hab
          rw [Nat.mul_zero, hFapp 1 (by omega), hf.map_one, one_mul]
        · have hab0 : a * b ≠ 0 := by positivity
          rw [hFapp _ hab0, hFapp _ (by omega), hFapp _ (by omega)]
          exact hf.map_mul_of_coprime a b hab
  have hgF : ∀ k, wintnerCoeff f k
      = (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * F) k := by
    intro k
    rw [wintnerCoeff, ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hx2 : x.2 ≠ 0 :=
      (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne'
    rw [hFapp _ hx2, ArithmeticFunction.intCoe_apply]
  rw [hgF, hgF, hgF]
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.mul hFmul).map_mul_of_coprime hmn

/-- `g(1) = 1`. -/
@[category API, AMS 11]
theorem wintnerCoeff_one (hf : IsPMOneMultiplicative f) : wintnerCoeff f 1 = 1 := by
  rw [wintnerCoeff]
  simp [hf.map_one]

/-- The local factor of `∑_d |g(d)|/d` at `p` is summable, dominated by `2 (1/p)^k`. -/
@[category API, AMS 11]
theorem summable_abs_wintnerCoeff_prime_pow_div (hf : IsPMOneMultiplicative f) {p : ℕ}
    (hp : p.Prime) :
    Summable (fun k : ℕ ↦ |wintnerCoeff f (p ^ k)| / ((p : ℝ) ^ k)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hdom : ∀ k, |wintnerCoeff f (p ^ k)| / ((p : ℝ) ^ k) ≤ 2 * (1 / (p : ℝ)) ^ k := by
    intro k
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    have hrw : 2 * (1 / (p : ℝ)) ^ k * (p : ℝ) ^ k = 2 := by
      rw [div_pow, one_pow]
      field_simp
    rw [div_le_iff₀ hpk, hrw]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, wintnerCoeff_one f hf]
      norm_num
    · exact abs_wintnerCoeff_prime_pow_le f hf hp hk
  refine Summable.of_nonneg_of_le (fun k ↦ by positivity) hdom ?_
  refine Summable.mul_left 2 (summable_geometric_of_lt_one (by positivity) ?_)
  rw [div_lt_one (by linarith)]
  linarith

/--
**The local Euler factor bound.**
`∑_k |g(p^k)|/p^k ≤ 1 + (1 - f(p))/p + 4/p²`.

The `k = 1` term is exactly the term of `Wirsing.pretentiousSeries` at `p`, and the tail
`k ≥ 2` is geometric with ratio `1/p ≤ 1/2`, hence at most `4/p²`.
-/
@[category API, AMS 11]
theorem tsum_abs_wintnerCoeff_prime_pow_div_le (hf : IsPMOneMultiplicative f) {p : ℕ}
    (hp : p.Prime) :
    ∑' k : ℕ, |wintnerCoeff f (p ^ k)| / ((p : ℝ) ^ k)
      ≤ 1 + (1 - f p) / p + 4 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  set a : ℕ → ℝ := fun k ↦ |wintnerCoeff f (p ^ k)| / ((p : ℝ) ^ k) with ha
  have hsum : Summable a := summable_abs_wintnerCoeff_prime_pow_div f hf hp
  have hsum1 : Summable (fun k ↦ a (k + 1)) := hsum.comp_injective (add_left_injective 1)
  have hsum2 : Summable (fun k ↦ a (k + 2)) := hsum.comp_injective (add_left_injective 2)
  -- peel the first two terms
  have hpeel : ∑' k, a k = a 0 + a 1 + ∑' k, a (k + 2) := by
    rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add]
    ring_nf
  have ha0 : a 0 = 1 := by
    rw [ha]
    simp only [pow_zero, div_one]
    rw [wintnerCoeff_one f hf]
    norm_num
  have ha1 : a 1 = (1 - f p) / p := by
    rw [ha]
    simp only [pow_one]
    rw [abs_wintnerCoeff_prime f hf hp]
  -- the geometric tail
  have hgeom : Summable (fun k : ℕ ↦ (1 / (p : ℝ)) ^ k) := by
    refine summable_geometric_of_lt_one (by positivity) ?_
    rw [div_lt_one hppos]
    linarith
  have htail : ∑' k, a (k + 2) ≤ 4 / (p : ℝ) ^ 2 := by
    have hdom : ∀ k, a (k + 2) ≤ 2 * (1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) ^ k := by
      intro k
      have hpk : (0 : ℝ) < (p : ℝ) ^ (k + 2) := by positivity
      have hrw : 2 * (1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) ^ k * (p : ℝ) ^ (k + 2) = 2 := by
        rw [div_pow, div_pow, one_pow, one_pow]
        field_simp
        rw [pow_add]
        ring
      rw [ha]
      simp only
      rw [div_le_iff₀ hpk, hrw]
      exact abs_wintnerCoeff_prime_pow_le f hf hp (by omega)
    have hle : ∑' k, a (k + 2)
        ≤ ∑' k : ℕ, 2 * (1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) ^ k :=
      hsum2.tsum_le_tsum hdom (hgeom.mul_left _)
    have hval : ∑' k : ℕ, 2 * (1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) ^ k
        = 2 * (1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by
        rw [div_lt_one hppos]; linarith)]
    rw [hval] at hle
    refine le_trans hle ?_
    rw [div_pow, one_pow]
    have hp2 : 1 / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hppos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hinv : (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by rw [sub_pos]; linarith) (by norm_num)]
      have h2 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [h2]
      linarith
    have h1 : (0 : ℝ) < 1 / (p : ℝ) ^ 2 := by positivity
    calc 2 * (1 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ))⁻¹
        ≤ 2 * (1 / (p : ℝ) ^ 2) * 2 := by
          refine mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 / (p : ℝ) ^ 2 := by ring
  rw [hpeel, ha0, ha1]
  linarith

/-- Each term of `Wirsing.pretentiousSeries` is nonnegative for a `±1`-valued `f`. -/
@[category API, AMS 11]
theorem pretentiousSeries_nonneg (hf : IsPMOneMultiplicative f) (p : Nat.Primes) :
    0 ≤ pretentiousSeries f p := by
  rw [pretentiousSeries]
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
    have := p.2.pos
    exact_mod_cast this
  refine div_nonneg ?_ hppos.le
  rcases hf.pmOne (p : ℕ) p.2.pos with h | h <;> rw [h] <;> norm_num

open scoped Classical in
/--
**The Euler product is bounded.**  The finite products of the local factors
`1 + (1 - f(p))/p + 4/p²` are bounded by a constant independent of the range.

This is where `∑_p (1 - f(p))/p < ∞` enters: `1 + x ≤ e^x`, so the product is at most
`\exp(∑_p (1 - f(p))/p + 8)`.
-/
@[category API, AMS 11]
theorem exists_bound_euler_product (hf : IsPMOneMultiplicative f)
    (h : Summable (pretentiousSeries f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      ∏ p ∈ (range M).filter Nat.Prime, (1 + (1 - f p) / p + 4 / (p : ℝ) ^ 2) ≤ C := by
  classical
  -- transfer the hypothesis to the `ℕ`-indexed extension
  have hinj : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ)) := Subtype.coe_injective
  have hzero : ∀ x ∉ Set.range (fun p : Nat.Primes ↦ (p : ℕ)), pretentiousTerm f x = 0 := by
    intro x hx
    rw [pretentiousTerm, if_neg]
    exact fun hp ↦ hx ⟨⟨x, hp⟩, rfl⟩
  have hcomp : pretentiousTerm f ∘ (fun p : Nat.Primes ↦ (p : ℕ)) = pretentiousSeries f := by
    funext p
    simp [pretentiousTerm, pretentiousSeries, p.2]
  have hterm : Summable (pretentiousTerm f) := by
    rw [← Function.Injective.summable_iff hinj hzero, hcomp]
    exact h
  set S : ℝ := ∑' n : ℕ, pretentiousTerm f n with hS
  refine ⟨Real.exp (S + 8), Real.exp_pos _, fun M ↦ ?_⟩
  -- each factor is `≤ exp` of its exponent
  have hfac : ∀ p ∈ (range M).filter Nat.Prime,
      1 + (1 - f p) / p + 4 / (p : ℝ) ^ 2
        ≤ Real.exp ((1 - f p) / p + 4 / (p : ℝ) ^ 2) := by
    intro p _
    have := Real.add_one_le_exp ((1 - f (p : ℕ)) / p + 4 / (p : ℝ) ^ 2)
    linarith
  have hnn : ∀ p ∈ (range M).filter Nat.Prime,
      0 ≤ 1 + (1 - f p) / p + 4 / (p : ℝ) ^ 2 := by
    intro p hp
    have hpp : p.Prime := (mem_filter.1 hp).2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h1 : 0 ≤ (1 - f (p : ℕ)) / p := by
      refine div_nonneg ?_ hppos.le
      rcases hf.pmOne p hpp.pos with hv | hv <;> rw [hv] <;> norm_num
    have h2 : (0 : ℝ) ≤ 4 / (p : ℝ) ^ 2 := by positivity
    linarith
  have hprod : ∏ p ∈ (range M).filter Nat.Prime, (1 + (1 - f p) / p + 4 / (p : ℝ) ^ 2)
      ≤ ∏ p ∈ (range M).filter Nat.Prime,
          Real.exp ((1 - f p) / p + 4 / (p : ℝ) ^ 2) :=
    Finset.prod_le_prod hnn hfac
  rw [← Real.exp_sum] at hprod
  refine le_trans hprod (Real.exp_le_exp.2 ?_)
  -- bound the exponent
  rw [Finset.sum_add_distrib]
  have hbad : ∑ p ∈ (range M).filter Nat.Prime, (1 - f p) / p ≤ S := by
    have hsub : ∑ p ∈ (range M).filter Nat.Prime, (1 - f p) / p
        = ∑ n ∈ range M, pretentiousTerm f n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [pretentiousTerm]
    rw [hsub, hS]
    exact sum_le_hasSum _ (fun n _ ↦ pretentiousTerm_nonneg f hf n) hterm.hasSum
  have hsq : ∑ p ∈ (range M).filter Nat.Prime, 4 / (p : ℝ) ^ 2 ≤ 8 := by
    have hsub : (range M).filter Nat.Prime ⊆ Icc 2 M := by
      intro p hp
      obtain ⟨hpr, hpp⟩ := mem_filter.1 hp
      rw [Finset.mem_range] at hpr
      exact mem_Icc.2 ⟨hpp.two_le, by omega⟩
    have hstep : ∑ p ∈ (range M).filter Nat.Prime, 4 / (p : ℝ) ^ 2
        ≤ ∑ n ∈ Icc 2 M, 4 / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ ↦ by positivity
    have hbase : ∑ n ∈ Icc 2 M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
      rcases Nat.lt_or_ge M 1 with hM | hM
      · have : Icc 2 M = (∅ : Finset ℕ) := by
          apply Finset.eq_empty_of_forall_notMem
          intro n hn
          rw [mem_Icc] at hn
          omega
        rw [this, Finset.sum_empty]
        norm_num
      · have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have := sum_Icc_one_div_sq_le M hM
        have hpos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
        linarith
    have hrw : ∑ n ∈ Icc 2 M, 4 / (n : ℝ) ^ 2
        = 4 * ∑ n ∈ Icc 2 M, (1 : ℝ) / (n : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ ↦ by ring
    rw [hrw] at hstep
    linarith
  linarith

/--
**The summability of the Möbius transform in the convergent case.**

`g = f * μ` is multiplicative, and on prime powers
`g(p) = f(p) - 1 ∈ \{0, -2\}`, `g(p^k) = f(p^k) - f(p^{k-1}) ∈ \{0, ±2\}`, so
`|g(p)| = 1 - f(p)` and `|g(p^k)| ≤ 2` for `k ≥ 2`.  Hence

    ∑_d |g(d)|/d  ≤  ∏_p (1 + (1 - f(p))/p + 4/p²),

and the product converges because `∑_p (1 - f(p))/p < ∞` is the hypothesis and
`∑_p 1/p² < ∞`.  Note the second factor is needed even when `f(p) = 1` for every `p`: the
higher prime powers `f(p^2)` are unconstrained by the hypothesis.

The comparison of a finite sum with the product is done through
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`: every nonzero `d`
below `M` is `M`-smooth, so any finite partial sum of the nonnegative summand is at most the
finite Euler product over `Nat.primesBelow M`, which is bounded uniformly by
`Wirsing.exists_bound_euler_product`.
-/
@[category API, AMS 11]
theorem summable_abs_wintnerCoeff_div (hf : IsPMOneMultiplicative f)
    (h : Summable (pretentiousSeries f)) :
    Summable (fun d : ℕ ↦ |wintnerCoeff f d| / d) := by
  classical
  set G : ℕ → ℝ := fun d ↦ |wintnerCoeff f d| / d with hG
  have hGnn : ∀ d, 0 ≤ G d := fun d ↦ by rw [hG]; positivity
  have hGnorm : ∀ d, ‖G d‖ = G d := fun d ↦ abs_of_nonneg (hGnn d)
  have hG1 : G 1 = 1 := by rw [hG]; simp [wintnerCoeff_one f hf]
  have hGmul : ∀ {m n : ℕ}, Nat.Coprime m n → G (m * n) = G m * G n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmn
      subst hmn
      rw [hG]
      simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [Nat.coprime_zero_right] at hmn
        subst hmn
        rw [hG]
        simp
      · have hmR : (m : ℝ) ≠ 0 := by positivity
        have hnR : (n : ℝ) ≠ 0 := by positivity
        rw [hG]
        simp only
        rw [wintnerCoeff_mul_of_coprime f hf hmn, abs_mul, Nat.cast_mul]
        field_simp
  have hGprime : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖G (p ^ k)‖) := by
    intro p hp
    have := summable_abs_wintnerCoeff_prime_pow_div f hf hp
    refine this.congr fun k ↦ ?_
    rw [hGnorm, hG]
    simp
  obtain ⟨C, hCpos, hC⟩ := exists_bound_euler_product f hf h
  refine summable_of_sum_le (c := C) (fun d ↦ hGnn d) fun u ↦ ?_
  -- bound the finite sum by the Euler product over a large enough range
  set M := u.sup id + 1 with hM
  have hsub : ∀ d ∈ u.erase 0, d ∈ M.smoothNumbers := by
    intro d hd
    obtain ⟨hd0, hdu⟩ := Finset.mem_erase.1 hd
    exact Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hd0)
      (by have := Finset.le_sup (f := id) hdu; simp only [id] at this; omega)
  obtain ⟨-, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := G) hG1 hGmul hGprime M
  have hfin : ∑ d ∈ u, G d ≤ ∏ p ∈ M.primesBelow, ∑' n : ℕ, G (p ^ n) := by
    have hzero : ∑ d ∈ u, G d = ∑ d ∈ u.erase 0, G d := by
      by_cases h0 : (0 : ℕ) ∈ u
      · rw [← Finset.sum_erase_add u _ h0]
        rw [hG]
        simp
      · rw [Finset.erase_eq_of_notMem h0]
    rw [hzero]
    set t : Finset M.smoothNumbers := (u.erase 0).subtype (· ∈ M.smoothNumbers) with ht
    have hval : ∑ m ∈ t, G m = ∑ d ∈ u.erase 0, G d := by
      rw [ht, Finset.sum_subtype_eq_sum_filter,
        Finset.filter_true_of_mem (fun d hd ↦ hsub d hd)]
    rw [← hval]
    exact sum_le_hasSum t (fun m _ ↦ hGnn m) hhas
  refine hfin.trans ?_
  refine le_trans (Finset.prod_le_prod (fun p _ ↦ ?_) (fun p hp ↦ ?_)) (hC M)
  · exact tsum_nonneg fun k ↦ hGnn _
  · have hpp : p.Prime := (Nat.mem_primesBelow.1 hp).2
    have := tsum_abs_wintnerCoeff_prime_pow_div_le f hf hpp
    refine le_trans (le_of_eq ?_) this
    refine tsum_congr fun k ↦ ?_
    rw [hG]
    simp

/-- The convergent case of Wirsing's theorem. -/
@[category API, AMS 11]
theorem exists_hasMeanValue_of_summable' (hf : IsPMOneMultiplicative f)
    (h : Summable (pretentiousSeries f)) : ∃ L, HasMeanValue f L :=
  ⟨_, hasMeanValue_of_summable_wintnerCoeff f (summable_abs_wintnerCoeff_div f hf h)⟩


end Wirsing
