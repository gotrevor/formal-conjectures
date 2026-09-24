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
public import FormalConjectures.ErdosProblems.Wirsing.Log

/-!
# The decay of the logarithmic average

The divergent case of Wirsing's theorem, in logarithmic form: if
$\sum_{f(p) = -1} 1/p = \infty$ then $L(N) = \sum_{n \le N} f(n)/n = o(\log N)$.

The argument runs on the *potential*
$$\Phi(N) = \sum_{n \le N} \frac{|L(n)|}{n},$$
whose increments are exactly $|L(N)|/N$.  The engine identity of
`FormalConjectures.ErdosProblems.Wirsing.Log`, combined with the comparison of the prime
weights $\log p/p$ with the harmonic weights $1/n$, closes into
$$|L(N)|\log N \le 2\Phi(N) - 2D(N) + O(\log N),$$
where $D(N) \ge 0$ collects the primes with $f(p) = -1$.  Telescoping
$\Phi(N)/(\log N)^2$ then makes $D$ summable against $1/(N(\log N)^3)$, and a Fubini swap
turns that summability into $\sum_{f(p) = -1} 1/p < \infty$.

*References:*
- [Wi67] Wirsing, E., Das asymptotische Verhalten von Summen über multiplikative Funktionen.
  Acta Math. Acad. Sci. Hung. (1967), 411-467.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-- Telescoping: a function on `ℕ` is its value at `1` plus the sum of its increments. -/
@[category API, AMS 11]
theorem eq_add_sum_sub (g : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    g M = g 1 + ∑ m ∈ Icc 2 M, (g m - g (m - 1)) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
    simp only [Nat.add_sub_cancel]
    linarith [ih]

/-- The hyperbola swap for the prime weights: `∑_{p ≤ N} ∑_{2 ≤ m ≤ N/p} = ∑_{2 ≤ m ≤ N} ∑_{p ≤ N/m}`. -/
@[category API, AMS 11]
theorem sum_Icc_div_comm (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, ∑ m ∈ Icc 2 (N / k), F k m)
      = ∑ m ∈ Icc 2 N, ∑ k ∈ Icc 1 (N / m), F k m := by
  refine Finset.sum_comm' ?_
  intro k m
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, hm2, hmk⟩
    have hkm : m * k ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmk
    have hkm' : k * m ≤ N := by rwa [Nat.mul_comm] at hkm
    have hmle : m ≤ m * k := Nat.le_mul_of_pos_right m (by omega)
    exact ⟨⟨hk1, (Nat.le_div_iff_mul_le (by omega)).2 hkm'⟩, hm2, by omega⟩
  · rintro ⟨⟨hk1, hkm⟩, hm2, hmN⟩
    have hkm' : k * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hkm
    have hkm'' : m * k ≤ N := by rwa [Nat.mul_comm] at hkm'
    have hkle : k ≤ k * m := Nat.le_mul_of_pos_right k (by omega)
    exact ⟨⟨hk1, by omega⟩, hm2, (Nat.le_div_iff_mul_le (by omega)).2 hkm''⟩

/-- The hyperbola swap for the harmonic weights. -/
@[category API, AMS 11]
theorem sum_Icc_le_comm (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 2 n, F n m)
      = ∑ m ∈ Icc 2 N, ∑ n ∈ Icc m N, F n m := by
  refine Finset.sum_comm' ?_
  intro n m
  simp only [Finset.mem_Icc]
  omega

/-- `log 2 ≤ 1`. -/
@[category API, AMS 11]
theorem log_two_le_one : Real.log 2 ≤ 1 :=
  le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)

/-- `log 4 ≤ 2`. -/
@[category API, AMS 11]
theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [this]
  linarith [log_two_le_one]

open scoped Classical in
/--
The two weight systems agree at every scale: `∑_{p ≤ ⌊N/m⌋} log p / p` and
`H(N) - H(m-1)` are both `log(N/m) + O(1)`.
-/
@[category API, AMS 11]
theorem abs_sum_primeWeight_div_sub_harmonicSum_sub_le {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) :
    |(∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1))| ≤ 16 := by
  have hN1 : 1 ≤ N := le_trans (by omega) hmN
  have hq : 1 ≤ N / m := (Nat.one_le_div_iff (by omega)).2 hmN
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hm1R : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    have : 1 ≤ m - 1 := by omega
    exact_mod_cast this
  -- the prime side
  have h1 := abs_sum_primeWeight_sub_harmonicSum_le (N / m)
  have h2 := log_le_harmonicSum (N / m)
  have h3 : harmonicSum (N / m) ≤ 1 + Real.log ((N / m : ℕ) : ℝ) := sum_one_div_le (N / m)
  -- the harmonic side
  have h4 := log_le_harmonicSum N
  have h5 : harmonicSum N ≤ 1 + Real.log N := sum_one_div_le N
  have h6 := log_le_harmonicSum (m - 1)
  have h7 : harmonicSum (m - 1) ≤ 1 + Real.log ((m - 1 : ℕ) : ℝ) := sum_one_div_le (m - 1)
  -- `log ⌊N/m⌋` against `log N - log (m-1)`
  have hX1 : Real.log ((N / m : ℕ) : ℝ) ≤ Real.log N - Real.log m := by
    have hle : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
    have hpos : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
    have := Real.log_le_log hpos hle
    rwa [Real.log_div (by linarith) (by linarith)] at this
  have hX2 : Real.log N - Real.log m - 1 ≤ Real.log ((N / m : ℕ) : ℝ) := by
    have := sub_log_le_one_add_log_div (N := N) (p := m) (by omega) hmN
    linarith
  have hm1 : Real.log ((m - 1 : ℕ) : ℝ) ≤ Real.log m :=
    log_natCast_mono (by omega)
  have hm2 : Real.log m ≤ Real.log 2 + Real.log ((m - 1 : ℕ) : ℝ) := by
    have hle : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by
      have : m ≤ 2 * (m - 1) := by omega
      exact_mod_cast this
    have := Real.log_le_log (by linarith) hle
    rwa [Real.log_mul (by norm_num) (by linarith)] at this
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [log_two_le_one, log_four_le_two, h1.1, h1.2]

open scoped Classical in
/-- The prime-weighted sum, expanded along the increments of `g`. -/
@[category API, AMS 11]
theorem sum_primeWeight_comp_eq (g : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Icc 1 N, primeWeight k * g (N / k))
      = g 1 * (∑ k ∈ Icc 1 N, primeWeight k)
        + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (∑ k ∈ Icc 1 (N / m), primeWeight k) := by
  have hterm : ∀ k ∈ Icc 1 N, primeWeight k * g (N / k)
      = primeWeight k * g 1 + ∑ m ∈ Icc 2 (N / k), primeWeight k * (g m - g (m - 1)) := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := mem_Icc.1 hk
    have hq : 1 ≤ N / k := (Nat.one_le_div_iff (by omega)).2 hkN
    have hpull : ∑ m ∈ Icc 2 (N / k), primeWeight k * (g m - g (m - 1))
        = primeWeight k * ∑ m ∈ Icc 2 (N / k), (g m - g (m - 1)) :=
      (Finset.mul_sum _ _ _).symm
    rw [eq_add_sum_sub g hq, hpull]
    ring
  have e1 : ∑ k ∈ Icc 1 N, primeWeight k * g 1 = g 1 * ∑ k ∈ Icc 1 N, primeWeight k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have e2 : ∀ m ∈ Icc 2 N, ∑ k ∈ Icc 1 (N / m), primeWeight k * (g m - g (m - 1))
      = (g m - g (m - 1)) * ∑ k ∈ Icc 1 (N / m), primeWeight k := by
    intro m _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    sum_Icc_div_comm N (fun k m ↦ primeWeight k * (g m - g (m - 1))), e1,
    Finset.sum_congr rfl e2]

/-- The harmonic sum, expanded along the increments of `g`. -/
@[category API, AMS 11]
theorem sum_div_eq_of_increments (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, g n / n)
      = g 1 * harmonicSum N
        + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)) := by
  have hterm : ∀ n ∈ Icc 1 N, g n / n
      = (1 : ℝ) / n * g 1 + ∑ m ∈ Icc 2 n, (1 : ℝ) / n * (g m - g (m - 1)) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.1 hn
    have hpull : ∑ m ∈ Icc 2 n, (1 : ℝ) / n * (g m - g (m - 1))
        = (1 : ℝ) / n * ∑ m ∈ Icc 2 n, (g m - g (m - 1)) :=
      (Finset.mul_sum _ _ _).symm
    rw [eq_add_sum_sub g hn1, hpull]
    ring
  have e1 : ∑ n ∈ Icc 1 N, (1 : ℝ) / n * g 1 = g 1 * harmonicSum N := by
    rw [harmonicSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ mul_comm _ _
  have e2 : ∀ m ∈ Icc 2 N, ∑ n ∈ Icc m N, (1 : ℝ) / n * (g m - g (m - 1))
      = (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)) := by
    intro m hm
    obtain ⟨hm2, hmN⟩ := mem_Icc.1 hm
    have hsub : harmonicSum N - harmonicSum (m - 1) = ∑ n ∈ Icc m N, (1 : ℝ) / n := by
      rw [harmonicSum_sub (m - 1) N (by omega)]
      congr 1
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hsub, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ mul_comm _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    sum_Icc_le_comm N (fun n m ↦ (1 : ℝ) / n * (g m - g (m - 1))), e1,
    Finset.sum_congr rfl e2]

/-- `∑_{2 ≤ m ≤ N} 1/m ≤ log N`. -/
@[category API, AMS 11]
theorem sum_Icc_two_one_div_le (N : ℕ) : ∑ m ∈ Icc 2 N, (1 : ℝ) / m ≤ Real.log N := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp [Real.log_one]
  · have hsub : harmonicSum N - harmonicSum 1 = ∑ n ∈ Icc 2 N, (1 : ℝ) / n := by
      rw [harmonicSum_sub 1 N (by omega)]
      congr 1
    have h1 : harmonicSum 1 = 1 := by simp [harmonicSum]
    have h2 : harmonicSum N ≤ 1 + Real.log N := sum_one_div_le N
    linarith [hsub, h1, h2]

open scoped Classical in
/--
**The weight comparison.**  For a `g` whose increments satisfy `|g m - g (m-1)| ≤ 1/m`,
the prime-weighted average `∑_{p ≤ N} (log p/p) g(⌊N/p⌋)` and the harmonic average
`∑_{n ≤ N} g(n)/n` differ by `O(|g 1| + log N)`.

This is the Fubini form of the comparison: both sides are expanded along the increments of
`g` and the inner weights are then `log(N/m) + O(1)` by Mertens' first theorem.
-/
@[category API, AMS 11]
theorem abs_sum_primeWeight_comp_sub_sum_div_le (g : ℕ → ℝ) (N : ℕ)
    (hg : ∀ m, 2 ≤ m → m ≤ N → |g m - g (m - 1)| ≤ 1 / m) :
    |(∑ k ∈ Icc 1 N, primeWeight k * g (N / k)) - ∑ n ∈ Icc 1 N, g n / n|
      ≤ 11 * |g 1| + 16 * Real.log N := by
  classical
  rw [sum_primeWeight_comp_eq g N, sum_div_eq_of_increments g N]
  have hBD : (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (∑ k ∈ Icc 1 (N / m), primeWeight k))
      - (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)))
      = ∑ m ∈ Icc 2 N, (g m - g (m - 1))
          * ((∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  have hrw : (g 1 * (∑ k ∈ Icc 1 N, primeWeight k)
        + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (∑ k ∈ Icc 1 (N / m), primeWeight k))
      - (g 1 * harmonicSum N
        + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)))
      = g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)
        + ∑ m ∈ Icc 2 N, (g m - g (m - 1))
            * ((∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1))) := by
    rw [← hBD]
    ring
  rw [hrw]
  have hhead : |g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)| ≤ 11 * |g 1| := by
    rw [abs_mul]
    have := abs_sum_primeWeight_sub_harmonicSum_le N
    have h4 := log_four_le_two
    nlinarith [abs_nonneg (g 1), abs_nonneg ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)]
  have htail : |∑ m ∈ Icc 2 N, (g m - g (m - 1))
      * ((∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1)))|
      ≤ 16 * Real.log N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbd : ∀ m ∈ Icc 2 N, |(g m - g (m - 1))
        * ((∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1)))|
        ≤ 16 * (1 / (m : ℝ)) := by
      intro m hm
      obtain ⟨hm2, hmN⟩ := mem_Icc.1 hm
      rw [abs_mul]
      have h1 := hg m hm2 hmN
      have h2 := abs_sum_primeWeight_div_sub_harmonicSum_sub_le hm2 hmN
      have hnn : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
      nlinarith [abs_nonneg (g m - g (m - 1)),
        abs_nonneg ((∑ k ∈ Icc 1 (N / m), primeWeight k)
          - (harmonicSum N - harmonicSum (m - 1)))]
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [← Finset.mul_sum]
    have := sum_Icc_two_one_div_le N
    linarith
  calc |g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)
      + ∑ m ∈ Icc 2 N, (g m - g (m - 1))
          * ((∑ k ∈ Icc 1 (N / m), primeWeight k) - (harmonicSum N - harmonicSum (m - 1)))|
      ≤ _ := abs_add_le _ _
  _ ≤ 11 * |g 1| + 16 * Real.log N := add_le_add hhead htail

end Wirsing
