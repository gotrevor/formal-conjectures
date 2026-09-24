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

variable (f : ℕ → ℝ)

/-- One step of the logarithmic average: `L(k+1) = L(k) + f(k+1)/(k+1)`. -/
@[category API, AMS 11]
theorem logMean_succ (k : ℕ) : logMean f (k + 1) = logMean f k + f (k + 1) / (k + 1) := by
  rw [logMean, logMean, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
  push_cast
  ring

/-- `|L|` is `1/m`-Lipschitz along `ℕ`: this is the only regularity the whole argument uses. -/
@[category API, AMS 11]
theorem abs_abs_logMean_sub_le (hf : IsPMOneMultiplicative f) {m : ℕ} (hm : 1 ≤ m) :
    abs (|logMean f m| - |logMean f (m - 1)|) ≤ 1 / m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hstep := logMean_succ f k
  have hfm : |f (k + 1)| = 1 := by
    rcases hf.pmOne (k + 1) (by omega) with h | h <;> rw [h] <;> norm_num
  calc abs (|logMean f (k + 1)| - |logMean f k|)
      ≤ |logMean f (k + 1) - logMean f k| := abs_abs_sub_abs_le_abs_sub _ _
  _ = 1 / ((k : ℝ) + 1) := by
        rw [hstep]
        simp only [add_sub_cancel_left, abs_div, hfm]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  _ = 1 / ((k + 1 : ℕ) : ℝ) := by push_cast; ring

/-- `L(1) = 1`. -/
@[category API, AMS 11]
theorem logMean_one (hf : IsPMOneMultiplicative f) : logMean f 1 = 1 := by
  simp [logMean, hf.map_one]

/-- The potential `Φ(N) = ∑_{n ≤ N} |L(n)|/n`.  Its increments are exactly `|L(N)|/N`. -/
noncomputable def potential (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, |logMean f n| / n

@[category API, AMS 11]
theorem potential_nonneg (N : ℕ) : 0 ≤ potential f N :=
  Finset.sum_nonneg fun n _ ↦ by positivity

@[category API, AMS 11]
theorem potential_succ (N : ℕ) :
    potential f (N + 1) = potential f N + |logMean f (N + 1)| / (N + 1) := by
  rw [potential, potential, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  push_cast
  ring

open scoped Classical in
/-- The bad-prime deficit `D(N) = ∑_{p ≤ N, f p = -1} (log p/p)·|L(⌊N/p⌋)|`. -/
noncomputable def badWeight (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter (fun p ↦ p.Prime ∧ f p = -1),
    Real.log p / p * |logMean f (N / p)|

open scoped Classical in
@[category API, AMS 11]
theorem badWeight_nonneg (N : ℕ) : 0 ≤ badWeight f N := by
  refine Finset.sum_nonneg fun p hp ↦ ?_
  have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have : 0 ≤ Real.log p / p := div_nonneg (Real.log_nonneg hpR) (by positivity)
  positivity

open scoped Classical in
@[category API, AMS 11]
theorem sum_one_sub_eq_two_mul_badWeight (hf : IsPMOneMultiplicative f) (N : ℕ) :
    (∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / p * ((1 - f p) * |logMean f (N / p)|))
      = 2 * badWeight f N := by
  have hstep : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 - f p) * |logMean f (N / p)|)
        = if f p = -1 then 2 * (Real.log p / p * |logMean f (N / p)|) else 0 := by
    intro p hp
    have hp1 : 1 ≤ p := (mem_Icc.1 (mem_filter.1 hp).1).1
    rcases hf.pmOne p hp1 with h | h
    · rw [h, if_neg (by norm_num)]; ring
    · rw [h, if_pos rfl]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, badWeight, Finset.filter_filter,
    Finset.mul_sum]

open scoped Classical in
/--
**The closed inequality.**  Combining the engine identity with the weight comparison:
$$|L(N)|\log N \le 2\Phi(N) - 2D(N) + 64(1 + \log N).$$

Everything on the right is a function of `N` alone; `D(N) \ge 0` carries the whole effect of
the hypothesis, and `Φ` is the potential whose telescoping drives the rest of the proof.
-/
@[category API, AMS 11]
theorem abs_logMean_mul_log_le_potential (hf : IsPMOneMultiplicative f) (N : ℕ) :
    |logMean f N| * Real.log N
      ≤ 2 * potential f N - 2 * badWeight f N + 64 * (1 + Real.log N) := by
  classical
  set g : ℕ → ℝ := fun n ↦ |logMean f n| with hg
  have hengine := abs_logMean_mul_log_le_of_forall_le f hf (N := N) g (fun M _ ↦ le_rfl)
  have hsplit : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / p * ((1 + f p) * g (N / p))
        = 2 * (Real.log p / p * g (N / p))
          - Real.log p / p * ((1 - f p) * g (N / p)) := fun p _ ↦ by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_one_sub_eq_two_mul_badWeight f hf N] at hengine
  -- the good-prime sum, compared with the potential
  have hcomp := abs_sum_primeWeight_comp_sub_sum_div_le g N (fun m hm2 _ ↦ by
    simpa only [hg] using abs_abs_logMean_sub_le f hf (by omega : 1 ≤ m))
  have hprime : ∑ k ∈ Icc 1 N, primeWeight k * g (N / k)
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * g (N / p) :=
    sum_primeWeight_mul (fun k ↦ g (N / k)) N
  have hg1 : g 1 = 1 := by rw [hg]; simp [logMean_one f hf]
  have hpot : ∑ n ∈ Icc 1 N, g n / n = potential f N := rfl
  rw [hprime, hg1, hpot] at hcomp
  have hle : ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p * g (N / p)
      ≤ potential f N + 11 + 16 * Real.log N := by
    have := (abs_le.1 hcomp).2
    simp only [abs_one] at this
    linarith
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlog4 : Real.log 4 ≤ 2 := log_four_le_two
  nlinarith [hengine, hle, hlog, hlog4]

/--
**The algebraic core of the telescoping.**  One step of `N ↦ Φ(N)/(\log N)^2`, with the
deficit `D` retained and the two error terms already in summable form.

Here `n = N`, `u = \log N`, `v = \log (N-1)`, `P₀ = Φ(N-1)`, `P₁ = Φ(N)`, `g = |L(N)|`.
The hypothesis `1 ≤ n(u - v)` is `\log N - \log(N-1) \ge 1/N`.
-/
@[category API, AMS 11]
theorem potential_step_algebra {n u v P₀ P₁ g D : ℝ}
    (hn : (0 : ℝ) < n) (hv : 0 < v) (hvu : v ≤ u) (hu : 1 ≤ u)
    (hnuv : 1 ≤ n * (u - v))
    (hP₁ : P₁ = P₀ + g / n) (hP₀ : 0 ≤ P₀) (hgu : g ≤ 1 + u)
    (hmain : g * u ≤ 2 * P₁ - 2 * D + 64 * (1 + u)) :
    P₁ / u ^ 2 + 2 * (D / (n * u ^ 3))
      ≤ P₀ / v ^ 2 + 128 * (1 / (n * u ^ 2)) + 4 * (1 / n ^ 2) := by
  rw [show 2 * (D / (n * u ^ 3)) = 2 * D / (n * u ^ 3) from by ring,
    show 128 * (1 / (n * u ^ 2)) = 128 / (n * u ^ 2) from by ring,
    show 4 * (1 / n ^ 2) = 4 / n ^ 2 from by ring]
  have hu0 : (0 : ℝ) < u := by linarith
  -- `Φ(N-1)` loses more from the denominator than the increment gains
  have hpoly : n * u * v ^ 2 + 2 * v ^ 2 ≤ n * u ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hnuv (show (0 : ℝ) ≤ u * (u + v) by positivity),
      mul_nonneg (sub_nonneg.2 hvu) (show (0 : ℝ) ≤ u + 2 * v by linarith)]
  have hcmp : P₀ / u ^ 2 + 2 * P₀ / (n * u ^ 3) ≤ P₀ / v ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hP₀)
      (sq_nonneg u), hP₀, hu0, hv, hn]
  have hid : P₁ / u ^ 2 = P₀ / u ^ 2 + g / (n * u ^ 2) := by
    rw [hP₁]; field_simp; try ring
  -- the engine bound, divided through by `n u³`
  have hrw : g / (n * u ^ 2) = g * u / (n * u ^ 3) := by
    field_simp; try ring
  have hkey2 : g / (n * u ^ 2) ≤ (2 * P₁ - 2 * D + 64 * (1 + u)) / (n * u ^ 3) := by
    rw [hrw]
    gcongr
  have hexp : (2 * P₁ - 2 * D + 64 * (1 + u)) / (n * u ^ 3)
      = 2 * P₀ / (n * u ^ 3) + 2 * g / (n ^ 2 * u ^ 3) - 2 * D / (n * u ^ 3)
        + 64 * (1 + u) / (n * u ^ 3) := by
    rw [hP₁]; field_simp; try ring
  -- the two error terms
  have herr1 : 2 * g / (n ^ 2 * u ^ 3) ≤ 4 / n ^ 2 := by
    have hcube : u ≤ u ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hu0.le (sub_nonneg.2 hu))
        (show (0 : ℝ) ≤ u + 1 by linarith)]
    have h1 : 2 * g ≤ 4 * u ^ 3 := by nlinarith [hgu, hu, hcube]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg n)]
  have herr2 : 64 * (1 + u) / (n * u ^ 3) ≤ 128 / (n * u ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (show 1 + u ≤ 2 * u by linarith)
      (show (0 : ℝ) ≤ 64 * (n * u ^ 2) by positivity)]
  rw [hexp] at hkey2
  linarith [hid, hcmp, hkey2, herr1, herr2]

/-- `1 ≤ log 3`, so `log N ≥ 1` for `N ≥ 3`. -/
@[category API, AMS 11]
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
  _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h

/-- `log(K+1) - log K ≥ 1/(K+1)`. -/
@[category API, AMS 11]
theorem one_div_le_log_succ_sub_log {K : ℕ} (hK : 1 ≤ K) :
    1 / ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 1) - Real.log K := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < (K : ℝ) / ((K : ℝ) + 1) by positivity)
  rw [Real.log_div (by linarith) (by linarith)] at h
  have he : (K : ℝ) / ((K : ℝ) + 1) - 1 = -(1 / ((K : ℝ) + 1)) := by
    field_simp
    ring
  linarith [he ▸ h]

open scoped Classical in
/-- One step of the telescoping of `Φ(N)/(\log N)^2`, at `N = K + 1 \ge 3`. -/
@[category API, AMS 11]
theorem potential_step (hf : IsPMOneMultiplicative f) {K : ℕ} (hK : 2 ≤ K) :
    potential f (K + 1) / Real.log ((K : ℝ) + 1) ^ 2
        + 2 * (badWeight f (K + 1) / (((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) ^ 3))
      ≤ potential f K / Real.log (K : ℝ) ^ 2
        + 128 * (1 / (((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) ^ 2))
        + 4 * (1 / ((K : ℝ) + 1) ^ 2) := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hv : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
  have hvu : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hu : 1 ≤ Real.log ((K : ℝ) + 1) :=
    le_trans one_le_log_three (Real.log_le_log (by norm_num) (by linarith))
  have hnuv : 1 ≤ ((K : ℝ) + 1) * (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ)) := by
    have h := one_div_le_log_succ_sub_log (K := K) (by omega)
    have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (K : ℝ) + 1 by linarith)
    rw [mul_one_div, div_self (by linarith : ((K : ℝ) + 1) ≠ 0)] at this
    linarith
  have hP₁ : potential f (K + 1)
      = potential f K + |logMean f (K + 1)| / ((K : ℝ) + 1) := potential_succ f K
  have hgu : |logMean f (K + 1)| ≤ 1 + Real.log ((K : ℝ) + 1) := by
    have := abs_logMean_le f hf (K + 1)
    push_cast at this
    exact this
  have hmain : |logMean f (K + 1)| * Real.log ((K : ℝ) + 1)
      ≤ 2 * potential f (K + 1) - 2 * badWeight f (K + 1)
        + 64 * (1 + Real.log ((K : ℝ) + 1)) := by
    have := abs_logMean_mul_log_le_potential f hf (K + 1)
    push_cast at this
    exact this
  exact potential_step_algebra (by linarith) hv hvu hu hnuv hP₁ (potential_nonneg f K)
    hgu hmain

open scoped Classical in
/-- The telescoped bound, accumulated from `N = 3` to `N = M`. -/
@[category API, AMS 11]
theorem potential_div_add_sum_le (hf : IsPMOneMultiplicative f) {M : ℕ} (hM : 2 ≤ M) :
    potential f M / Real.log M ^ 2
        + 2 * ∑ N ∈ Icc 3 M, badWeight f N / ((N : ℝ) * Real.log N ^ 3)
      ≤ potential f 2 / Real.log 2 ^ 2
        + 128 * ∑ N ∈ Icc 3 M, 1 / ((N : ℝ) * Real.log N ^ 2)
        + 4 * ∑ N ∈ Icc 3 M, 1 / (N : ℝ) ^ 2 := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have hstep := potential_step f hf hK
    rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ K + 1),
      Finset.sum_Icc_succ_top (by omega : 3 ≤ K + 1),
      Finset.sum_Icc_succ_top (by omega : 3 ≤ K + 1)]
    push_cast
    linarith [hstep, ih]

/-- `∑_{3 ≤ N ≤ M} 1/(N (log N)²) ≤ 1/log 2 - 1/log M`, by telescoping. -/
@[category API, AMS 11]
theorem sum_one_div_mul_log_sq_le {M : ℕ} (hM : 2 ≤ M) :
    ∑ N ∈ Icc 3 M, 1 / ((N : ℝ) * Real.log N ^ 2)
      ≤ 1 / Real.log 2 - 1 / Real.log M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hv : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
    have hvu : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hu : 1 ≤ Real.log ((K : ℝ) + 1) :=
      le_trans one_le_log_three (Real.log_le_log (by norm_num) (by linarith))
    have hnuv : 1 ≤ ((K : ℝ) + 1) * (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ)) := by
      have h := one_div_le_log_succ_sub_log (K := K) (by omega)
      have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (K : ℝ) + 1 by linarith)
      rw [mul_one_div, div_self (by linarith : ((K : ℝ) + 1) ≠ 0)] at this
      linarith
    have hkey : 1 / (((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) ^ 2)
        ≤ 1 / Real.log (K : ℝ) - 1 / Real.log ((K : ℝ) + 1) := by
      have hrw : 1 / Real.log (K : ℝ) - 1 / Real.log ((K : ℝ) + 1)
          = (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ))
              / (Real.log (K : ℝ) * Real.log ((K : ℝ) + 1)) := by
        field_simp
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hnuv
        (sq_nonneg (Real.log ((K : ℝ) + 1))), hv, hvu, hu]
    rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ K + 1)]
    push_cast
    linarith [ih, hkey]

/-- `∑_{3 ≤ N ≤ M} 1/N² ≤ 2`. -/
@[category API, AMS 11]
theorem sum_Icc_three_one_div_sq_le (M : ℕ) : ∑ N ∈ Icc 3 M, 1 / (N : ℝ) ^ 2 ≤ 2 := by
  have hsub : Icc 3 M ⊆ Icc 1 M := by
    intro n hn
    simp only [mem_Icc] at hn ⊢
    omega
  calc ∑ N ∈ Icc 3 M, 1 / (N : ℝ) ^ 2 ≤ ∑ N ∈ Icc 1 M, 1 / (N : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ by positivity
  _ ≤ 2 := sum_one_div_sq_le M

open scoped Classical in
/--
**Step D.**  The bad-prime deficit is summable against `1/(N(\log N)^3)`.

This is where the marginality of the single-scale Gronwall induction is bypassed: the
deficit is not converted into an improved constant at any one scale, it is accumulated
across all scales with the weight produced by differentiating `Φ(N)/(\log N)^2`.
-/
@[category API, AMS 11]
theorem exists_sum_badWeight_le (hf : IsPMOneMultiplicative f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ,
      ∑ N ∈ Icc 3 M, badWeight f N / ((N : ℝ) * Real.log N ^ 3) ≤ B := by
  set B : ℝ := (potential f 2 / Real.log 2 ^ 2 + 128 * (1 / Real.log 2) + 8) / 2 with hB
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hBnn : 0 ≤ B := by
    have := potential_nonneg f 2
    rw [hB]
    positivity
  refine ⟨B, hBnn, fun M ↦ ?_⟩
  rcases Nat.lt_or_ge M 3 with hM | hM
  · have hempty : Icc 3 M = (∅ : Finset ℕ) := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      simp only [mem_Icc] at hn
      omega
    rw [hempty, Finset.sum_empty]
    exact hBnn
  · have hM2 : 2 ≤ M := by omega
    have h1 := potential_div_add_sum_le f hf hM2
    have h2 := sum_one_div_mul_log_sq_le hM2
    have h3 := sum_Icc_three_one_div_sq_le M
    have h4 : 0 ≤ potential f M / Real.log M ^ 2 := by
      have := potential_nonneg f M
      positivity
    have h5 : 0 < Real.log M := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
      exact Real.log_pos (by linarith)
    have h6 : 0 ≤ 1 / Real.log M := by positivity
    rw [hB]
    linarith [h1, h2, h3, h4, h6]

end Wirsing
