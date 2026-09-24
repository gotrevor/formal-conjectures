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
public import FormalConjectures.ErdosProblems.Wirsing.Decay
public import FormalConjectures.ErdosProblems.Wirsing.Newman
public import FormalConjectures.ErdosProblems.Wirsing.Window

/-!
# The sharp weight comparison

Replacing the prime weights `\log p/p` by the harmonic weights `1/k` in an average
`\sum_k w_k\,g(\lfloor N/k\rfloor)` costs `O(\log N)` when Mertens' first theorem is used with
its `O(1)` error (`Wirsing.abs_sum_primeWeight_comp_sub_sum_div_le`, error `16\log N`), which
is the same size as the main term and therefore useless.  Laps 2-5 refuted three weight
transfers for exactly this reason.

With the *sharp* form `\sum_{p \le M}\log p/p = \log M - E + o(1)` — equivalent to the prime
number theorem, and proved in `Wirsing/Newman.lean` — the cost drops to `o(\log N)`.  The
mechanism is a telescoping: the discrepancy `\sum_{k \le M}\mathrm{primeWeight}(k) - H_M`
tends to the *constant* `-E - \gamma`, and a constant discrepancy integrates against `dg` to
`E\,(g(N) - g(1))`, which is `O(1)` for bounded `g` rather than `E` times the total variation
of `g`.

This file collects the pieces of that comparison.

*References:*
- [Me74] Mertens, F., Ein Beitrag zur analytischen Zahlentheorie. J. Reine Angew. Math. 78
  (1874), 46-62.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

open scoped Classical in
/--
**Sharp Mertens in `primeWeight` form**: `\sum_{k \le M}\mathrm{primeWeight}(k) - \log M`
converges.  This is `Newman.exists_tendsto_sum_log_prime_div_sub_log` with the prime filter
folded into `Wirsing.primeWeight`; the limit `-E` is Mertens' constant.
-/
@[category API, AMS 11]
theorem exists_tendsto_sum_primeWeight_sub_log :
    ∃ E : ℝ, Tendsto (fun M : ℕ ↦ (∑ k ∈ Icc 1 M, primeWeight k) - Real.log M) atTop (𝓝 (-E)) := by
  obtain ⟨E, hE⟩ := Newman.exists_tendsto_sum_log_prime_div_sub_log
  refine ⟨E, hE.congr fun M ↦ ?_⟩
  congr 1
  have := sum_primeWeight_mul (fun _ ↦ (1 : ℝ)) M
  simpa using this.symm

/--
`\log\lfloor N/m\rfloor` differs from `\log N - \log m` by at most `1/\lfloor N/m\rfloor`, and
the sign is determined: the floor only decreases the argument.
-/
@[category API, AMS 11]
theorem log_natCast_div_sub_le {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    Real.log ((N / m : ℕ) : ℝ) ≤ Real.log N - Real.log m ∧
      Real.log N - Real.log m
        ≤ Real.log ((N / m : ℕ) : ℝ) + 1 / ((N / m : ℕ) : ℝ) := by
  have hq1 : 1 ≤ N / m := (Nat.one_le_div_iff (by omega)).2 hmN
  have hqR : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hq1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hle : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hm0]
    have : (m * (N / m) : ℕ) ≤ N := by
      rw [mul_comm]; exact Nat.div_mul_le_self N m
    have h' : ((m * (N / m) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith [h']
  have hge : (N : ℝ) / (m : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
    have hlt : (N : ℕ) < m * (N / m + 1) := by
      have hdm := Nat.div_add_mod N m
      have hmod : N % m < m := Nat.mod_lt _ (by omega)
      have : m * (N / m + 1) = m * (N / m) + m := by ring
      omega
    have h' : (N : ℝ) < (m : ℝ) * (((N / m : ℕ) : ℝ) + 1) := by
      have := (Nat.cast_lt (α := ℝ)).2 hlt
      push_cast at this
      linarith
    rw [div_le_iff₀ hm0]
    linarith
  have hlogdiv : Real.log N - Real.log m = Real.log ((N : ℝ) / (m : ℝ)) := by
    rw [Real.log_div (ne_of_gt hN0) (ne_of_gt hm0)]
  constructor
  · rw [hlogdiv]
    exact Real.log_le_log (by linarith) hle
  · rw [hlogdiv]
    have h1 : Real.log ((N : ℝ) / (m : ℝ)) ≤ Real.log (((N / m : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) hge
    have h2 : Real.log (((N / m : ℕ) : ℝ) + 1) - Real.log ((N / m : ℕ) : ℝ)
        ≤ 1 / ((N / m : ℕ) : ℝ) := by
      have hq0 : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by linarith
      rw [← Real.log_div (by linarith) (ne_of_gt hq0)]
      have hkey : (((N / m : ℕ) : ℝ) + 1) / ((N / m : ℕ) : ℝ) = 1 + 1 / ((N / m : ℕ) : ℝ) := by
        field_simp
      rw [hkey]
      exact Real.log_le_sub_one_of_pos (by positivity) |>.trans (by ring_nf; rfl)
    linarith

/-- `\sum_{2 \le m \le N} \frac1{m(m-1)} = 1 - 1/N`. -/
@[category API, AMS 11]
theorem sum_Icc_one_div_mul_pred {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Icc 2 N, 1 / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hne : (n : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1), ih]
    push_cast
    have hne1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
    rw [h1]
    field_simp
    ring

/-- `\sum_{2 \le m \le N} \frac1{m(m-1)} \le 1`. -/
@[category API, AMS 11]
theorem sum_Icc_one_div_mul_pred_le (N : ℕ) :
    ∑ m ∈ Icc 2 N, 1 / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · rw [sum_Icc_one_div_mul_pred hN]
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith

open scoped Classical in
/--
**The sharp weight comparison.**  For every `\varepsilon > 0` there is a constant `C` such
that for every `g` with `|g| \le 1` and increments `|g(m) - g(m-1)| \le 1/m`,
$$\Bigl|\sum_{p \le N}\frac{\log p}{p}\,g(\lfloor N/p\rfloor) - \sum_{n \le N}\frac{g(n)}{n}
  \Bigr| \le \varepsilon\log N + C.$$

The error is `o(\log N)`, not `O(\log N)`: this is the pay-off of the prime number theorem
through sharp Mertens.  The mechanism is the telescoping of the *constant* part of the
discrepancy `D(m) = \sum_{k \le \lfloor N/m\rfloor}\mathrm{primeWeight}(k)
- (H_N - H_{m-1})`.  Writing `D(m) = -E + \eta(m)`, the constant contributes
`-E\,(g(N) - g(1))`, bounded by `2|E|` because `g` is bounded, while `\eta(m)` is small as
soon as `\lfloor N/m\rfloor` is large.  The `O(1)`-error version
`Wirsing.abs_sum_primeWeight_comp_sub_sum_div_le` cannot do this, because a discrepancy that
is merely bounded integrates against `dg` to the total variation of `g`, which is `\log N`.
-/
@[category API, AMS 11]
theorem exists_abs_sum_primeWeight_comp_sub_sum_div_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (g : ℕ → ℝ) (N : ℕ),
      (∀ m, 2 ≤ m → m ≤ N → |g m - g (m - 1)| ≤ 1 / m) → (∀ m, |g m| ≤ 1) →
        |(∑ k ∈ Icc 1 N, primeWeight k * g (N / k)) - ∑ n ∈ Icc 1 N, g n / n|
          ≤ ε * Real.log N + C := by
  classical
  obtain ⟨E, hE⟩ := exists_tendsto_sum_primeWeight_sub_log
  obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.1 hE (ε / 4) (by positivity)
  set M₀ : ℕ := max (max M₁ 1) ⌈4 / ε⌉₊ with hM₀def
  have hM₀1 : 1 ≤ M₀ := le_trans (le_max_right M₁ 1) (le_max_left _ _)
  have hM₀R : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
  have hlogM₀ : 0 ≤ Real.log M₀ := Real.log_nonneg hM₀R
  have hE0 : (0 : ℝ) ≤ |E| := abs_nonneg E
  have hM₀inv : 1 / (M₀ : ℝ) ≤ ε / 4 := by
    have hceil : (4 / ε : ℝ) ≤ (M₀ : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_right (max M₁ 1) ⌈4 / ε⌉₊
    rw [div_le_iff₀ (by linarith : (0:ℝ) < (M₀:ℝ))]
    rw [div_le_iff₀ hε] at hceil
    nlinarith [hceil]
  have hsharp : ∀ M : ℕ, M₀ ≤ M →
      |(∑ k ∈ Icc 1 M, primeWeight k) - Real.log M + E| ≤ ε / 4 := by
    intro M hM
    have hM₁M : M₁ ≤ M :=
      le_trans (le_trans (le_max_left M₁ 1) (le_max_left _ _)) hM
    have h := hM₁ M hM₁M
    rw [Real.dist_eq, sub_neg_eq_add] at h
    exact le_of_lt h
  refine ⟨11 + 2 * |E| + 2 + (16 + |E|) * (Real.log M₀ + 1) + (11 + 16 * Real.log M₀), ?_⟩
  intro g N hg hgb
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hcNN : (0 : ℝ) ≤ (16 + |E|) * (Real.log M₀ + 1) := by positivity
  rcases lt_or_ge N M₀ with hNlt | hNge
  · have h := abs_sum_primeWeight_comp_sub_sum_div_le g N hg
    have h1 : |g 1| ≤ 1 := hgb 1
    have h2 : Real.log N ≤ Real.log M₀ := log_natCast_mono (le_of_lt hNlt)
    have h3 : 0 ≤ ε * Real.log N := by positivity
    nlinarith [h, h1, h2, h3, hcNN, hE0, abs_nonneg (g 1)]
  · have hN1 : 1 ≤ N := le_trans hM₀1 hNge
    have hsumΔ : ∑ m ∈ Icc 2 N, (g m - g (m - 1)) = g N - g 1 := by
      have := eq_add_sum_sub g hN1
      linarith
    set D : ℕ → ℝ := fun m ↦ (∑ k ∈ Icc 1 (N / m), primeWeight k)
      - (harmonicSum N - harmonicSum (m - 1)) with hDdef
    -- the small-`η` estimate at the scales where `⌊N/m⌋` is large
    have heta : ∀ m, 2 ≤ m → m ≤ N → M₀ ≤ N / m →
        |D m + E| ≤ ε / 2 + 2 / ((m : ℝ) - 1) := by
      intro m hm2 hmN hQ
      have hm1 : 1 ≤ m - 1 := by omega
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      have hm1R : (1 : ℝ) ≤ (m : ℝ) - 1 := by
        rw [← hcast]; exact_mod_cast hm1
      have hA := hsharp (N / m) hQ
      have hB := abs_harmonicSum_sub_sub_log_le hm1 (by omega : m - 1 ≤ N)
      have hC := log_natCast_div_sub_le (by omega : 1 ≤ m) hmN
      have hQR : (M₀ : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hQ
      have hDiv : 1 / ((N / m : ℕ) : ℝ) ≤ ε / 4 := by
        refine le_trans ?_ hM₀inv
        exact one_div_le_one_div_of_le (by linarith) hQR
      have hstep := log_sub_le_one_div hm1
      have hmono : Real.log ((m - 1 : ℕ) : ℝ) ≤ Real.log m := log_natCast_mono (by omega)
      rw [hcast] at hB hstep hmono
      rw [show (m : ℝ) - 1 + 1 = (m : ℝ) by ring] at hstep
      have hinv : (0 : ℝ) < 1 / ((m : ℝ) - 1) := by positivity
      have hDval : D m + E = (∑ k ∈ Icc 1 (N / m), primeWeight k)
          - (harmonicSum N - harmonicSum (m - 1)) + E := by
        simp only [hDdef]
      have h2div : 2 / ((m : ℝ) - 1) = 2 * (1 / ((m : ℝ) - 1)) := by ring
      rw [abs_le] at hA hB
      rw [hDval, abs_le, h2div]
      constructor <;>
        linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, hDiv, hstep, hmono, hinv]
    -- the crude estimate at the remaining scales
    have hcrude : ∀ m, 2 ≤ m → m ≤ N → |D m + E| ≤ 16 + |E| := by
      intro m hm2 hmN
      have h := abs_sum_primeWeight_div_sub_harmonicSum_sub_le hm2 hmN
      have hDval : D m + E = (∑ k ∈ Icc 1 (N / m), primeWeight k)
          - (harmonicSum N - harmonicSum (m - 1)) + E := by simp only [hDdef]
      rw [hDval]
      calc |(∑ k ∈ Icc 1 (N / m), primeWeight k)
            - (harmonicSum N - harmonicSum (m - 1)) + E| ≤ _ := abs_add_le _ _
      _ ≤ 16 + |E| := by linarith [le_abs_self E, h]
    -- the two ranges, summed
    have h2 : |∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)|
        ≤ ε / 2 * Real.log N + 2 + (16 + |E|) * (Real.log M₀ + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 N) (fun m ↦ M₀ ≤ N / m)]
      have hS : ∑ m ∈ (Icc 2 N).filter (fun m ↦ M₀ ≤ N / m),
            |(g m - g (m - 1)) * (D m + E)|
          ≤ ε / 2 * Real.log N + 2 := by
        have hbd : ∀ m ∈ (Icc 2 N).filter (fun m ↦ M₀ ≤ N / m),
            |(g m - g (m - 1)) * (D m + E)|
              ≤ ε / 2 * (1 / (m : ℝ)) + 2 * (1 / ((m : ℝ) * ((m : ℝ) - 1))) := by
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm
          obtain ⟨⟨hm2, hmN⟩, hQ⟩ := hm
          have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
          have hb1 := hg m hm2 hmN
          have hb2 := heta m hm2 hmN hQ
          have hmul := mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity : (0:ℝ) ≤ 1 / (m:ℝ))
          rw [abs_mul]
          refine hmul.trans (le_of_eq ?_)
          have hne1 : (m : ℝ) ≠ 0 := by positivity
          have hne2 : (m : ℝ) - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
          field_simp
        refine (Finset.sum_le_sum hbd).trans ?_
        have hsub : ∑ m ∈ (Icc 2 N).filter (fun m ↦ M₀ ≤ N / m),
              (ε / 2 * (1 / (m : ℝ)) + 2 * (1 / ((m : ℝ) * ((m : ℝ) - 1))))
            ≤ ∑ m ∈ Icc 2 N, (ε / 2 * (1 / (m : ℝ)) + 2 * (1 / ((m : ℝ) * ((m : ℝ) - 1)))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i hi _
          have hi2 : (2 : ℝ) ≤ (i : ℝ) := by
            have := (Finset.mem_Icc.1 hi).1
            exact_mod_cast this
          have : (0:ℝ) < (i:ℝ) * ((i:ℝ) - 1) := by nlinarith
          positivity
        refine hsub.trans ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have ha := sum_Icc_two_one_div_le N
        have hb := sum_Icc_one_div_mul_pred_le N
        have hε2 : (0:ℝ) ≤ ε / 2 := by positivity
        nlinarith [ha, hb]
      have hSc : ∑ m ∈ (Icc 2 N).filter (fun m ↦ ¬ M₀ ≤ N / m),
            |(g m - g (m - 1)) * (D m + E)|
          ≤ (16 + |E|) * (Real.log M₀ + 1) := by
        have hbd : ∀ m ∈ (Icc 2 N).filter (fun m ↦ ¬ M₀ ≤ N / m),
            |(g m - g (m - 1)) * (D m + E)| ≤ (16 + |E|) * (1 / (m : ℝ)) := by
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm
          obtain ⟨⟨hm2, hmN⟩, -⟩ := hm
          rw [abs_mul, mul_comm]
          exact mul_le_mul (hcrude m hm2 hmN) (hg m hm2 hmN) (abs_nonneg _) (by positivity)
        refine (Finset.sum_le_sum hbd).trans ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        have hK1 : 1 ≤ N / M₀ := (Nat.one_le_div_iff (by omega)).2 hNge
        have hKN : N / M₀ ≤ N := Nat.div_le_self N M₀
        have hincl : (Icc 2 N).filter (fun m ↦ ¬ M₀ ≤ N / m) ⊆ Ioc (N / M₀) N := by
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm
          obtain ⟨⟨hm2, hmN⟩, hne⟩ := hm
          refine Finset.mem_Ioc.2 ⟨?_, hmN⟩
          by_contra hcon
          rw [not_lt] at hcon
          have h' := (Nat.le_div_iff_mul_le (by omega : 0 < M₀)).1 hcon
          exact hne ((Nat.le_div_iff_mul_le (by omega : 0 < m)).2 (by rw [mul_comm]; exact h'))
        have h1 : ∑ m ∈ (Icc 2 N).filter (fun m ↦ ¬ M₀ ≤ N / m), (1 : ℝ) / m
            ≤ ∑ m ∈ Ioc (N / M₀) N, (1 : ℝ) / m :=
          Finset.sum_le_sum_of_subset_of_nonneg hincl (fun i _ _ ↦ by positivity)
        have h2 : ∑ m ∈ Ioc (N / M₀) N, (1 : ℝ) / m
            = harmonicSum N - harmonicSum (N / M₀) := (harmonicSum_sub _ _ hKN).symm
        have h3 := harmonicSum_sub_le_log_sub hK1 hKN
        have h4 := (log_natCast_div_sub_le hM₀1 hNge).2
        have h5 : 1 / ((N / M₀ : ℕ) : ℝ) ≤ 1 := by
          have : (1 : ℝ) ≤ ((N / M₀ : ℕ) : ℝ) := by exact_mod_cast hK1
          rw [div_le_one (by linarith)]; linarith
        linarith [h1, h3, h4, h5]
      linarith [hS, hSc]
    -- assemble
    rw [sum_primeWeight_comp_eq g N, sum_div_eq_of_increments g N]
    have hsplitD : (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (∑ k ∈ Icc 1 (N / m), primeWeight k))
        - (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)))
        = ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * D m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ ↦ by simp only [hDdef]; ring
    have hshift : ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * D m
        = (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)) - E * (g N - g 1) := by
      have hexp : ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)
          = (∑ m ∈ Icc 2 N, (g m - g (m - 1)) * D m)
            + (∑ m ∈ Icc 2 N, (g m - g (m - 1))) * E := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ ↦ by ring
      rw [hexp, hsumΔ]
      ring
    have hmul : g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)
        = g 1 * (∑ k ∈ Icc 1 N, primeWeight k) - g 1 * harmonicSum N := by ring
    have hval : (g 1 * (∑ k ∈ Icc 1 N, primeWeight k)
          + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (∑ k ∈ Icc 1 (N / m), primeWeight k))
        - (g 1 * harmonicSum N
          + ∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (harmonicSum N - harmonicSum (m - 1)))
        = g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)
          + ((∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)) - E * (g N - g 1)) := by
      linarith [hsplitD, hshift, hmul]
    rw [hval]
    have hhead : |g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)| ≤ 11 := by
      rw [abs_mul]
      have h1 := abs_sum_primeWeight_sub_harmonicSum_le N
      have h4 := log_four_le_two
      have hg1 := hgb 1
      nlinarith [abs_nonneg (g 1),
        abs_nonneg ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)]
    have hEg : |E * (g N - g 1)| ≤ 2 * |E| := by
      rw [abs_mul]
      have h1 : |g N - g 1| ≤ 2 := by
        have := hgb N
        have := hgb 1
        calc |g N - g 1| ≤ |g N| + |g 1| := abs_sub _ _
        _ ≤ 2 := by linarith
      nlinarith [abs_nonneg E, abs_nonneg (g N - g 1)]
    have htail : |(∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)) - E * (g N - g 1)|
        ≤ (ε / 2 * Real.log N + 2 + (16 + |E|) * (Real.log M₀ + 1)) + 2 * |E| := by
      calc |(∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)) - E * (g N - g 1)|
          ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add h2 hEg
    calc |g 1 * ((∑ k ∈ Icc 1 N, primeWeight k) - harmonicSum N)
        + ((∑ m ∈ Icc 2 N, (g m - g (m - 1)) * (D m + E)) - E * (g N - g 1))|
        ≤ _ := abs_add_le _ _
    _ ≤ 11 + ((ε / 2 * Real.log N + 2 + (16 + |E|) * (Real.log M₀ + 1)) + 2 * |E|) :=
        add_le_add hhead htail
    _ ≤ ε * Real.log N + (11 + 2 * |E| + 2 + (16 + |E|) * (Real.log M₀ + 1)
        + (11 + 16 * Real.log M₀)) := by
      have : ε / 2 * Real.log N ≤ ε * Real.log N := by nlinarith
      linarith

end Wirsing
