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

end Wirsing
