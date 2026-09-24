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
# Multiplicative windows of integers

The rigidity window step needs to know that a multiplicative window `(M, N]` of fixed ratio
carries a definite amount of weight.  Over *primes* that is a PNT-strength statement: Mertens'
first theorem has an `O(1)` error, which swamps the `\log(N/M) = O(1)` weight of a short
window (see `Wirsing/Newman.lean`).

Over *integers* it is elementary and sharp.  Comparing `\sum_{M < n \le N} 1/n` with
`\int_M^N dt/t` termwise gives
$$0 \le \log(N/M) - \sum_{M < n \le N}\frac1n \le \frac1M - \frac1N,$$
so the harmonic weight of a window of ratio `c` is `\log c + O(1/M)` — an error that tends to
`0`, unlike Mertens'.

This is why the character collapse of `Wirsing/Character.lean` should be run over integers
rather than primes: the propagation step (rigidity from primes to all integers, by induction
on `\Omega(k)`) has to be done anyway, and once it is done the window population is free.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

/-- `1/(n+1) \le \log(n+1) - \log n` for `n \ge 1`. -/
@[category API, AMS 26]
theorem one_div_succ_le_log_sub {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hx : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  have hlog : Real.log ((n : ℝ) / ((n : ℝ) + 1)) = Real.log n - Real.log ((n : ℝ) + 1) :=
    Real.log_div (by linarith) (by linarith)
  have hval : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [hlog, hval] at h
  linarith

/-- `\log(n+1) - \log n \le 1/n` for `n \ge 1`. -/
@[category API, AMS 26]
theorem log_sub_le_one_div {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ)) = Real.log ((n : ℝ) + 1) - Real.log n :=
    Real.log_div (by linarith) (by linarith)
  have hval : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
    field_simp
    ring
  rw [hlog, hval] at h
  linarith

/-- The harmonic sum grows by `1/(N+1)`. -/
@[category API, AMS 11]
theorem harmonicSum_succ (N : ℕ) :
    harmonicSum (N + 1) = harmonicSum N + 1 / ((N : ℝ) + 1) := by
  rw [harmonicSum, harmonicSum, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  push_cast
  ring

/-- **The window sum is below the logarithm.** -/
@[category API, AMS 11]
theorem harmonicSum_sub_le_log_sub {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    harmonicSum N - harmonicSum M ≤ Real.log N - Real.log M := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn1 : 1 ≤ n := le_trans hM hn
    have hstep := one_div_succ_le_log_sub hn1
    rw [harmonicSum_succ]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- **The window sum is above the logarithm, up to `1/M - 1/N`.** -/
@[category API, AMS 11]
theorem log_sub_le_harmonicSum_sub {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    Real.log N - Real.log M ≤ harmonicSum N - harmonicSum M + 1 / (M : ℝ) - 1 / (N : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn1 : 1 ≤ n := le_trans hM hn
    have hstep := log_sub_le_one_div hn1
    rw [harmonicSum_succ]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/--
**The harmonic weight of a multiplicative window**, sharply:
$$\Bigl|\sum_{M < n \le N}\frac1n - \log\frac NM\Bigr| \le \frac1M.$$

The error tends to `0` with `M`, which is exactly what Mertens' first theorem cannot provide
for primes.  With `N = \lfloor cM\rfloor` the left side is `\log c + o(1)`, so every
multiplicative window of fixed ratio `c > 1` carries harmonic weight bounded away from `0`.
-/
@[category API, AMS 11]
theorem abs_harmonicSum_sub_sub_log_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    |harmonicSum N - harmonicSum M - (Real.log N - Real.log M)| ≤ 1 / (M : ℝ) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hM hMN
  have h1 := harmonicSum_sub_le_log_sub hM hMN
  have h2 := log_sub_le_harmonicSum_sub hM hMN
  have h3 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

end Wirsing
