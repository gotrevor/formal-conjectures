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
public import FormalConjectures.ErdosProblems.Wirsing.Rigidity

/-!
# The character collapse

At a near-extremal point `N` the rigidity relation reads `σ(⌊N/n⌋) ≈ sAf(n)`
(`Wirsing.mean_quotient_near_extremal`, `Wirsing.sum_bad_weight_le_step`).  Writing
`u = \log N` and `c(y) = f(p)` for a good prime `p` with `\log p ≈ yu`, the one-step and
two-step forms of that relation say
$$F((1-y)u) = sAc(y), \qquad F((1-y-z)u) = sAc(y)c(z),$$
so comparing the two-step value at `(p, q)` with the one-step value at a prime `r` of the
same size forces
$$c(y + z) = c(y)c(z),$$
i.e. `c` is a `\{\pm1\}`-valued character of `(\mathbb R_{\ge 0}, +)`.

The point of this file is that no structure theory of characters is needed: taking `q = p`
already gives `c(2y) = c(y)^2 = 1`, so `c` is **trivial** on the good range, i.e. `f(r) = 1`
for every good prime `r` that is multiplicatively close to the square of a good prime.  That
is the *squaring collapse* `Wirsing.eq_one_of_mean_quotient_sq_close`.

Both statements are consequences of `Wirsing.eq_of_mean_quotient_close`, which says that two
multiplicatively close quotients cannot carry opposite signs of a near-extremal `σ`.
-/

@[expose] public section

open Filter Finset

open scoped Topology

namespace Wirsing

variable (f : ℕ → ℝ)

/--
**The character relation.**  If `p`, `q` are good in the two-step sense at `N` and `r` is a
good prime at `N` whose quotient `⌊N/r⌋` is multiplicatively close to `⌊N/(pq)⌋`, then
`f(r) = f(p)f(q)`.

This is `c(y + z) = c(y)c(z)` in its usable finite form: it uses only the two rigidity
inequalities and the window step, no property of the primes.
-/
@[category API, AMS 11]
theorem eq_mul_of_mean_quotient_close (hf : IsPMOneMultiplicative f) {A ρ s : ℝ}
    {N p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hM : 1 ≤ N / (p * q)) (hMM' : N / (p * q) ≤ N / r) (hs : |s| = 1)
    (hgoodpq : A - ρ ≤ s * (f p * (f q * mean f (N / (p * q)))))
    (hgoodr : A - ρ ≤ s * (f r * mean f (N / r)))
    (hclose : (((N / r : ℕ) : ℝ) - ((N / (p * q) : ℕ) : ℝ)) / ((N / r : ℕ) : ℝ) < A - ρ) :
    f r = f p * f q := by
  have hxr : |f r| = 1 := abs_eq_one_of_one_le f hf hr.pos
  have hxp : |f p| = 1 := abs_eq_one_of_one_le f hf hp.pos
  have hxq : |f q| = 1 := abs_eq_one_of_one_le f hf hq.pos
  have hy : |f p * f q| = 1 := by rw [abs_mul, hxp, hxq, one_mul]
  refine eq_of_mean_quotient_close f hf hM hMM' hs hxr hy hgoodr ?_ hclose
  rw [show f p * f q * mean f (N / (p * q)) = f p * (f q * mean f (N / (p * q))) by ring]
  exact hgoodpq

/--
**The squaring collapse.**  The character relation at `q = p` gives `f(r) = f(p)^2 = 1`.

So at a near-extremal point every good prime `r` that is multiplicatively close to the square
of a good prime has `f(r) = 1`: the sign pattern of `f` on the good primes cannot be
anything but trivial.  This is the step that converts the rigidity of `σ` into rigidity of
`f` itself, and it is what the divergence hypothesis `\sum_p (1 - f(p))/p = \infty`
ultimately contradicts.
-/
@[category API, AMS 11]
theorem eq_one_of_mean_quotient_sq_close (hf : IsPMOneMultiplicative f) {A ρ s : ℝ}
    {N p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hM : 1 ≤ N / (p * p)) (hMM' : N / (p * p) ≤ N / r) (hs : |s| = 1)
    (hgoodpp : A - ρ ≤ s * (f p * (f p * mean f (N / (p * p)))))
    (hgoodr : A - ρ ≤ s * (f r * mean f (N / r)))
    (hclose : (((N / r : ℕ) : ℝ) - ((N / (p * p) : ℕ) : ℝ)) / ((N / r : ℕ) : ℝ) < A - ρ) :
    f r = 1 := by
  have h := eq_mul_of_mean_quotient_close f hf hp hp hr hM hMM' hs hgoodpp hgoodr hclose
  rcases hf.pmOne p hp.pos with hv | hv <;> rw [h, hv] <;> norm_num

/--
**The multiplicative period.**  Two applications of the character relation with the *same*
prime `q` cancel, because `f(q)^2 = 1`:
$$f(r_1) = f(r_0)f(q),\quad f(r_2) = f(r_1)f(q) \ \Longrightarrow\ f(r_2) = f(r_0).$$

So every good `q` is a *multiplicative period* of `f` along the good primes: `f` takes the
same value at scales `\log r` and `\log r + 2\log q`.  This is the form of the character
collapse that the density of the good set can actually supply — see
`Wirsing.eq_one_of_mean_quotient_sq_close` for the form that it cannot.
-/
@[category API, AMS 11]
theorem eq_of_character_step_two (hf : IsPMOneMultiplicative f) {q r₀ r₁ r₂ : ℕ}
    (hq : q.Prime) (h1 : f r₁ = f r₀ * f q) (h2 : f r₂ = f r₁ * f q) :
    f r₂ = f r₀ := by
  rw [h2, h1, mul_assoc]
  rcases hf.pmOne q hq.pos with hv | hv <;> rw [hv] <;> norm_num

/-! ### The good primes carry almost all of the Mertens weight -/

/-- `\log N \le \log(2M_0) + \log\lfloor N/M_0\rfloor` when `M_0 \le N`. -/
@[category API, AMS 11]
theorem log_le_log_two_mul_add_log_div {M₀ N : ℕ} (hM₀ : 1 ≤ M₀) (hMN : M₀ ≤ N) :
    Real.log N ≤ Real.log (2 * M₀) + Real.log (N / M₀ : ℕ) := by
  have hq1 : 1 ≤ N / M₀ := Nat.one_le_div_iff (by omega) |>.2 hMN
  have hnat : N < 2 * (M₀ * (N / M₀)) := by
    have hmod : M₀ * (N / M₀) + N % M₀ = N := Nat.div_add_mod N M₀
    have hlt : N % M₀ < M₀ := Nat.mod_lt _ (by omega)
    have hge : M₀ ≤ M₀ * (N / M₀) := Nat.le_mul_of_pos_right _ (by omega)
    set k := M₀ * (N / M₀) with hk
    set r := N % M₀ with hr
    omega
  have hqR : (0 : ℝ) < (N / M₀ : ℕ) := by exact_mod_cast hq1
  have hM1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
  have hM2 : (0 : ℝ) < 2 * (M₀ : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcast : (N : ℝ) ≤ (2 * (M₀ : ℝ)) * ((N / M₀ : ℕ) : ℝ) := by
    have h : ((N : ℕ) : ℝ) ≤ ((2 * (M₀ * (N / M₀)) : ℕ) : ℝ) := by exact_mod_cast hnat.le
    push_cast at h
    linarith
  calc Real.log N ≤ Real.log ((2 * (M₀ : ℝ)) * ((N / M₀ : ℕ) : ℝ)) :=
        Real.log_le_log hN0 hcast
    _ = Real.log (2 * M₀) + Real.log (N / M₀ : ℕ) :=
        Real.log_mul (ne_of_gt hM2) (ne_of_gt hqR)

/--
**Step 1 of the chain: the good primes have almost full Mertens weight.**  At a near-extremal
`N`, the primes `p` for which the rigidity relation is *not* nearly extremal carry weight
`O((\delta\log N + 1)/\rho)` by `Wirsing.sum_bad_weight_le`, while `rigidityPrimes M₀ N`
carries `\log N - \log(2M_0) + O(1)` by Mertens.  Subtracting:
$$\sum_{p \text{ good}} \frac{\log p}{p} \ \ge\ \log N - \log(2M_0) - (\log 4 + 8)
  - \frac{2\delta\log N + c(M_0)}{\rho + \delta}.$$

With `δ → 0` and `ρ` fixed this is `(1 - o(1))\log N`, which is what steps 2–4 consume.
-/
@[category API, AMS 11]
theorem sum_good_primeWeight_ge (hf : IsPMOneMultiplicative f) {A δ s ρ : ℝ} {M₀ N : ℕ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hM₀ : 1 ≤ M₀) (hMN : M₀ ≤ N) (hs : |s| = 1)
    (hub : ∀ M, M₀ ≤ M → |mean f M| ≤ A + δ)
    (hsN : A - δ ≤ s * mean f N) :
    Real.log N - Real.log (2 * M₀) - (Real.log 4 + 8)
        - (2 * δ * Real.log N + rigidityConst M₀) / (ρ + δ)
      ≤ ∑ p ∈ (rigidityPrimes M₀ N).filter
          (fun p ↦ A - ρ ≤ s * (f p * mean f (N / p))), Real.log p / p := by
  classical
  have hq1 : 1 ≤ N / M₀ := Nat.one_le_div_iff (by omega) |>.2 hMN
  -- the total Mertens weight of `rigidityPrimes`
  have htot : Real.log N - Real.log (2 * M₀) - (Real.log 4 + 8)
      ≤ ∑ p ∈ rigidityPrimes M₀ N, Real.log p / p := by
    have hme := Mertens.abs_sum_log_prime_div_sub_log_le (N := N / M₀) hq1
    have h1 := (abs_le.1 hme).1
    have h2 := log_le_log_two_mul_add_log_div hM₀ hMN
    rw [rigidityPrimes]
    linarith
  -- the bad primes
  have hbad := sum_bad_weight_le f hf hA0 hA1 hδ0 hδ1 hρ hM₀ hMN hs hub hsN
  -- split
  have hsplit : ∑ p ∈ (rigidityPrimes M₀ N).filter
        (fun p ↦ s * (f p * mean f (N / p)) < A - ρ), Real.log p / p
      + ∑ p ∈ (rigidityPrimes M₀ N).filter
        (fun p ↦ ¬ (s * (f p * mean f (N / p)) < A - ρ)), Real.log p / p
      = ∑ p ∈ rigidityPrimes M₀ N, Real.log p / p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hcongr : (rigidityPrimes M₀ N).filter
        (fun p ↦ ¬ (s * (f p * mean f (N / p)) < A - ρ))
      = (rigidityPrimes M₀ N).filter (fun p ↦ A - ρ ≤ s * (f p * mean f (N / p))) :=
    Finset.filter_congr fun p _ ↦ by simp [not_lt]
  rw [hcongr] at hsplit
  linarith

/-! ### The collapse over integers -/

/-- A window of ratio `c` has relative gap at most `1 - 1/c`. -/
@[category API, AMS 11]
theorem gap_lt_of_le_mul {A ρ c : ℝ} {M M' : ℕ} (hM : 0 < (M : ℝ)) (hc1 : 1 < c)
    (hMM' : (M : ℝ) ≤ (M' : ℝ)) (hcle : (M' : ℝ) ≤ c * M) (h : 1 - 1 / c < A - ρ) :
    (((M' : ℝ)) - (M : ℝ)) / (M' : ℝ) < A - ρ := by
  have hM' : 0 < (M' : ℝ) := lt_of_lt_of_le hM hMM'
  have hc0 : (0 : ℝ) < c := by linarith
  have hkey : ((M' : ℝ) - M) / M' = 1 - (M : ℝ) / M' := by field_simp
  have hge : 1 / c ≤ (M : ℝ) / (M' : ℝ) := by
    rw [div_le_div_iff₀ hc0 hM']
    linarith
  rw [hkey]
  linarith

/--
**The window step for integers.**  Two good integers whose quotients are multiplicatively
close carry the same value of `f`.

This is `Wirsing.eq_of_mean_quotient_close` with `x = f(m)`, `y = f(n)`; nothing about primes
is used there, which is exactly why the argument transfers to integers.
-/
@[category API, AMS 11]
theorem eq_of_window (hf : IsPMOneMultiplicative f) {A ρ s : ℝ} {N n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hM : 1 ≤ N / n) (hMM' : N / n ≤ N / m) (hs : |s| = 1)
    (hgn : A - ρ ≤ s * (f n * mean f (N / n)))
    (hgm : A - ρ ≤ s * (f m * mean f (N / m)))
    (hclose : (((N / m : ℕ) : ℝ) - ((N / n : ℕ) : ℝ)) / ((N / m : ℕ) : ℝ) < A - ρ) :
    f m = f n :=
  eq_of_mean_quotient_close f hf hM hMM' hs (abs_eq_one_of_one_le f hf hm)
    (abs_eq_one_of_one_le f hf hn) hgm hgn hclose

/--
**The collapse over integers.**  Two *coprime* good integers in one multiplicative window
force `f(nm) = 1`.

The window step makes `f(m) = f(n)`, and multiplicativity on coprime arguments then gives
`f(nm) = f(n)f(m) = f(n)^2 = 1`.

The coprimality is essential and is where this differs from the prime version: `f` is
multiplicative only on coprime arguments, so `f(n^2)` is *not* `f(n)^2` and is in fact
completely unconstrained.  The squaring happens in the character, never in `f` itself.  A
window of ratio `c` around `M` contains the coprime pair `M+1, M+2` as soon as
`M(c-1) \ge 2`, so the pair always exists once `M` is large — and, unlike for primes, counting
integers in a short multiplicative window is elementary
(`Wirsing.abs_harmonicSum_sub_sub_log_le`).
-/
@[category API, AMS 11]
theorem eq_one_of_coprime_window (hf : IsPMOneMultiplicative f) {A ρ s : ℝ} {N n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hcop : Nat.Coprime n m)
    (hM : 1 ≤ N / n) (hMM' : N / n ≤ N / m) (hs : |s| = 1)
    (hgn : A - ρ ≤ s * (f n * mean f (N / n)))
    (hgm : A - ρ ≤ s * (f m * mean f (N / m)))
    (hclose : (((N / m : ℕ) : ℝ) - ((N / n : ℕ) : ℝ)) / ((N / m : ℕ) : ℝ) < A - ρ) :
    f (n * m) = 1 := by
  have heq := eq_of_window f hf hn hm hM hMM' hs hgn hgm hclose
  rw [hf.map_mul_of_coprime n m hcop, heq]
  rcases hf.pmOne n hn with hv | hv <;> rw [hv] <;> norm_num

/-- A multiplicative window of ratio `c` around `M` contains the coprime pair `M+1, M+2`. -/
@[category API, AMS 11]
theorem coprime_succ_succ (M : ℕ) : Nat.Coprime (M + 1) (M + 2) := by
  unfold Nat.Coprime
  rw [show M + 2 = (M + 1) + 1 by ring, Nat.gcd_comm, Nat.gcd_rec]
  simp

end Wirsing

