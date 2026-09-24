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

end Wirsing
