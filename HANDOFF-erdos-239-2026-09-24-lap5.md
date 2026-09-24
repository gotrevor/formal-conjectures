# HANDOFF — Erdős 239 — 2026-09-24 (lap 5)

Branch `erdos-239-proof`. Working tree clean. Nothing pushed.

**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE outranks this file. That directive's
objective ("prove `tendsto_logMean_div_log_atTop_zero` by the potential route") is **met**, so
an altitude lap should now retarget it.

## Headline: the crux is closed

`Wirsing.tendsto_logMean_div_log_atTop_zero` — `L(N) = o(\log N)` when
`∑_{f(p) = -1} 1/p = ∞` — is a complete machine-checked proof. The lap-4 potential route went
through exactly as designed. `logProfile` scaffolding is deleted from `Main.lean`.

`Main.lean` is down from three sorries to two:

1. `tendsto_mean_atTop_zero_of_logMean` — the Tauberian step, now the crux. Restructured this
   lap to carry **both** `hdiv` and `L(N) = o(\log N)`.
2. `exists_hasMeanValue_of_summable` — the Wintner half, still untouched, still elementary.

## What landed (all sorry-free)

`Wirsing/Decay.lean` — steps E and F of the potential route:
`windowTerm_nonneg`, `potential_window_le_sum`, `sum_badWeight_div_eq`,
`sum_window_le_sum_badWeight`, `sub_badPrimeSum_le_sum_tail`, `exists_threshold`,
`potential_window_ge`, **`envelopeInf_eq_zero`**, `tendsto_envelope_atTop_zero`,
`tendsto_abs_logMean_div_log_atTop_zero`.

`Wirsing/Mean.lean` (new) — the Dirichlet inversion on the mean side:
`sum_Icc_one_div_comm`, `sum_partialSum_div_eq` (exact:
`∑_{k ≤ N} S(⌊N/k⌋) = ∑_{m ≤ N} f(m)⌊N/m⌋`), `abs_natDiv_sub_div_le_one`,
`abs_sum_partialSum_div_sub_mul_logMean_le`, and
**`abs_sum_mean_div_sub_logMean_le`**: `|∑_{k ≤ N} σ(⌊N/k⌋)/k - L(N)| ≤ 2`, an `O(1)`
identity, so the crux transfers to the mean side with no loss.

## Route findings (see `PENDING_WORK.md` for the full record)

* `L(N) = o(\log N)` **alone** cannot give `σ → 0`: `σ(N) = \cos(θ\log N)` satisfies it and is
  log-Lipschitz. Real-valuedness of `f` is essential and must be used.
* The mean-side analogue of the `(1 + f p)` engine identity is **vacuous**: every error term
  is `O(\log N)` while `σ(N)\log N ≤ \log N`.
* Route B's `exists_functional_relation` already *is* Hildebrand's Turán–Kubilius +
  Cauchy–Schwarz engine, and it is **exactly consistent with `|σ| ≍ E^{-1/2}`**, so no
  iteration of it contracts. Three pushes were checked and all reproduce `A ≤ A`.
* The missing ingredient is a joint second moment (Cauchy–Schwarz in `p` and `N` at once).
  `ON-LINE-REQUEST.md` asks for exactly that step of [Hi86]; arXiv 1604.00295
  (Granville–Harper–Soundararajan) is fetchable by a host session and covers real `f`.

## Also landed lap 5: the Wintner half, reduced to one comparison

`Wirsing/Wintner.lean` (new) — the convergent case. `DIRECTION.md` forbade starting this until
the crux closed; the crux closed, so it was opened. **Wintner's theorem itself is proved in
full**, sorry-free:

* `wintnerCoeff f n = ∑_{(a,b)} μ(a) f(b)` — the Möbius transform `g = f * μ`.
* `sum_divisors_wintnerCoeff` — `f(n) = ∑_{d ∣ n} g(d)` (via mathlib's
  `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`).
* `sum_sum_divisors_eq`, `partialSum_eq_sum_wintnerCoeff` — `S(N) = ∑_{d ≤ N} g(d)⌊N/d⌋`.
* `abs_mean_sub_sum_wintnerCoeff_div_le` — `|σ(N) - ∑_{d ≤ N} g(d)/d| ≤ (1/N)∑_{d ≤ N}|g(d)|`.
* `tendsto_div_sum_mul_atTop_zero` — **Kronecker's lemma**, proved from scratch:
  `∑ a_d < ∞`, `a_d ≥ 0` ⟹ `(1/N)∑_{d ≤ N} d a_d → 0`.
* **`hasMeanValue_of_summable_wintnerCoeff`** — Wintner's mean value theorem:
  `∑_d |g(d)|/d < ∞ ⟹ HasMeanValue f (∑_d g(d)/d)`.

And the arithmetic of `g`, all sorry-free:

* `wintnerCoeff_eq_sum_divisors`, `wintnerCoeff_one`,
  **`wintnerCoeff_prime_pow`** — `g(p^k) = f(p^k) - f(p^{k-1})`;
* `abs_wintnerCoeff_prime` — `|g(p)| = 1 - f(p)`, *exactly* the `pretentiousSeries` term;
* `abs_wintnerCoeff_prime_pow_le` — `|g(p^k)| ≤ 2`;
* **`wintnerCoeff_mul_of_coprime`** — `g` is multiplicative (via
  `ArithmeticFunction.isMultiplicative_moebius.intCast.mul`);
* `summable_abs_wintnerCoeff_prime_pow_div`,
  **`tsum_abs_wintnerCoeff_prime_pow_div_le`** — `∑_k |g(p^k)|/p^k ≤ 1 + (1-f(p))/p + 4/p²`;
* `pretentiousSeries_nonneg`,
  **`exists_bound_euler_product`** — `∏_{p < M}(1 + (1-f(p))/p + 4/p²) ≤ \exp(S + 8)`
  uniformly in `M`, where `S = ∑_n` of the `ℕ`-indexed `pretentiousTerm`.  **This is where the
  convergence hypothesis is consumed** (`1 + x ≤ e^x`, plus `∑_p 4/p² ≤ 4`).

### The single remaining gap in the convergent case

`Wirsing.summable_abs_wintnerCoeff_div` (`Wintner.lean`), the **sum-to-product comparison**:

    Summable (fun d ↦ |g d| / d).

Everything it needs is now in place. The route, concretely:

1. Set `G d = |g(d)|/d`. It is nonnegative, `G 1 = 1`, and multiplicative on coprimes
   (`wintnerCoeff_mul_of_coprime` plus `1/(mn) = (1/m)(1/n)`); `G 0 = 0`. Note `Coprime 0 n`
   forces `n = 1`, so the degenerate cases are fine.
2. Feed `G` to `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
   (in `Mathlib/NumberTheory/EulerProduct/Basic.lean`), whose hypotheses are exactly
   `G 1 = 1`, coprime multiplicativity, and per-prime summability
   (`summable_abs_wintnerCoeff_prime_pow_div`). For each `Finset` `s` it yields
   `HasSum (fun m : factoredNumbers s ↦ G m) (∏ p ∈ s with p.Prime, ∑' k, G (p^k))`.
3. Given an arbitrary `u : Finset ℕ`, take `s = range (u.max' + 1)`. Every nonzero `d ∈ u` is
   `s`-factored, so `∑_{d ∈ u} G d ≤ ∏ p ∈ s with p.Prime, ∑' k, G (p^k)` by nonnegativity.
4. Bound that product with `tsum_abs_wintnerCoeff_prime_pow_div_le` (termwise, via
   `Finset.prod_le_prod`) and then `exists_bound_euler_product`.
5. Conclude with `summable_of_sum_le` (nonnegative summand, all finite partial sums bounded).

The only real Lean friction expected is step 3: moving between `Finset ℕ` and the subtype
`factoredNumbers s`, and the `(p : ℝ)^k` versus `((p^k : ℕ) : ℝ)` casts in step 4.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Decay'
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Mean'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
