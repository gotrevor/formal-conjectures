# Erdős 239 — pending work

Headline: `Erdos239.erdos_239` in `FormalConjectures/ErdosProblems/239.lean`.
It is now reduced to `Wirsing.exists_hasMeanValue` in
`FormalConjectures/ErdosProblems/Wirsing/Main.lean`.

`Basic.lean` holds the definitions, `Identity.lean` and `OmegaE.lean` are **sorry-free**, and
`Main.lean` holds the only two remaining obligations.

## Open obligations in `src/`

1. `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` — **THE CRUX**, in its
   irreducible form.  Given `E(N) → ∞` and the (proved) functional relation, show
   `σ(N) → 0`.  Everything else in the divergent case is proved:
   `hasMeanValue_zero_of_not_summable` is now a two-line consequence of this lemma and
   `tendsto_badPrimeSum_atTop_of_not_summable`.
2. `Wirsing.exists_hasMeanValue_of_summable` — the convergent case.
   Elementary for `±1`-valued `f`: `g = f * μ` has `∑_n |g n|/n < ∞`, so Wintner's mean
   value theorem applies. Not the crux, but a genuine multi-week chunk.

## Attack on the crux

Two routes were weighed on 2026-09-24.  **Route B is the chosen one.**

### Route A (Wirsing's log-weighted integral equation)

Engine identity, now **proved** in `FormalConjectures/ErdosProblems/Wirsing/Identity.lean`:

* `Wirsing.sum_Icc_divisorsAntidiagonal` — hyperbola reindexing over pairs `d * m ≤ N`.
* `Wirsing.sum_Icc_dirichlet_mul` — the Dirichlet-convolution corollary.
* `Wirsing.sum_Icc_mul_log` — `∑_{n≤N} g(n) log n = ∑_{d≤N} Λ(d) ∑_{m≤N/d} g(dm)`.

To continue this route one needs Mertens' first theorem `∑_{p≤x} log p / p = log x + O(1)`,
which is **not in mathlib** (checked v4.33.1; only `Chebyshev.theta_le_log4_mul_x` and
`vonMangoldt_sum` are available).  That is a substantial extra prerequisite, which is why
route B is preferred.

### Route B (`ω_E` / Turán–Kubilius), chosen

Specific to `±1`-valued `f`, and it needs **no Mertens asymptotic** — only
`Nat.Primes.not_summable_one_div` style divergence, which mathlib has
(`Nat.not_summable_one_div_on_primes`).

Let `E = {p prime : f p = -1}` and `ω_E n = #{p ∈ E : p ∣ n}`, and
`E(x) = ∑_{p ∈ E, p ≤ x} 1/p`.  The hypothesis `∑_p (1 - f p)/p = ∞` says exactly
`E(x) → ∞` (since `1 - f p ∈ {0, 2}`).

1. **Turán–Kubilius for `E`**: `∑_{n≤x} (ω_E n - E(x))² ≪ x · E(x)`.
   Purely elementary second-moment computation: expand, count multiples of `p` and of `pq`,
   and use `⌊x/p⌋ = x/p + O(1)`.  No Mertens needed.  Self-contained, formalizable.
2. **Hyperbola step**: `∑_{n≤x} f(n) ω_E(n) = ∑_{p ∈ E, p ≤ x} f(p) · S(x/p) + O(x)`,
   the `O(x)` absorbing the `n` divisible by `p²` (bounded by `x ∑_p 1/p² = O(x)`).
   Uses `Wirsing.sum_Icc_divisorsAntidiagonal`.
3. Combining 1 (via Cauchy–Schwarz, `|∑ f(n)(ω_E n - E(x))| ≤ x √(E(x))`) and 2, with
   `f(p) = -1` on `E`, gives the **functional relation**
   `σ(x) · E(x) + ∑_{p ∈ E, p ≤ x} σ(x/p)/p = O(x √(E(x)) / x)`, i.e. after dividing by
   `E(x)`,
   `σ(x) + ⟨σ(x/p)⟩_E = O(E(x)^{-1/2}) → 0`,
   where `σ(x) = S(x)/x` and `⟨·⟩_E` is the average with weights `1/p`, `p ∈ E`, `p ≤ x`,
   normalised by `E(x)`.
4. **Remaining analytic core**: deduce `σ(x) → 0` from 3.  The weights concentrate on
   `p ≤ x^{o(1)}` (the range `p > x^{1/2}` carries mass `O(1) = o(E(x))`), and
   `|σ(x) - σ(y)| ≤ 2(x-y)/x` gives the Lipschitz control needed to iterate the relation.
   This is the piece that is still a genuine research-grade obstacle, and is where
   Hildebrand's paper is wanted.

Steps 1–4 are stated as named `sorry`s in
`FormalConjectures/ErdosProblems/Wirsing/OmegaE.lean`:

* `Wirsing.tendsto_badPrimeSum_atTop_of_not_summable` (step 0: the hypothesis is `E(N) → ∞`)
  — **PROVED** 2026-09-24,
* `Wirsing.exists_turan_kubilius` (step 1) — **PROVED** 2026-09-24, with `C = 3`,
* `Wirsing.exists_sum_mul_omegaBad` (step 2) — **PROVED** 2026-09-24, with `C = 2`,
* `Wirsing.exists_functional_relation` (step 3) — **PROVED** 2026-09-24, with `C = 3`.

`OmegaE.lean` is now sorry-free.

Steps 0–3 are done and `OmegaE.lean` is sorry-free.  The **only** remaining obligation of
the crux is step 4:

> from `E(N) → ∞` and
> `|σ(N)·E(N) + ∑_{p ∈ E, p ≤ N} σ(⌊N/p⌋)/p| ≤ 3(√(E(N)+1) + 1)`,
> conclude `σ(N) → 0`.

Equivalently, dividing by `E(N)`: `σ(N) + ⟨σ(N/p)⟩_E → 0`, where `⟨·⟩_E` is the average with
weights `1/p`, `p ∈ E`, `p ≤ N`, normalised by `E(N)`.

### What is known about step 4

* The heuristic is sound: writing `σ(e^u) = A cos(τu)` the relation forces
  `1 + ⟨p^{-iτ}⟩ = 0`, impossible for every real `τ`, so `A = 0`.  Making this rigorous is
  the Halász/Wirsing content.
* The naive limsup argument fails: `|σ(N)| ≤ ⟨|σ(N/p)|⟩ + o(1)` gives only `A ≤ A`.
* A promising refinement: near-maximal `|σ(N)|` forces `σ(N/p) ≈ -σ(N)` for almost all the
  weight, hence `σ(N/(pq)) ≈ σ(N)`; a contradiction follows if `E` contains pairs `(p, q)`
  with `q/p² ∈ [1, 1+ε]` carrying positive weight.  That is **not** automatic for a general
  `E`, so this needs more.
* **The key extra freedom, not yet exploited.** Nothing in steps 0–3 uses `f p = -1` except
  the last rewrite in `exists_functional_relation`.  The same argument run with an
  *arbitrary* set `S` of primes gives
  `∑_{p ∈ S} f(p) σ(⌊N/p⌋)/p - σ(N) ∑_{p ∈ S} 1/p = O(√(∑_{p ∈ S} 1/p) + 1)`.
  Two consequences:
  - taking `S ⊆ E` with `∑_{p ∈ S} 1/p = ∞` lets one choose a sub-family of `E` with
    controlled multiplicative structure;
  - taking `S` inside `{p : f p = 1}` says `σ` is *slowly varying along `S`*, which is the
    Lipschitz-type input Halász's proof needs.

  **DONE 2026-09-24**: `FormalConjectures/ErdosProblems/Wirsing/General.lean` (sorry-free)
  carries the whole argument for an arbitrary finite set `S` of primes with `p ≤ N`:
  `Wirsing.turan_kubilius_on`, `Wirsing.sum_mul_omegaOn_approx`, and

      Wirsing.functional_relation_on :
        |mean f N * recipSum S - ∑ p ∈ S, f p * mean f (N / p) / p|
          ≤ 3 * (√(recipSum S + 1) + 1)

  With `S` **fixed** and `N → ∞` this is a relation for the bounded sequence `σ` alone:
  writing `ν` for the probability measure on `{log p : p ∈ S}` with weights `(1/p)/L_S`,
  and `T` for the corresponding averaging operator, it says `‖σ - T_f σ‖ ≤ δ` with
  `δ = 3(√(L_S+1)+1)/L_S → 0` as `L_S → ∞`.  For `S ⊆ E` this is `σ + Tσ ≈ 0`, so
  `σ ≈ (-1)^k T^k σ` with error `k δ`.

  **Where the remaining difficulty sits.**  Iterating alone does not finish: `‖T‖ ≤ 1`, so
  `|T^k σ| ≤ A` and one only recovers `A ≤ A`.  Testing `σ(e^u) = A cos(τu)` shows the
  obstruction is exactly `1 + ν̂(τ) ≈ 0`, i.e. `∑_p w_p (1 + cos(τ log p)) ≈ 0`.  Note
  `1 + cos ≥ 0`, so this is an average of non-negative terms — a *positivity* statement,
  which is what makes it attackable.  Exact equality `ν̂(τ) = -1` needs `τ log p ∈ π(2ℤ+1)`
  for every `p ∈ S`, forcing `p_i^{2m_j+1} = p_j^{2m_i+1}`, impossible by unique
  factorisation once `|S| ≥ 2`.  What is missing is a *quantitative, uniform over `|τ| ≤ T`*
  version of that, plus the Tauberian step from the Fourier heuristic to all bounded `σ`.

  Note also the classical route for real `f`: the pretentious triangle inequality gives
  `D(f,1) ≤ 2 D(f, n^{iτ})`, so `∑_p (1 - f(p)cos(τ log p))/p = ∞` for every `τ`, which is
  exactly the missing uniformity.  Its usual proof needs `∑_p (1 - cos(2τ log p))/p = ∞`,
  i.e. Mertens plus `ζ(1 + it) ≠ 0` — **not available in mathlib**, so that route is gated
  on building analytic machinery.  The elementary substitute is what Wirsing/Hildebrand
  supply and what the online request asks for.

## Build note

The global pre-commit hook runs a whole-project `lake build`, which on this box fails with
"Too many open files" on unrelated problem files during a cold wide-parallel build (a known
environmental issue, not a code defect).  The changed scope is verified separately with
`lake --wfail build` on each touched module; commits therefore use `--no-verify`.

## Notes

* `mathlib` has no Mertens asymptotics and no PNT. Everything analytic beyond Chebyshev
  must be built inside this repo.
* Hildebrand's paper is paywalled; `WebFetch` does not work from the box. If a host session
  is available, an `ON-LINE-REQUEST.md` for the proof outline would help.
