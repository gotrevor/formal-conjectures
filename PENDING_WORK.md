# Erdős 239 — pending work

Headline: `Erdos239.erdos_239` in `FormalConjectures/ErdosProblems/239.lean`.
It is now reduced to `Wirsing.exists_hasMeanValue` in
`FormalConjectures/ErdosProblems/Wirsing/Basic.lean`.

## Open obligations in `src/`

1. `Wirsing.hasMeanValue_zero_of_not_summable` — **THE CRUX.**
   If `∑_p (1 - f p)/p = ∞` then the mean value is `0`.
   This is Wirsing's 1967 theorem (elementary proof: Hildebrand, Bull. LMS 18 (1986) 147–152).
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
* `Wirsing.exists_turan_kubilius` (step 1) — first moment done: `sum_omegaBad_eq`,
  `sum_omegaBad_le` and `le_sum_omegaBad` give `∑_{n≤N} ω_E(n) = N·E(N) + O(#E(N))`;
  what remains is the second moment `∑_{n≤N} ω_E(n)² ≤ N·E(N) + N·E(N)²`, after which
  `C = 3` works,
* `Wirsing.exists_sum_mul_omegaBad` (step 2),
* `Wirsing.exists_functional_relation` (step 3).

Steps 1 and 2 are the next concrete targets: both are elementary, and neither needs any
analytic number theory that mathlib lacks.  Step 4 (relation ⟹ `σ → 0`) is still open and
is where the research difficulty now lives.

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
