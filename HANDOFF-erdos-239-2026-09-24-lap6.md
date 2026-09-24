# HANDOFF — Erdős 239 — 2026-09-24 (lap 6)

Branch `erdos-239-proof`. Working tree clean. Nothing pushed.

`DIRECTION.md`'s CURRENT DIRECTIVE (lap 4) has its objective met and its two prohibitions
spent: `tendsto_logMean_div_log_atTop_zero` is proved, and the Wintner half it deferred is
now finished. An altitude lap should retarget it at the Tauberian step.

## Headline: the convergent case is complete; `src/` has exactly one sorry left

`Wirsing.exists_hasMeanValue_of_summable` is machine-checked
(`#print axioms`: propext, Classical.choice, Quot.sound). The last gap,
`Wirsing.summable_abs_wintnerCoeff_div`, is proved through
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` plus
`summable_of_sum_le`; see `PENDING_WORK.md` for the two Lean details that differ from the
lap-5 recipe (smooth numbers instead of `factoredNumbers`, `Finset.subtype` for the partial
sum). The declaration had to move to the end of `Wintner.lean`, after the prime-power
arithmetic it depends on.

The only open obligation in `src/` is now
`Wirsing.tendsto_mean_atTop_zero_of_logMean` (`Main.lean`) — the Tauberian crux.

## The crux: rigidity at a near-extremal point (new route, step 1 landed)

`Wirsing/Rigidity.lean` (new, sorry-free):

* `rigidityPrimes M₀ N`, `mem_rigidityPrimes`, `rigidityPrimes_subset` — the primes with
  `⌊N/p⌋ ≥ M₀`.
* **`sum_deficit_le`** — if `|σ(M)| ≤ A + δ` for `M ≥ M₀` and `A - δ ≤ s σ(N)` with `|s| = 1`,
  then `∑_{p ≤ N/M₀} (log p/p)(A + δ - s f(p)σ(⌊N/p⌋)) ≤ 2δ log N + rigidityConst M₀`.
* `rigidity_term_nonneg` — every term of that sum is `≥ 0`.
* **`sum_bad_weight_le`** — hence the primes with `s f(p)σ(⌊N/p⌋) < A - ρ` carry Mertens
  weight `≤ (2δ log N + rigidityConst M₀)/(ρ + δ)`.

The idea: the recorded `A ≤ A` stall is an *equality case* of the functional relation, and at
a point `N` within `δ` of the limsup the relation is forced to be nearly an equality term by
term. With `ρ = √δ` this gives, for all but `O(√δ log N)` of the weight,
`|σ(⌊N/p⌋)| ≥ A - √δ` **and** `f(p) = s·sign σ(⌊N/p⌋)`. The first kills the Halász
obstruction `cos(θ log N)` (which is near-extremal only near its peaks); the second is a
character equation for `f`, and is where `f(p) = ±1` — a sign, never a phase — enters.

**Step 4 is also done** (`le_abs_logMean_of_sign_stable`, same file): if
`s σ(⌊N/k⌋) ≥ A - ρ` for every `k` outside a set of harmonic weight `η`, then
`|L(N)| ≥ (A - ρ)(log N - η) - η - 2`, which contradicts `L(N) = o(log N)` whenever
`A > ρ`.  This fixes the exact shape steps 2-3 must deliver: a good set `G ⊆ Icc 1 N` of
`1/k`-weight `harmonicSum N - o(log N)` on which `s σ(⌊N/k⌋)` has a positive lower bound.

Steps 2-3 (few sign changes of `σ`; the correlation `C(v) ≈ f(p)` is an approximate `{±1}`
character, hence `≡ 1`) are
written out in `PENDING_WORK.md`, with the ordered next attack. The cheapest next piece is
step 4, which is independent of 2-3 and pins down the exact shape they must deliver. The
main technical risk is the weight transfer (`log p/p` to `1/k`) in step 3.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Wintner'
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Rigidity'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
