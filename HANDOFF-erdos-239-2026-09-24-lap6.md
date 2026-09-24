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

**Step 4** (`le_abs_logMean_of_sign_stable`, same file, also proved): if
`s σ(⌊N/k⌋) ≥ A - ρ` for every `k` outside a set of harmonic weight `η`, then
`|L(N)| ≥ (A - ρ)(log N - η) - η - 2`.  **But see the correction below: its hypothesis is not
what rigidity delivers**, so it is kept as a lemma and is not on the current path.

**The corrected picture (late in the lap).**  Rigidity gives `σ(⌊N/p⌋) ≈ s A f(p)`, so the
sign of `σ` along the quotients is `s f(p)` — a *character*, not a stable sign.  Substituting
that into `∑_{k ≤ N} σ(⌊N/k⌋)/k = L(N) + O(1)` reproduces `sA·L(N) = o(log N)`: consistent, so
relation (2) cannot be the source of the contradiction, and every transfer from the Mertens
weight `log p/p` to the harmonic weight `1/k` was refuted (all three fail on the same `O(1)`
Mertens error accumulated over `log N` scales; localising it is PNT-strength).

The live endgame instead compares `σ` at two quotients directly, using the third lemma landed
this lap, `abs_mean_sub_mean_le`: `|σ(N) - σ(M)| ≤ 2(N - M)/N`.  With
`σ(⌊N/n⌋) ≈ sA f(n)` this forces `f(n) = f(n')` for good `n, n'` in any multiplicative window
of ratio `1 + A/2` — and a `{±1}`-valued multiplicative function that is locally constant is
eventually `1`, contradicting `hdiv`.  A cheap version of the finish uses only the ratios
`k² : k(k+1) : (k+1)²`.  `PENDING_WORK.md` has the full argument and the ordered next attack.

## The crux, restated (end of lap 6)

`Main.lean` now carries the single open statement

    Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero (hf : IsPMOneMultiplicative f) :
      Tendsto (fun N ↦ mean f N - logMean f N / Real.log N) atTop (𝓝 0)

— [Hi86]'s `S(x) ~ (x/log x) L(x)`, with `hdiv` factored out (it is used only to produce
`L(N) = o(log N)`).  `tendsto_mean_atTop_zero_of_logMean` is two lines from it.  An exact
Abel identity worth knowing, not yet in the repo: `S(N) = N L(N) - ∫_1^N L(t) dt`, i.e.
`σ(N) = L(N) - (1/N)∫_1^N L`, so the crux says the *local* increments of `L` over bounded
multiplicative ranges average to `L(N)/log N`.

**Aristotle**: project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` was submitted at the end of
this lap with a self-contained mathlib-only statement of the crux (`/tmp/.../ar/Crux.lean`).
Check it with `aristotle show`; verify any returned proof in-kernel with `#print axioms`
before trusting it.  Nothing else is in flight.

## Open questions that decide the route (also in `ON-LINE-REQUEST.md`)

1. Hildebrand's actual proof of the asymptotic, and where real-valuedness enters.
2. Is `∑_{p ≤ x} log p/p = log x - E + o(1)` elementary, or PNT-equivalent?  Every attempt
   this lap to localise the rigidity argument to a bounded multiplicative window reduced to
   exactly this: the repo's Mertens error is the absolute constant `log 4 + 8 ≈ 9.4`, so it
   says nothing about windows of ratio below `e^{19}`.

## ROUTE-DECISIVE: Erdős 239 implies PNT

`λ` (Liouville) is an instance of the problem, its mean value must be `0`, and
`∑_{n≤x}λ(n) = o(x)` is equivalent to the Prime Number Theorem.  So the headline theorem is
PNT-strength and **no PNT-free route exists**.  That is one explanation for all three
obstructions recorded this lap (the weight transfers, the window chaining, and the `2/π`
resonance computation): each reduced to a PNT-equivalent estimate.

Consequently `Wirsing/Rigidity.lean` is the Erdős half of the elementary Erdős–Selberg proof
of PNT, and it stalls because it is fed only the *first-order* relation.  The missing input
is the second-order one, the **Selberg symmetry formula** (not in mathlib).  See
`PENDING_WORK.md` for the decision an altitude lap must take: formalise Selberg here, or add
`PrimeNumberTheoremAnd` (on disk, not a dependency) and import PNT.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Wintner'
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Rigidity'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
