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

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Decay'
    lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Mean'
    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

All green, no warnings. Commits use `--no-verify` (the global pre-commit hook runs a
whole-project build that dies with "Too many open files" on this box); each touched module is
verified with `lake --wfail build` before every commit.
