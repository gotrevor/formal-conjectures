# HANDOFF — Erdős 239 — 2026-09-25 (lap 13)

Branch `erdos-239-proof`, HEAD `c4ce7ade`, working tree clean.  Nothing pushed.
`lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` is green (8947 jobs).
Commit with `--no-verify` (the global pre-commit hook builds the whole project and dies with
"Too many open files").  `DIRECTION.md`'s CURRENT DIRECTIVE (lap 11) was discharged in lap 12
and is now stale; it needs an altitude lap.  Do not edit it yourself.

## Where the crux stands

The only `sorry` in `src/` is

    Wirsing.exists_tendsto_logMean_of_badPrimeSum_atTop :
      hdiv → ∃ c, Tendsto (logMean f) atTop (𝓝 c)

i.e. **the Dirichlet series of `f` converges at `s = 1`** (value irrelevant).  Everything else
on the headline path is proved and axiom-clean.

## Landed this lap (all `#print axioms = [propext, Classical.choice, Quot.sound]`)

1. **`Sharp.lean`** — `exists_abs_sum_primeWeight_comp_sub_sum_div_le`: the **sharp weight
   comparison**, `|∑_k primeWeight k·g(⌊N/k⌋) − ∑_{n≤N} g(n)/n| ≤ ε log N + C` for bounded `g`
   with `1/m` increments.  The `o(log N)` replacement for the old `16 log N` version; the
   mechanism is telescoping the *constant* part `−E` of the discrepancy.  Plus the `2/m`-scaled
   corollary and `sum_Icc_one_div_mul_pred(_le)`.
2. `exists_abs_mean_mul_log_le`: `|σ(N)| log N ≤ ∑_{n≤N}|σ(n)|/n + ε log N + C`.
3. **`GoodPrime.lean`** (new) — `exists_window_weight_gt` (a window `(X, e^{|K|+1}X]` of prime
   weight `> K`, from PNT), `exists_prime_notMem`, `exists_near_extremal_prime`.
4. **The crux reformulation** — `tendsto_mean_atTop_zero_of_tendsto_logMean`: `L(N) → c` for
   **any** `c` gives `mean f N → 0` (exact Abel identity + `Filter.Tendsto.cesaro`).
5. **`TuranDeficit.lean`** (new) — `exists_sum_tk_deficit_le`, the Turán–Kubilius deficit.

## THE ROUTE CHANGE — read this first

`OmegaE.exists_functional_relation` (proved in lap 0, unused since) is the right engine:

    |σ(N)E(N) + ∑_{p ∈ E, p ≤ N} σ(⌊N/p⌋)/p| ≤ C(√(E(N)+1)+1),  E(N) = ∑_{p≤N, f p = −1} 1/p.

Total weight `E(N)`, error `O(√E(N))`: the ratio → 0 under `hdiv`.  Every earlier attack used the
log-weighted relation, whose error `c(M₀) + 2δ log N` sits against a main term `ρ log N` while
the bad primes may be far sparser than `log N`.  That is the exact accounting that killed lap
10's route and, as established this lap, also kills the direct `σ` deficit/window argument
(`exists_abs_mean_mul_log_le`'s main term `A log N` is the same size as its `ε log N` error, and
its bad-prime gain `≈ 2Aβ(N)` is swamped whenever `β(N) = o(log N)`; closing that would need an
*effective* PNT error term, which Newman's method does not give).  **Do not retry it.**

`exists_sum_tk_deficit_le` is the TK analogue of `Rigidity.sum_bad_weight_le`, with the bad
weight a small *fraction* of `E(N)` and no `log N` anywhere.

## Next steps (the four-step finish, detailed in `PENDING_WORK.md`)

1. `tailWeight f M₀ N → 0` for fixed `M₀`: `tail ≤ π(N)/(N/M₀) ≤ 2M₀/log N`, needing a short
   `π(N) ≲ 2N/log N` corollary of `Newman.tendsto_chebyshevPsi_div_atTop_one`.
2. Take `A = limsup |σ|` (**not** `Extremal.meanSup`): choosing `M₀` for `A + δ/2` leaves
   infinitely many near-extremal `N`, so `N` can be taken above any `M₀Y^k`.  This removes the
   ordering obstruction that blocked the log-weighted route, and makes `Extremal.lean` optional.
3. Iterate the deficit at `N/p₁`, `N/(p₁p₂)`, … : thresholds grow geometrically but `ρ₁` can be
   made arbitrarily small first (take `δ → 0`, `E → ∞`), so the number of levels `k` is
   unbounded — unlike lap 10's setting.
4. Finish with a subset-sum pigeonhole: among the even- and odd-size subsets of `k` chosen bad
   primes, two of opposite parity have log-products within `k log Y/2^{k−1}`; the corresponding
   scales are multiplicatively adjacent with opposite near-extremal signs, contradicting
   `abs_mean_sub_mean_le`.  Hence `A = 0`.

Then `mean f N → 0` follows directly — note that with this route the intermediate
`∃ c, L → c` sorry can be **bypassed**: prove `tendsto_mean_atTop_zero_of_badPrimeSum_atTop`
straight from the TK chain and delete the logMean detour (keep the Cesàro bridge, it is sound
and cheap).

## Gotchas found this lap

* `field_simp` sometimes closes the goal; a following `ring` then errors "No goals".
* `push_neg` is deprecated in favour of `push Not`; for `¬ (a < b)` prefer `rw [not_lt]`.
* `linarith` treats `2/x` and `1/x` as unrelated atoms — supply `2/x = 2*(1/x)` by `ring`.
* `set x := e with h` then `simp only [h]` to unfold; `rw [abs_le] at *` can mangle unrelated
  hypotheses, so name them.
* For `|s| = 1` case splits use `abs_eq (le_of_lt one_pos) |>.1 hs`.
* The repo's `lean_lib` globs build every file under `FormalConjectures/`, and `warn.sorry` is
  off there — so a `sorry` does **not** show up as a warning, even with `--wfail`.  Check with
  `grep -n sorry` and `#print axioms`.

## Aristotle / online

No job submitted.  Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (lap 6) still uncollected.
`ON-LINE-REQUEST.md` still has the lap-12 request for Hildebrand 1986 (direct PDF link); no
findings file has arrived.  It is less critical now that the TK route is identified.
