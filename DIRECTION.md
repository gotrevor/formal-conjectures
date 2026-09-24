# DIRECTION — Erdős 239

## CURRENT DIRECTIVE (set lap 7, 2026-09-24; altitude laps only may rewrite)

**Objective.** Prove the *non-pretentiousness* input that laps 2–6 repeatedly identified as
the one missing ingredient and then wrongly ruled out:

    Wirsing.not_summable_one_sub_cos   (t ≠ 0) :
      ¬ Summable (fun p : Nat.Primes ↦ (1 - Real.cos (t * Real.log p)) / p)

and its consequence for a `±1`-valued multiplicative `f`, for **every** real `t`:

    Wirsing.not_summable_one_sub_mul_cos :
      ¬ Summable (fun p : Nat.Primes ↦ (1 - f p * Real.cos (t * Real.log p)) / p)

(the case `t = 0` being the standing divergence hypothesis).  New file
`FormalConjectures/ErdosProblems/Wirsing/Pretentious.lean`.

**Mandated next move.** Build that file.  The proof is short and uses only mathlib:
`riemannZeta_eulerProduct_exp_log` gives `log‖ζ(s)‖ = ∑_p Re(-log(1 - p^{-s}))`; comparing
`s = 1+x` with `s = 1+x+it` gives, termwise,

    log(|1 - a ω| / (1 - a))  ≤  2 a (1 - Re ω),        a = p^{-(1+x)} ≤ 1/2, |ω| = 1,

so `log ζ(1+x) - log‖ζ(1+x+it)‖ ≤ 2 ∑_p (1 - cos(t log p)) p^{-(1+x)}`.  The left side tends
to `∞` (`∑_p p^{-(1+x)} → ∞` from `Nat.Primes.not_summable_one_div`, while `ζ` is *continuous*
at `1+it` for `t ≠ 0`), so the right side is unbounded, and summability at `x = 0` would bound
it.  **Only continuity of `ζ` at `1+it` is needed — not `ζ(1+it) ≠ 0`** (though mathlib has
that too: `riemannZeta_ne_zero_of_one_le_re`).  Then `|f(p)² - (p^{it})²| ≤ 2|f(p) - p^{it}|`
transfers it from `t` to `t/2` and to `f`, because `f² ≡ 1`.

**Forbidden drift.**
* Do **not** resume the elementary Selberg-symmetry / Erdős–Selberg PNT plan.  It is a
  correct but 5–10× larger road to the same place; `Selberg.lean` stays as sorry-free
  scaffolding and is not the path.
* Do **not** add `PrimeNumberTheoremAnd` (or any package) as a dependency.
* Do **not** repeat any of the three refuted Mertens-weight transfers, the window chaining,
  or the `logProfile` recursion.

**Why.** `PENDING_WORK.md` recorded that the classical route for real `f` needs
`∑_p (1 - cos(2t log p))/p = ∞`, "i.e. Mertens plus `ζ(1+it) ≠ 0` — **not available in
mathlib**, so that route is gated on building analytic machinery".  **That assessment is
wrong.**  Mathlib v4.33.1 has `riemannZeta` with its analytic continuation, its simple pole
(`riemannZeta_residue_one`), non-vanishing on `re s ≥ 1`
(`riemannZeta_ne_zero_of_one_le_re`), the log-Euler product
(`riemannZeta_eulerProduct_exp_log`), and `L(Λ, s) = -ζ'/ζ`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).  Every lap since lap 2 has been steering
around an obstacle that is not there, which is why the plan drifted to formalising PNT from
scratch.  The headline *is* PNT-strength (lap 6, correct), but the analytic input for that
strength is already in the dependency tree.

### Directive history
* lap 4 (2026-09-24) — switch the crux attack from the `logProfile` multi-scale recursion to
  the potential route `Φ(N) = ∑_{n≤N} |L(n)|/n`.  **Met** (lap 5).
* lap 7 (2026-09-24) — correct the false "no analytic machinery in mathlib" premise; target
  the non-pretentiousness input `∑_p (1 - f(p)\cos(t\log p))/p = ∞` for all `t`, from
  mathlib's `riemannZeta`.

---

## Standing charter

Prove `Erdos239.erdos_239` (`FormalConjectures/ErdosProblems/239.lean`) — Wirsing's mean value
theorem for `±1`-valued multiplicative functions — without changing its statement, docstring,
`answer(True)` or attributes.  All helper mathematics lives in
`FormalConjectures/ErdosProblems/Wirsing/` and `FormalConjecturesForMathlib/`.

The two halves:
1. **divergent case** (`∑_p (1-f p)/p = ∞ ⇒ mean 0`) — the crux, currently open; its
   remaining content is the single `sorry`
   `Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero` in `Main.lean`;
2. **convergent case** (Wintner) — **done** (lap 6), sorry-free.
