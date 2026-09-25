# DIRECTION — Erdős 239

## CURRENT DIRECTIVE (set lap 14, 2026-09-25; altitude laps only may rewrite)

**Objective.** Prove `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` — `mean f N → 0`
under `hdiv` — by reducing it to the single named classical lemma
`Wirsing.DilationInvariant` (Elliott's Lipschitz estimate: for every real multiplicative
`g` with `|g| ≤ 1` and every fixed `a ≥ 1`, `mean g N - mean g (N/a) → 0`), and then chipping
`DilationInvariant`.

**Two refutations force this; both are new and decisive.**

1. **The lap-11..13 crux `∃ c, logMean f → c` is FALSE**, not merely an overshoot.  Take `f`
   completely multiplicative with `f p = -1` iff `p ≡ 3 (mod 8)`: `hdiv` holds, yet
   `F(s) = ζ(s)∏_{p≡3(8)}(1-p^{-s})/(1+p^{-s}) ≫ (s-1)^{-1/2} → ∞`, which a bounded
   `logMean` forbids.  Numerically `logMean f N = 1.073·√(log N)` to three places from
   `N = 10^3` to `4·10^6`.  The lemma is deleted; `tendsto_mean_atTop_zero_of_tendsto_logMean`
   stays (true) but its hypothesis never holds.  **Never restate the crux on `logMean`
   convergence, and never "fall back" to it.**
2. **The lap-13 Turán–Kubilius iteration is refuted by a hard ceiling.**
   `E(N) = badPrimeSum f N ≤ log log N + O(1)` always, so the relative error of
   `OmegaE.exists_functional_relation` is `≍ E^{-1/2} ≥ (log log N)^{-1/2}`.  A `k`-level
   sign-flip iteration amplifies that by `ε^{-k}`, so at most `k ≈ ½log₂E ≈ ½log₂log log N`
   levels survive — while the subset-sum parity pigeonhole of lap 13 step 4 needs
   `k ≳ log₂ log N` buckets to make `k·log Y/2^{k-1} < A/2`.  The two are incompatible by an
   exponential.  **Do not resume the multi-level TK/sign-flip iteration or the subset-sum
   pigeonhole.**  `TuranDeficit.lean` and `GoodPrime.lean` stay in place, sorry-free, unused.

**Mandated next move — build `Wirsing/Split.lean`:**
* `IsBddMultiplicative` (real multiplicative, `|g n| ≤ 1` for `n ≥ 1`) and
  `coprimeRestrict f p n = if p ∣ n then 0 else f n`, with the closure lemma.
* **the splitting identity** `∑_{n ≤ N} f n = ∑_{k ≤ log_p N} f(p^k) ∑_{m ≤ N/p^k} v m`
  (`v = coprimeRestrict f p`), from the unique factorisation `n = p^k m`, `p ∤ m`
  (`Nat.ord_proj_mul_ord_compl_eq_self`).  This is the load-bearing brick.
* `DilationInvariant`, the one-step contraction
  `limsup |mean f| ≤ |∑_k f(p^k)/p^k| · limsup |mean v|`, the Euler bound
  `|∑_k f(p^k)p^{-k}| ≤ 1 - 1/p + 1/(p(p-1))` when `f p = -1`, and the induction over a
  finite set of bad primes.

**Forbidden drift.**
* No `logMean`-convergence crux (refuted above); no multi-level TK iteration (refuted above).
* Do **not** re-prove `logMean f N = o(log N)`: `Decay.lean` has it.  (The splitting identity
  gives a three-line second proof — note it, do not build it.)
* Do **not** retry the direct `σ` deficit/window arguments of laps 10 and 13, the Mertens
  weight transfers of laps 2–5, or the `logProfile` recursion.
* Do **not** add `PrimeNumberTheoremAnd` or any package as a dependency.
* Do **not** attack `DilationInvariant` through a disc contour or through Newman's theorem:
  `∫_1^∞ (mean f t) dt/t` diverges (refutation 1), so no Tauberian theorem on the Dirichlet
  series of `f` at `s = 1` can apply.

**Why.**  The splitting reduction is elementary, needs nothing the repository lacks, and
concentrates *all* the remaining analytic difficulty in one classical lemma whose statement
is strictly weaker than the headline.  After it, the only open obligation is
`DilationInvariant` — Halász's theorem in its most tractable guise, and the thing
Granville–Harper–Soundararajan (arXiv:1706.03749) derive Halász *from*.

### Directive history
* lap 14 (2026-09-25) — the `logMean`-convergence crux is FALSE and the multi-level TK
  iteration is capped by `E ≤ log log N`; reduce the crux to `DilationInvariant` (Elliott's
  Lipschitz estimate) via the coprime splitting identity in `Wirsing/Split.lean`.
* lap 4 (2026-09-24) — switch the crux attack from the `logProfile` multi-scale recursion to
  the potential route `Φ(N) = ∑_{n≤N} |L(n)|/n`.  **Met** (lap 5).
* lap 7 (2026-09-24) — correct the false "no analytic machinery in mathlib" premise; target
  the non-pretentiousness input `∑_p (1 - f(p)\cos(t\log p))/p = ∞` for all `t`, from
  mathlib's `riemannZeta`.  **Met** (lap 7-8).
* lap 11 (2026-09-24) — the disc contour for Newman's analytic theorem is unreachable
  (`{re z ≥ 0}` contains no disc around `0`); rebuild the contour as a **rectangle** on
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

---

## Standing charter

Prove `Erdos239.erdos_239` (`FormalConjectures/ErdosProblems/239.lean`) — Wirsing's mean value
theorem for `±1`-valued multiplicative functions — without changing its statement, docstring,
`answer(True)` or attributes.  All helper mathematics lives in
`FormalConjectures/ErdosProblems/Wirsing/` and `FormalConjecturesForMathlib/`.

The two halves:
1. **divergent case** (`∑_p (1-f p)/p = ∞ ⇒ mean 0`) — the crux, currently open; its
   remaining content is the single `sorry`
   `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` in `Main.lean`;
2. **convergent case** (Wintner) — **done** (lap 6), sorry-free.
