# STATUS — fc-erdos-239 📊

**Erdős 239 (Wirsing's mean value theorem for `±1`-valued multiplicative functions), formalised
in Lean 4 / Mathlib.** · **Build**: 🟢 green (8940 jobs) · **Updated**: lap 11 · 2026-09-24 ·
`1bc1c772`

## Where it stands

`Erdos239.erdos_239` reduces to `Wirsing.exists_hasMeanValue`, whose **convergent (Wintner) half
is complete and sorry-free**.  The divergent half is complete down to *one* analytic theorem:
Newman's Tauberian theorem `Newman.tendsto_integral_of_analyticOn`.  Everything downstream of it
is already proved — PNT (`tendsto_chebyshevPsi_div_atTop_one`), sharp Mertens, the window
statement `tendsto_sum_log_prime_div_window`, and steps 1–5 of the rigidity chain over primes.
The remaining `sorry`s in `src/` are that theorem, its application
(`Newman.summable_psi_sub_div`) and the headline crux that consumes them
(`Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero`).

## What's happened (newest first)

* **2026-09-24 (lap 11, review + proof)** — **route correction**: the lap-10 plan to feed the
  Newman *disc* estimate an analytic `G` on `closedBall 0 R` is **unreachable** —
  `{re z ≥ 0}` contains no disc around `0` (it misses `-R/2` for every `R`), and no conformal
  or shifted-disc repair works, because the near-`0` part of the contour must have `re z ≤ -δ`
  bounded away from `0` to supply the `e^{-δT}` decay.  Mathlib's only non-disc Cauchy theorem
  is for a **rectangle**, so the contour becomes `Q = [-δ, R] × [-R, R]`; all edge estimates
  were re-derived by hand and go through with the same kernel `1/z + z/R²`.  New sorry-free
  `Wirsing/Rectangle.lean` (`rectInt`, `rectInt_inv` = `∮ dz/z = 2πi`, `rectInt_mul_kernel`,
  the two kernel bounds) and `Wirsing/Laplace.lean` (`Newman.lean` split; `newmanAux`, the four
  edge estimates, and **`norm_sub_integral_le_rect`**, Newman's estimate on the rectangle).
* **2026-09-24 (lap 10)** — the deficit-budget/`Ω(k)`-induction rigidity route refuted, and
  Chebyshev's bounds shown unable to lift the window gate (PNT is unavoidable).
  `Wirsing/Extremal.lean` (the variational extremal point, bad-prime weight `O(1)` independent
  of `N`).  `Newman.lean`: discrete Abel summation, sharp Mertens from the two Newman inputs,
  **PNT proved** from `summable_psi_sub_div` by a discrete Zagier endgame, the Λ→primes
  passage, the window statement, and the Newman estimate on a disc.
* **2026-09-24 (lap 9)** — `Wirsing/Karamata.lean`, `Character.lean`, `PrimeCos.lean`,
  `Uniform.lean`, `Window.lean`; the window step located as the exact point where PNT enters.
* **2026-09-24 (lap 7–8)** — route correction: mathlib v4.33.1 *does* have `ζ`'s continuation,
  simple pole, non-vanishing on `re s ≥ 1`, log-Euler product and `L(Λ,s) = -ζ'/ζ`; only a
  Tauberian theorem is missing.  `Wirsing/Pretentious.lean` (`∑_p (1 - f(p)\cos(t\log p))/p
  = ∞` for every real `t`), `Wirsing/Weighted.lean`.
* **2026-09-24 (lap 6)** — the convergent case closed; `Wirsing/Rigidity.lean`; the exact Abel
  identity; `Selberg.lean`.  **Route-decisive**: the headline implies PNT (`λ` is an instance).
* **2026-09-24 (lap 5)** — the first crux closed: `L(N) = o(\log N)` in the divergent case.
* **2026-09-24 (lap 4)** — the potential route `Φ(N) = ∑_{n≤N}|L(n)|/n`; `Wirsing/Decay.lean`.
* **2026-09-24 (lap 3)** — the sharp Mertens chain; the limsup shortcut refuted.
* **2026-09-24 (lap 2)** — `logProfile` (now dead scaffolding); the deficit bootstrap refuted.
* **2026-09-24 (lap 1)** — Mertens' first theorem from scratch.
* **2026-09-24 (lap 0)** — `Identity.lean`, `OmegaE.lean` (Turán–Kubilius), `General.lean`.

## Outstanding

### Short-term (mirrors `PENDING_WORK.md`)
1. **Done this lap**: `Newman.norm_sub_integral_le_rect`, Newman's estimate on the rectangle,
   `‖G 0 - ∫_0^T F‖ ≤ (2Mδ + 5C)/R + R M e^{-δT}(1/δ + 2/R)`.
2. `Newman.tendsto_integral_of_analyticOn` from it: the compactness step
   (`IsCompact.exists_thickening_subset_open` gives `δ(R) > 0` with
   `rect (-δ) R (-R) R ⊆ {z | AnalyticAt ℂ G z}`; fix `δ₀` first so one `M` serves all
   `δ ≤ δ₀`), then the ε-chase `T → ∞`, `δ → 0`, `R → ∞`.
3. `Newman.summable_psi_sub_div` — apply (2) to `F(t) = ψ(e^t)e^{-t} - 1`, whose transform is
   `-ζ'/ζ(z+1)/(z+1) - 1/z`.

### Long-term
* `Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero` — feed the now-unconditional window
  statement into `Wirsing.eq_of_mean_quotient_close` and close the prime chain.

### To completion
`#print axioms Erdos239.erdos_239` free of `sorryAx`.

## Axiom ledger

| headline theorem | paper claim | `#print axioms` shows | status |
| --- | --- | --- | --- |
| `Erdos239.erdos_239` | unconditional (Wirsing 1967) | `propext, sorryAx, Classical.choice, Quot.sound` | 🔴 `sorryAx` — 3 open `sorry`s (1 in `Wirsing/Main.lean`, 2 in `Wirsing/Newman.lean`) |
| `Wirsing.exists_hasMeanValue_of_summable` | unconditional (Wintner) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Newman.tendsto_chebyshevPsi_div_atTop_one` (PNT) | unconditional | `propext, sorryAx, …` | 🔴 via `summable_psi_sub_div` only; the Zagier endgame itself is clean |
| `Newman.tendsto_sum_log_prime_div_window` | unconditional | `propext, sorryAx, …` | 🔴 same single root |
| `Newman.norm_sub_integral_le` | unconditional (Newman, disc form) | `propext, Classical.choice, Quot.sound` | ✅ clean, but **unused**: the disc hypothesis is unsatisfiable here |
| `Newman.rectInt_div_self`, `Newman.rectInt_mul_kernel` | unconditional (residue on a rectangle) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Newman.norm_sub_integral_le_rect` | unconditional (Newman, rectangle form) | `propext, Classical.choice, Quot.sound` | ✅ clean — the live route |
| `Wirsing.tendsto_logMean_div_log_atTop_zero` | unconditional (Halász, log form) | `propext, Classical.choice, Quot.sound` | ✅ clean |

Math-axiom count (🟢+🟡+🟠): **0**.  The project carries no cited axioms; the only debt is the
three disclosed `sorry`s, all rooted in the single analytic theorem
`Newman.tendsto_integral_of_analyticOn`, which is why `sorryAx` is the single 🔴 entry.

## Pointers

`DIRECTION.md` (binding directive — lap 11: rectangle contour) · `PENDING_WORK.md` (attack
path) · `HANDOFF-erdos-239-2026-09-24-lap11.md` (newest baton) ·
`KICKOFF-2026-09-24-erdos-239.md`
