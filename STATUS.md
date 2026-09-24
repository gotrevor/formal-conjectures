# STATUS — fc-erdos-239 📊

**Erdős 239 (Wirsing's mean value theorem for `±1`-valued multiplicative functions), formalised
in Lean 4 / Mathlib.** · **Build**: 🟢 green (8939 jobs) · **Updated**: lap 7 · 2026-09-24 ·
`1787bf04`

## Where it stands

`Erdos239.erdos_239` reduces to `Wirsing.exists_hasMeanValue`, whose **convergent (Wintner)
half is complete and sorry-free**.  The divergent half is complete down to one statement, the
Hildebrand asymptotic `σ(N) - L(N)/\log N → 0` (`Wirsing/Main.lean`), which lap 6 showed to be
PNT-strength and therefore not avoidable.  Lap 7 found that the analytic input for that
strength **is already in mathlib** — laps 2–6 had all recorded the opposite — and proved the
first consequence: `f` is pretentious to no character `n^{it}`.  The crux is now decomposed
into two named, mathlib-grounded sub-`sorry`s in `Wirsing/Weighted.lean`.

## What's happened (newest first)

* **2026-09-24 (lap 7, review + proof)** — **route correction**: mathlib v4.33.1 has `ζ`'s
  continuation, its simple pole, `ζ ≠ 0` on `re s ≥ 1`, the log-Euler product, `L(Λ,s)=-ζ'/ζ`
  and `continuousOn_neg_logDeriv_LFunctionTrivChar₁`; only a *Tauberian* theorem is missing.
  The elementary Erdős–Selberg PNT plan is dropped.  New sorry-free `Wirsing/Pretentious.lean`
  proves `∑_p (1 - f(p)\cos(t\log p))/p = ∞` for **every** real `t` — the "missing uniformity"
  that laps 2, 3 and 6 each named and each declared unavailable.  New `Wirsing/Weighted.lean`
  decomposes the next step (the same statement in the Mertens weight `\log p/p`, at rate
  `\gg \log N`) into two sub-`sorry`s and proves the `f`-transfer between them.
* **2026-09-24 (lap 6)** — the convergent case closed (`exists_hasMeanValue_of_summable`,
  axiom-clean); `Wirsing/Rigidity.lean` (rigidity at a near-extremal point); the exact Abel
  identity `S(N) = N L(N) - ∑_{M<N} L(M)`; `Selberg.lean` (the arithmetic identity
  `Λ·\log + Λ*Λ = μ*\log²`).  **Route-decisive**: the headline implies PNT, since `λ` is an
  instance.
* **2026-09-24 (lap 5)** — the first crux closed: `L(N) = o(\log N)` in the divergent case
  (`tendsto_logMean_div_log_atTop_zero`), by the lap-4 potential route.
* **2026-09-24 (lap 4)** — the potential route `Φ(N) = ∑_{n≤N}|L(n)|/n`; `Wirsing/Decay.lean`.
* **2026-09-24 (lap 3)** — the sharp Mertens chain (`sum_log_prime_div_le_log`); the limsup
  shortcut refuted.
* **2026-09-24 (lap 2)** — `logProfile` (now dead scaffolding); the step-function deficit
  bootstrap refuted.
* **2026-09-24 (lap 1)** — Mertens' first theorem from scratch; the log-weighted functional
  relation.
* **2026-09-24 (lap 0)** — `Identity.lean`, `OmegaE.lean` (Turán–Kubilius), `General.lean`.

## Outstanding

### Short-term (mirrors `PENDING_WORK.md`)
1. `Wirsing.exists_tsum_vonMangoldt_twisted_ge` — `∑_n Λ(n)n^{-1-x}(1-\cos(t\log n)) ≥ 1/x - C`
   for `t ≠ 0`, from `continuousOn_neg_logDeriv_LFunctionTrivChar₁` (level 1) plus
   `riemannZeta_ne_zero_of_one_le_re`.
2. `Wirsing.exists_sum_primeWeight_one_sub_cos_ge` — transfer it to
   `∑_{p≤N}(\log p/p)(1-\cos(t\log p)) ≥ \log N/4 - C` by Abel summation at `x = 1/\log N`,
   using `Mertens.abs_sum_vonMangoldt_div_sub_log_le` for the tail.

### Long-term
* Feed the weighted deficit into the route-C relation to break the `A ≤ A` stall, i.e. prove
  `Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero`.
* If a genuine Tauberian step is still needed there, Newman's theorem on top of mathlib's `ζ`
  (a ~1-page complex-analysis formalisation), **not** PNT from scratch.

### To completion
`#print axioms Erdos239.erdos_239` free of `sorryAx`.

## Axiom ledger

| headline theorem | paper claim | `#print axioms` shows | status |
| --- | --- | --- | --- |
| `Erdos239.erdos_239` | unconditional (Wirsing 1967) | `propext, sorryAx, Classical.choice, Quot.sound` | 🔴 `sorryAx` — 3 open `sorry`s (1 in `Wirsing/Main.lean`, 2 in `Wirsing/Weighted.lean`) |
| `Wirsing.exists_hasMeanValue_of_summable` | unconditional (Wintner) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Wirsing.tendsto_logMean_div_log_atTop_zero` | unconditional (Halász, log form) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Wirsing.not_summable_one_sub_mul_cos_of_not_summable` | unconditional | `propext, Classical.choice, Quot.sound` | ✅ clean |

Math-axiom count (🟢+🟡+🟠): **0**.  The project carries no cited axioms; the only debt is the
three disclosed `sorry`s, which is why `sorryAx` is the single 🔴 entry.  The sorry count in
`src/` rose from 1 to 3 this lap **by decomposition**, which is progress: the crux now has two
named sub-goals whose mathlib inputs are identified by name.

## Pointers

`DIRECTION.md` (binding directive) · `PENDING_WORK.md` (attack path) ·
`HANDOFF-erdos-239-2026-09-24-lap7.md` (newest baton) · `KICKOFF-2026-09-24-erdos-239.md`
