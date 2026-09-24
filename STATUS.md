# STATUS — fc-erdos-239 📊

**Erdős 239 (Wirsing's mean value theorem for `±1`-valued multiplicative functions), formalised
in Lean 4 / Mathlib.** · **Build**: 🟢 green · **Updated**: lap 4 · 2026-09-24 · `139faeae`

## Where it stands

`Erdos239.erdos_239` is reduced to `Wirsing.exists_hasMeanValue`, which splits into the
divergent case (the crux) and the convergent Wintner case.  All the number theory of the
divergent case is proved and sorry-free: the engine identity, Mertens' first theorem with a
sharp negative error, the log-weighted functional relation, and the Turán–Kubilius machinery.
Three `sorry`s remain, all in `Wirsing/Main.lean`.  Laps 1–3 built the analytic inputs and
refuted two single-scale iteration schemes; lap 4 replaced the whole iteration strategy with a
**potential route** that closes the crux on paper with only inputs this repo already has.

## What's happened (newest first)

* **2026-09-24 (lap 4, review)** — found a complete elementary proof of the crux: telescope
  `Φ(N)/(log N)²` for `Φ(N) = ∑_{n≤N}|L(n)|/n`, which makes the bad-prime deficit summable
  against `1/(N (log N)³)`; a Fubini swap turns that into `∑_{f(p)=-1} 1/p < ∞`.  Direction
  switched; `logProfile` demoted to dead scaffolding.
* **2026-09-24 (lap 3)** — the sharp Mertens chain (`sum_log_prime_div_le_log`: `∑_{p≤x} log p/p
  ≤ log x` for `x ≥ 10¹⁰`), `sum_primeWeight_mul_log_div_le` with no `log N` term, the sharp
  Gronwall step, and the general weight comparison for an antitone profile.  Refuted the limsup
  shortcut.
* **2026-09-24 (lap 2)** — the recursive profile `logProfile` and `abs_logMean_le_logProfile`;
  refuted the step-function deficit bootstrap.
* **2026-09-24 (lap 1)** — route C opened: Mertens' first theorem proved from scratch, plus the
  log-weighted functional relation `σ(N)log N = ∑_p (log p/p) f(p) σ(⌊N/p⌋) + O(1)`.
* **2026-09-24 (lap 0)** — routes A/B; `Identity.lean`, `OmegaE.lean`, `General.lean` all
  sorry-free (hyperbola reindexing, Turán–Kubilius, the functional relation on an arbitrary
  prime set).

## Outstanding

### Short-term (mirrors `PENDING_WORK.md`)
1. `Wirsing/Decay.lean` step B — the Fubini comparison
   `∑_{p≤N}(log p/p) g(⌊N/p⌋) = ∑_{n≤N} g(n)/n + O(log N)` for `1/m`-Lipschitz `g`.
2. Steps C–F — the telescoping of `Φ/(log N)²`, the summability of the deficit, the window
   lower bound, and the contradiction with `∑_{f(p)=-1} 1/p = ∞`.
3. Delete the now-redundant `tendsto_logProfile_div_log_atTop_zero` sorry once step F lands.

### Long-term
* `Wirsing.tendsto_mean_atTop_zero_of_logMean` — the Tauberian step `L = o(log N) ⇒ σ → 0`.
* `Wirsing.exists_hasMeanValue_of_summable` — the Wintner half.

### To completion
`#print axioms Erdos239.erdos_239` free of `sorryAx`.

## Axiom ledger

| headline theorem | paper claim | `#print axioms` shows | status |
| --- | --- | --- | --- |
| `Erdos239.erdos_239` | unconditional (Wirsing 1967) | `propext, sorryAx, Classical.choice, Quot.sound` | 🔴 `sorryAx` — 3 open `sorry`s in `Wirsing/Main.lean`; no cited axioms anywhere in the tree |

Math-axiom count (🟢+🟡+🟠): **0**.  The project carries no cited axioms at all — the only
debt is the three disclosed `sorry`s, which is why `sorryAx` is the single 🔴 entry.

## Pointers

`DIRECTION.md` (binding directive) · `PENDING_WORK.md` (attack path) ·
`HANDOFF-erdos-239-2026-09-24-lap3.md` (newest baton) · `KICKOFF-2026-09-24-erdos-239.md`
