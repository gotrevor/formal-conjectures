# STATUS — fc-erdos-239 📊

**Erdős 239 (Wirsing's mean value theorem for `±1`-valued multiplicative functions), formalised
in Lean 4 / Mathlib.** · **Build**: 🟢 green (8947 jobs) · **Updated**: lap 14 · 2026-09-25 ·
`65d9697b`+

## Where it stands

`Erdos239.erdos_239` reduces to `Wirsing.exists_hasMeanValue`, whose **convergent (Wintner)
half is complete and sorry-free**.  All the analytic infrastructure is now proved and
axiom-clean: Newman's Tauberian theorem, the **prime number theorem**, sharp Mertens, the
multiplicative window statement, the Turán–Kubilius functional relation and deficit, and the
sharp prime-weight/harmonic-weight comparison.  Exactly **one `sorry`** is left in `src/`:
the divergent case `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop`.

Lap 14 found that the statement laps 11–13 were attacking — convergence of `logMean f` — is
**false**, deleted it, restated the crux on `mean` directly, and reduced it (on paper) to one
classical lemma, `DilationInvariant` (Elliott's Lipschitz estimate), via an error-free coprime
splitting identity.  That reduction is what `Wirsing/Split.lean` is being built to carry.

## What's happened (newest first)
* **2026-09-25 (lap 14, review)** — **two refutations**.  (a) The lap-11..13 crux
  `∃ c, logMean f → c` is **FALSE**: for `f` completely multiplicative with `f p = -1` iff
  `p ≡ 3 (mod 8)`, `hdiv` holds while `F(s) ≫ (s-1)^{-1/2} → ∞` forbids a bounded `logMean`;
  a sieve to `4·10^6` gives `logMean f N/√(log N) = 1.073` at every scale, i.e.
  `logMean f N ≍ √(log N) → ∞` with `mean f N ≍ 1/√(log N) → 0`.  Lemma deleted, crux restated
  on `mean`, and every Tauberian attack at `s = 1` (Newman included) is dead with it.
  (b) The lap-13 Turán–Kubilius sign-flip iteration is capped: `E(N) ≤ log log N + O(1)`, so
  its `E^{-1/2}` relative error supports `≤ ½log₂log log N` levels while the subset-sum parity
  pigeonhole needs `≳ log₂ log N`.  Also refuted: lap 13's "next attack 0"
  (`∑_N ε/(N log N)` diverges, so `Ψ/log N` is not quasi-monotone).  **New route**: the
  error-free coprime splitting `∑_{n≤N}f n = ∑_k f(p^k)∑_{m≤N/p^k}v m`, which reduces the crux
  to `Wirsing.DilationInvariant` alone.

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
1. `Wirsing/Split.lean`: `IsBddMultiplicative`, `coprimeRestrict`, closure lemma.
2. **(SPLIT)** `∑_{n ≤ N} f n = ∑_{k ≤ log_p N} f(p^k)·∑_{m ≤ N/p^k} v m` — load-bearing,
   an exact identity from `n = p^k·ord_compl[p] n`.
3. `Summable (k ↦ f(p^k)/p^k)` and the Euler bound `|∑'| ≤ 1 - 1/p + 1/(p(p-1))` when `f p = -1`.
4. The one-step contraction `limsup|mean f| ≤ |∑_k f(p^k)p^{-k}|·limsup|mean v|` from (SPLIT)
   plus `DilationInvariant`; then `Finset.induction` over a finite set of bad primes and `hdiv`.

### Long-term
* `Wirsing.DilationInvariant` — Elliott's Lipschitz estimate, the sole remaining obligation
  once the splitting reduction lands.  Granville–Harper–Soundararajan (arXiv:1706.03749)
  derive Halász's theorem from it.  Fallback if it stalls: the twisted splitting bound
  `|L_θ(N)| ≪_θ (log N)^{1-1/16}` (from `PrimeCos`) plus a Parseval/Perron step.

### To completion
`#print axioms Erdos239.erdos_239` free of `sorryAx`.

## Axiom ledger

Verified by `#print axioms` this lap (lap 14).

| headline theorem | paper claim | `#print axioms` shows | status |
| --- | --- | --- | --- |
| `Erdos239.erdos_239` | unconditional (Wirsing 1967) | `propext, sorryAx, Classical.choice, Quot.sound` | 🔴 `sorryAx` — **one** open `sorry`, `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` |
| `Wirsing.exists_hasMeanValue` | unconditional | `propext, sorryAx, Classical.choice, Quot.sound` | 🔴 same single root |
| `Wirsing.exists_hasMeanValue_of_summable` | unconditional (Wintner) | `propext, Classical.choice, Quot.sound` | ✅ clean — the convergent half |
| `Newman.tendsto_integral_of_analyticOn` | unconditional (Newman 1980) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Newman.tendsto_chebyshevPsi_div_atTop_one` (PNT) | unconditional | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Newman.tendsto_sum_log_prime_div_window` | unconditional | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Wirsing.tendsto_logMean_div_log_atTop_zero` | unconditional (Halász, log form) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Wirsing.exists_abs_mean_mul_log_le` | unconditional (sharp comparison) | `propext, Classical.choice, Quot.sound` | ✅ clean |
| `Wirsing.exists_sum_tk_deficit_le` | unconditional (Turán–Kubilius deficit) | `propext, Classical.choice, Quot.sound` | ✅ clean, now **unused** (route refuted lap 14) |
| `Wirsing.tendsto_mean_atTop_zero_of_tendsto_logMean` | unconditional (Cesàro bridge) | `propext, Classical.choice, Quot.sound` | ✅ clean, but **unusable**: its hypothesis is never satisfied under `hdiv` |

Math-axiom count (🟢+🟡+🟠): **0**.  The project cites no axioms at all; the sole debt is the
one disclosed `sorry` on the divergent case, which is why `sorryAx` is the single 🔴 entry.
Nothing here is 🟡/🟠 debt: PNT and Newman's theorem, the usual project-scale candidates, are
both fully proved in-repo.

## Pointers

`DIRECTION.md` (binding directive — lap 14: reduce the crux to `DilationInvariant` via
`Wirsing/Split.lean`) · `PENDING_WORK.md` (attack path, with the lap-14 refutations) ·
newest baton: `ls HANDOFF-*-lap*.md | sort -t p -k2 -n | tail -1` ·
`KICKOFF-2026-09-24-erdos-239.md`
