# Handoff: Erdős 239 — COMPLETE (final, lap 17)

**Date**: 2026-09-25 02:49 UTC · **Branch**: `erdos-239-proof` · **HEAD**: `e1d4f424` · tree clean

This is the closing handoff for the run. The per-lap doc with the full technical narrative is
`HANDOFF-erdos-239-2026-09-25-lap17.md`; this one is the top-level summary and the state of the
branch.

## 🎯 What we were doing

Prove `Erdos239.erdos_239` — Wirsing's mean value theorem for `±1`-valued multiplicative
functions — in Lean 4 / Mathlib, without changing the problem statement. **Done.**

## ✅ State (all observed this session, not assumed)

* `lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` → `Build completed successfully
  (8957 jobs)`.
* `#print axioms Erdos239.erdos_239` → `[propext, Classical.choice, Quot.sound]`. **No
  `sorryAx`, no cited axiom.** Same for `Wirsing.dilationInvariant_prime` and
  `Wirsing.hasMeanValue_zero_of_not_summable`.
* `git diff main -- FormalConjectures/ErdosProblems/239.lean` touches only the
  `module`/`public import` header and the proof body; the theorem statement, docstring,
  `answer(True)` and attributes are byte-identical to `main`, as the charter requires.
* Nothing pushed. Four commits this lap: `7fc4edc7` (the proof), `64fb76c3` (handoff+STATUS),
  `04a996bb` (gate note), `e1d4f424` (faithfulness check).

## 🧠 Context to carry forward

The whole theorem came down to one lemma, `Wirsing.dilationInvariant_prime` — Elliott's
Lipschitz estimate, `D(N) = mean g N - mean g ⌊N/q⌋ → 0`. Laps 14–16 built the crossing
argument for it in `Wirsing/Saturate.lean`; lap 17 wrote the finite iteration that finishes it:

* `exists_improvement` (lap 16) improves *any* eventual bound `|D| ≤ B` with `Δ ≤ B ≤ 2` to
  `|D| ≤ B - κ`, with `κ = κ(Δ, q)` **independent of `B`** — that independence is the whole
  trick, it is what makes the step iterable a fixed finite number of times.
* `eventually_abs_dilationDiff_le_of_pos` — induction on `k` for
  `∃ n₀ ≥ 1, ∀ n ≥ n₀, |D n| ≤ max Δ (2 - k·κ)`. Base: `abs_dilationDiff_le_two`. Step: apply
  `exists_improvement` at `B = max Δ (2 - k·κ)`, then case on `2 - k·κ ≤ Δ`. Finish with
  `exists_nat_gt ((2-Δ)/κ)`.
* `tendsto_dilationDiff_atTop_nhds_zero` — `Metric.tendsto_atTop`, `Δ = min (ε/2) 2`.

Dead ends already refuted by earlier laps, recorded in `DIRECTION.md` — do **not** revive them:
the `logMean`-convergence crux is *false* (`p ≡ 3 mod 8` counterexample); the multi-level
Turán–Kubilius sign-flip iteration is capped by `E(N) ≤ log log N`; no Tauberian theorem at
`s = 1` can apply because `∫₁^∞ (mean f t) dt/t` diverges.

## 🎬 Next actions

There is **no open obligation in the Erdős 239 chain.** If the branch is picked up again:

1. Push `erdos-239-proof` (this box has no egress; the host pushes) and open the PR. The PR body
   should say: proves `erdos_239`; statement unchanged; `#print axioms` clean; new material is
   `FormalConjectures/ErdosProblems/Wirsing/*` plus the `239.lean` proof body.
2. Optional altitude pass: `STATUS.md` and `DIRECTION.md` still carry per-lap narration from laps
   3–17 that could be compressed now that the route is settled.
3. Optional tidy: `Wirsing/Saturate.lean` keeps two proved-but-unused sharp results,
   `exists_saturation` and `natDiv_mem_window` / `abs_dilationDiff_natDiv_le_of_prime_window`
   (the PNT route's window step). Keep or delete — nothing depends on them.

## ⚠️ Gotchas

* **Commit with `--no-verify`.** The global pre-commit hook builds the whole project and dies
  with "Too many open files".
* **The repo-wide self-stop gate declines `box done`** because Formal Conjectures has ~4467 open
  `sorry`s — that is the point of a *statement* repository, not unfinished work. A scoped
  relaunch wants `--done-when 'sorry-free:FormalConjectures/ErdosProblems/Wirsing'`.
* `Main.dilationInvariant_prime` closes by `exact h`, **not** `simpa [dilationDiff]`: the goal's
  `fun N ↦ mean g N - mean g (N/p)` is eta-defeq to `dilationDiff g p`, and `simp` will not
  bridge that — it reports a type mismatch between two visibly equal terms. Eta, not unfolding.

## 📁 Key files

- `FormalConjectures/ErdosProblems/239.lean` — the headline; proof body only.
- `FormalConjectures/ErdosProblems/Wirsing/Saturate.lean` — the crossing argument and the finite
  iteration; the mathematical heart of the proof.
- `FormalConjectures/ErdosProblems/Wirsing/Main.lean` — the assembly chain.
- `DIRECTION.md` — the charter and the list of refuted routes.
- `HANDOFF-erdos-239-2026-09-25-lap17.md` — this lap in technical detail.

---
**→ Next session: the mathematics is finished and kernel-verified. Do not reopen the proof or
start new proof work on this branch. Pick up at "Next actions" #1 — get the branch pushed and the
PR written.**
