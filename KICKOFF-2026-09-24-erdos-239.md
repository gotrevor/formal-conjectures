# KICKOFF 2026-09-24 — prove Erdős 239 (Wirsing for ±1 multiplicative functions)

Worktree `~/src/fc-erdos-239` (a formal-conjectures checkout), branch `erdos-239-proof`, based on
`upstream/main`.  Opus/low.

## Target

Replace the `sorry` in `FormalConjectures/ErdosProblems/239.lean` (`erdos_239`) with a proof.
**Do not change the statement, the docstring, the `answer(True)`, or the category attribute.**
Helper lemmas go in new files under `FormalConjectures/ErdosProblems/Wirsing/` (import them from
239.lean).  Never touch any other existing file.

Math: every multiplicative `f : ℕ → {±1}` has a mean value.  Wirsing 1967; route via
**Hildebrand, "On Wirsing's mean value theorem for multiplicative functions", Bull. LMS 18 (1986)**,
an ELEMENTARY proof.  Also useful: Granville–Soundararajan, *Multiplicative Number Theory I*
(pretentious book), chapters on Wirsing/Halász for real-valued `f`.  Full complex Halász is out of
scope.  Structure to expect:
1. If `Σ_p (1 − f(p))/p = ∞`, the mean is `0`.
2. Otherwise the mean is `Π_p (1 − 1/p)(1 + f(p)/p + f(p²)/p² + …)` (converges).
Freeze each as a named lemma early (a named `sorry` is progress), prove the easy direction first,
and probe numerically where useful (Python in `scripts/` or a scratch dir, NOT committed to src).

## Rules
- Never delete, rename or weaken `erdos_239`.  An open named leaf is an acceptable end state.
- Build: `lake build 'FormalConjectures.ErdosProblems.«239»'` (warm tree; never run
  `lake exe cache get`).  `native_decide`/boosts fine at this tier.  Commit each green step.
  Each HANDOFF (in the repo root, `HANDOFF-erdos-239-*.md`) names the current crux.
- Nothing gets pushed or PR'd by the treadmill.  Trevor decides on upstream.
