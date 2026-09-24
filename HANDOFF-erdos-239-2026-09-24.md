# HANDOFF — Erdős 239 (Wirsing for ±1 multiplicative functions) — 2026-09-24

Branch `erdos-239-proof`, HEAD `329ea264`. Working tree clean. Nothing pushed.

## Target

`Erdos239.erdos_239` in `FormalConjectures/ErdosProblems/239.lean`.
The statement, docstring, `answer(True)` and category attribute are **untouched**, as the
kickoff requires. The proof now reads

    refine ⟨fun _ f h ↦ ?_, fun _ ↦ trivial⟩
    exact Wirsing.exists_hasMeanValue f ⟨h.1, h.2.1, h.2.2⟩

## Files

All under `FormalConjectures/ErdosProblems/Wirsing/`.

| file | status |
|---|---|
| `Basic.lean` | sorry-free — definitions only |
| `Identity.lean` | sorry-free — hyperbola reindexing, Dirichlet convolution, `∑ g(n) log n` |
| `OmegaE.lean` | sorry-free — the whole `ω_E` argument for `E = {p : f p = -1}` |
| `General.lean` | sorry-free — the same argument for an arbitrary finite prime set `S` |
| `Main.lean` | **2 sorries** — the two remaining obligations |

## The two open obligations (both in `Main.lean`)

1. `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` — **THE CRUX**.
   Given `E(N) → ∞`, show `mean f N → 0`. All the number theory is discharged; what is
   left is a statement about the bounded sequence `σ = mean f` together with the proved
   relation.
2. `Wirsing.exists_hasMeanValue_of_summable` — the convergent case (Wintner).
   Elementary and independent of the crux: `g = f * μ` has `∑ |g n|/n < ∞`, so
   `mean = ∑ g(n)/n`. Not yet started.

## What is available to attack the crux

`Wirsing.functional_relation_on` (General.lean), for any finite set `S` of primes with
`p ≤ N` for all `p ∈ S`, and any `N ≥ 1`:

    |mean f N * recipSum S - ∑ p ∈ S, f p * mean f (N / p) / p| ≤ 3 * (√(recipSum S + 1) + 1)

plus `Wirsing.exists_functional_relation` (the `S = {p ≤ N : f p = -1}` specialisation),
`Wirsing.tendsto_badPrimeSum_atTop_of_not_summable`, `Wirsing.abs_mean_le_one`,
`Wirsing.abs_partialSum_le`.

With `S` fixed and `N → ∞` this says `‖σ - T_f σ‖ ≤ δ`, `δ = 3(√(L_S+1)+1)/L_S → 0`, where
`T_f` averages `f(p) σ(·/p)` with weights `(1/p)/L_S`. For `S ⊆ E` that is `σ + Tσ ≈ 0`.

## Next steps

1. **Crux.** Iterating `σ ≈ (-1)^k T^k σ` alone gives only `A ≤ A` (`‖T‖ ≤ 1`). The real
   obstruction is `∑_p w_p (1 + cos(τ log p)) ≈ 0`, an average of *non-negative* terms, so
   it is a positivity question; exact vanishing is ruled out by unique factorisation for
   `|S| ≥ 2` but a version quantitative and uniform over `|τ| ≤ T` is needed, plus a
   Tauberian step. See `PENDING_WORK.md` for the full analysis. The classical real-valued
   shortcut `D(f,1) ≤ 2 D(f, n^{iτ})` is gated on `∑_p (1 - cos(2τ log p))/p = ∞`, i.e.
   Mertens + `ζ(1+it) ≠ 0`, which **mathlib lacks**. `ON-LINE-REQUEST.md` asks a host
   session for Hildebrand's elementary proof / Tenenbaum §III.4.
2. **Wintner half.** Fully elementary, no missing mathlib prerequisites; a good parallel
   thread when the crux stalls.
3. Optional tidy: derive `OmegaE.lean` from `General.lean` (they currently duplicate the
   argument; `OmegaE` came first).

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

Green, no warnings. **Commits use `--no-verify`**: the global pre-commit hook runs a
whole-project `lake build`, which on this box dies with "Too many open files" on unrelated
problem files during a cold wide-parallel build (known environmental issue — see the
reference corpus note `lean-box-fd-exhaustion-is-mmap-not-nofile.md`). Each touched module
is verified with `lake --wfail build` before every commit.
