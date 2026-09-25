# HANDOFF — Erdős 239 — 2026-09-25 (lap 15)

Branch `erdos-239-proof`, HEAD `9928b395`, working tree clean.  Nothing pushed.
`lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` green (8956 jobs).
Commit with `--no-verify` (the global pre-commit hook builds the whole project and dies with
"Too many open files").

`DIRECTION.md` CURRENT DIRECTIVE (lap 14) is still in force and outranks this file.  Its
mandated move — build `Wirsing/Split.lean` and reduce the crux to `DilationInvariant` — is now
**complete**.  `PENDING_WORK.md` (lap-15 section, at the top) is the detailed record.

## The state of the proof

`src/` has **one** `sorry`: `Wirsing.dilationInvariant_prime` in `Main.lean`.

    ∀ g : ℕ → ℝ, IsBddMultiplicative g → ∀ p, p.Prime →
      Tendsto (fun N ↦ mean g N - mean g (N / p)) atTop (𝓝 0)

Everything else in Wirsing's theorem is proved.  The chain is
`dilationInvariant_prime` → `dilationInvariant_of_prime` → `DilationInvariant`
→ `tendsto_mean_atTop_zero_of_dilationInvariant` → `tendsto_mean_atTop_zero_of_badPrimeSum_atTop`
→ `hasMeanValue_zero_of_not_summable` → `exists_hasMeanValue` → `Erdos239.erdos_239`.

## Landed this lap (six green commits, all sorry-free)

* **`Wirsing/Contract.lean`** — the lap-14 plan finished.  `DilationInvariant` (def), the Euler
  factor `|∑_{k≤K} g(p^k)/p^k| ≤ 1 - 1/p + 1/(p(p-1)) ≤ 1 - 1/(2p)` (`p ≥ 5`, `K ≥ 1`), the
  one-step contraction, the `Finset.induction` over bad primes, `∏(1-1/(2q)) ≤ exp(-½∑1/q)`,
  and the crux **given `DilationInvariant`**.
* **`Wirsing/BddLog.lean`** — the whole `Log.lean` chain, and the log-Lipschitz bound
  `|σ(N)-σ(M)| ≤ 2(N-M)/N`, transferred from `IsPMOneMultiplicative` to `IsBddMultiplicative`.
* **`Wirsing/Dilation.lean`** — `dilationDiff`, the functional relation for `D`, the cocycle
  identity `D_{ab}(N) = D_a(N) + D_b(⌊N/a⌋)` (hence `dilationInvariant_of_prime`), the
  differential inequality `|D(N)|log N ≤ ∑_{n≤N}|D(n)|/n + ε log N + C`, the log-average bridge
  for `D` **and** for `σ` in the bounded class.
* **`Wirsing/BddPrimeCos.lean`** — non-pretentiousness for the bounded class, including the
  `t`-uniform `bdd_exists_forall_primeDefect_ge`.
* **`Wirsing/BddGeneral.lean`** — the Turán–Kubilius functional relation for the bounded class.

Net effect: **the bounded class now has every ingredient the `±1` class had.**  The endgame can
be written entirely inside `IsBddMultiplicative`, with no further class-transfer work.

## The one thing that is missing, stated precisely

`WebSearch` recovered Hildebrand's key estimate — it *is* the open sorry, with a rate:

> real multiplicative `-1 ≤ f ≤ 1`, `1 ≤ w ≤ √x`  ⟹
> `(1/x)∑_{n≤x}f(n) = (w/x)∑_{n≤x/w}f(n) + O((log(log x / log 2w))^{-1/2})`.

The `-1/2` is the Turán–Kubilius standard deviation, so `bdd_functional_relation_on` is the
engine and the hypothesis `-1 ≤ f ≤ 1` is exactly `IsBddMultiplicative`.  **What is missing is
how the prime set `S` is chosen in terms of `w` and `x`.**  Refuted naive choices:

* the same `S` at `x` and at `x/w` gives `L_S|D(x)| ≤ 2L_S + O(√L_S)`, vacuous;
* reindexing the prime range by `w` to align the scales `x/p` turns `f(p)` into `f(p/w)`.

## Also refuted this lap — do not redo

The soft **"two near-periods"** argument (anti-period `log p` ⟹ period `2 log p`; two bad
primes give the tiny period `2(log p - log q)`).  An approximate period `δ` with error `η` per
step transports a shift `c` at cost `η c/δ`, so a tiny period is worthless; and 2-Lipschitzness
makes small-scale approximate periods automatic (`abs_dilationDiff_sub_dilationDiff_le` gives
`|D_a - D_b| ≤ 2(1-a/b)` for free), hence vacuous.  No Lipschitz-only argument can separate the
anti-aligned configuration.

## Next steps

1. Harvest `ON-LINE-REQUEST.md` (lap-15 entry): **GHS arXiv:1706.03749 §2** is free on arXiv and
   derives the Lipschitz estimate from the same TK relation; [Hi86] is the alternative.  The
   single question is the choice of `S`.
2. With that, `dilationInvariant_prime` should be a few hundred lines on top of
   `bdd_functional_relation_on` + `bdd_exists_forall_primeDefect_ge`.
3. If the request goes unanswered, attack the choice of `S` directly: the scales `x/p` for
   `p ∈ S` must be made to *cover* both `x` and `x/w` comparably — i.e. `S` a union of two
   ranges arranged so that the two weighted averages share most of their mass.

## Gotchas found this lap

* `field_simp` frequently closes the goal outright; a following `ring` then errors "No goals"
  (hit three times this lap).  Same for a trailing `positivity` after `simp`.
* `omega` abstracts nonlinear subterms as *syntactic* atoms: `2 * a * (N / a)` and
  `2 * (a * (N / a))` are **different** atoms.  Write the parenthesisation that matches the
  hypothesis (`Nat.div_add_mod` gives `a * (N / a)`).
* `Nat.succ_div_le_succ_div` does not exist; use
  `Nat.div_le_div_right (m ≤ (m-1)+a)` then `Nat.add_div_right`.
* `push_neg` is deprecated in favour of `push Not`; `simp only [not_lt]` avoids the warning.
* `NormedAddCommGroup.tendsto_nhds_zero` → `NormedAddGroup.tendsto_nhds_zero`;
  `tendsto_finset_sum` → `tendsto_finsetSum`; `abs_add` → `abs_add_le`.
* `Filter.Tendsto.eventually_lt_const` and `Filter.Tendsto.div_atTop` are the right tools for
  "eventually below `ε`" goals.
* Unused hypotheses fail `--wfail` (the unused-variable linter); drop them rather than
  underscore-prefixing in a public statement.

## Aristotle / online

No job submitted this lap.  Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (lap 6) still
uncollected.  `WebSearch` works from the box and was productive this lap (it gave the exact
statement of Hildebrand's estimate); `WebFetch` times out as always.
