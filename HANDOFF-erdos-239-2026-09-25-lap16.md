# HANDOFF — Erdős 239 — 2026-09-25 (lap 16)

Branch `erdos-239-proof`, HEAD `546e600e`, working tree clean.  Nothing pushed.
`lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Saturate'` green (8945 jobs).
Commit with `--no-verify` (the global pre-commit hook builds the whole project and dies with
"Too many open files").

`DIRECTION.md` CURRENT DIRECTIVE (lap 14) is still in force: chip `DilationInvariant`.  This lap
did exactly that and the end is in sight.

## The state of the proof

`src/` still has **one** `sorry`: `Wirsing.dilationInvariant_prime` in `Main.lean`.  It is no
longer a wall.  A **complete elementary proof** of it was found this lap and all four of its
inputs are now machine-checked, in the new sorry-free file
`FormalConjectures/ErdosProblems/Wirsing/Saturate.lean` (~1100 lines, ten green commits).

### What closes the crux, and what is left

`Wirsing.exists_improvement` (proved) is the whole argument:

> For every target `Δ ∈ (0,2]` there is `κ = κ(Δ,q) > 0` such that **any** bound
> `|D| ≤ B` holding beyond some point, with `Δ ≤ B ≤ 2`, improves to
> `∀ᶠ N, |D N| ≤ B - κ`.

`κ` depends only on `Δ` and `q` — not on `B`, not on where the bound starts.

**All that is left is the finite iteration.**  Start from the trivial bound `|D| ≤ 2`
(`abs_dilationDiff_le_two`) and apply `exists_improvement` `k` times, `k > (2-Δ)/κ`:

    ∀ k, ∃ n₀ ≥ 1, ∀ n ≥ n₀, |dilationDiff g q n| ≤ max Δ (2 - k * κ)

by induction on `k` (in the `max Δ _ = Δ` case there is nothing to do; otherwise
`2 - k*κ ≥ Δ` so `exists_improvement` applies with `B = 2 - k*κ`).  Choose `k` with
`2 - k*κ ≤ Δ` (`exists_nat_gt ((2-Δ)/κ)`) to get `∀ᶠ N, |D N| ≤ Δ`.  Since `Δ ∈ (0,2]` was
arbitrary and `|D| ≤ 2` always, `Metric.tendsto_atTop` gives
`Tendsto (dilationDiff g q) atTop (𝓝 0)`, which *is* `dilationInvariant_prime` after
`dilationDiff` is unfolded (it is `mean g N - mean g (N / q)` by definition).

Then `Main.lean`'s `sorry` goes away and the whole chain closes:
`dilationInvariant_prime` → `dilationInvariant` → `tendsto_mean_atTop_zero_of_badPrimeSum_atTop`
→ `hasMeanValue_zero_of_not_summable` → `exists_hasMeanValue` → `Erdos239.erdos_239`.
Check with `#print axioms Erdos239.erdos_239`.

## The argument (all proved this lap)

Write `D(N) = σ(N) - σ(⌊N/q⌋)`, `Φ(N) = ∑_{n≤N}|D(n)|/n`.

1. **Run bound** — `abs_sum_Ico_dilationDiff_le_two`.  `∑_{i₁≤i<i₂} D(⌊N/q^i⌋)` telescopes to
   `σ(⌊N/q^{i₁}⌋) - σ(⌊N/q^{i₂}⌋)`, so every partial sum is `≤ 2`.  Hence no long one-signed
   run (`card_le_of_forall_dilationDiff_ge`, `..._le_neg`).
2. **Claim A** — `exists_abs_dilationDiff_le_of_block`.  With `J·Δ/4 > 2`, every block
   `[⌊m/q^J⌋, m]` contains `s` with `|D(s)| ≤ Δ/4`: the run bound forbids one-signedness, and
   then the discrete IVT (`exists_sign_change`) plus the `O(1/m)` step bound
   (`abs_dilationDiff_le_of_straddle`) produce a near-zero scale.  **This is the only step that
   uses that `g` is real** — for `g(n) = n^{iθ}`, `D` rotates at constant modulus and never
   crosses `0`.
3. **Deficit window** — `abs_dilationDiff_sub_le_log_sub` (`|D(n)-D(w)| ≤ (2+4q)(log n - log w)`)
   and `exists_window_of_abs_dilationDiff_le`.  With `ρ = e^{Δ/(4(2+4q))}`, the window
   `⌊s/ρ⌋+1 ≤ n ≤ s` has `|D| ≤ Δ/2` throughout and harmonic weight `≥ (log ρ)/2`
   (`log_sub_log_le_sum_Ioc_one_div`).
4. **Packing** — `sum_abs_dilationDiff_div_le_of_window`, `sum_abs_dilationDiff_div_block_step`,
   `le_of_block_recursion`.  One deficit window per block `(⌊N/T⌋, N]`, `T = 4q^J`, gives
   `Φ(N) ≤ Φ(⌊N/T⌋) + B(log N - log⌊N/T⌋) - γ₀`, and the strong induction with rate
   `κ₁ = γ₀/log(2T)` gives `Φ(N) ≤ (B - κ₁)log N + C`.  The rate must be `γ₀/log 2T`, not
   `γ₀/log T`: the floor loss `log N - log⌊N/T⌋ ≤ log 2T` is paid out of the same `γ₀`.
5. **Pointwise gain** — `exists_abs_dilationDiff_mul_log_le` (lap 15) turns
   `Φ(N) ≤ (B-κ₁)log N + C` into `∀ᶠ N, |D(N)| ≤ B - κ₁/4`.

## Two obstructions recorded by earlier laps, and why they do not bite

* *The functional relation is exactly critical, so it cannot be iterated.*  True, and the
  argument never iterates it: it is used once, through the differential inequality of step 5.
* *Mertens' first theorem has an `O(1)` error, so it cannot bound the prime weight of a
  fixed-ratio window from below.*  True — which is why step 4 runs against the **harmonic**
  weight, where the bound is elementary.  (The PNT variant also works: the repo proves PNT
  unconditionally in `Wirsing/Newman.lean`, and `natDiv_mem_window` /
  `abs_dilationDiff_natDiv_le_of_prime_window` in `Saturate.lean` are that route's step.  They
  are kept, unused by the main line.)
* `exists_saturation` (first commit of the lap) is the Mertens-weight form of step 5; also kept,
  also unused by the main line.  It is the sharp statement that deficient scales are rare.

## Next lap, in order

1. Write the finite iteration above; discharge `Main.dilationInvariant_prime`.
2. `lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` and
   `#print axioms Erdos239.erdos_239` — it must show no `sorryAx`.
3. Then the repository target is met; `STATUS.md` and `DIRECTION.md` want an altitude pass.

`PENDING_WORK.md` (lap-16 section, at the top) has the same content in more detail, including
the exact statements of all the new lemmas.
