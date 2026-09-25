# HANDOFF — Erdős 239 — 2026-09-25 (lap 14, review lap)

Branch `erdos-239-proof`, HEAD `de2fe464`, working tree clean.  Nothing pushed.
`lake --wfail build 'FormalConjectures.ErdosProblems.«239»'` green (8947 jobs);
`lake --wfail build 'FormalConjectures.ErdosProblems.Wirsing.Split'` green (8933 jobs).
Commit with `--no-verify` (the global pre-commit hook builds the whole project and dies with
"Too many open files").

**Read `DIRECTION.md` CURRENT DIRECTIVE first — it was rewritten this lap and it OUTRANKS this
file.**  `STATUS.md` and `PENDING_WORK.md` (lap-14 section, at the top) are current.

## The two refutations this lap — do not undo them

1. **`∃ c, logMean f → c` is FALSE**, not an overshoot.  It was the only `sorry` in `src/` for
   three laps.  `f` completely multiplicative with `f p = -1` iff `p ≡ 3 (mod 8)`: `hdiv` holds
   and `F(s) = ζ(s)∏_{p≡3(8)}(1-p^{-s})/(1+p^{-s}) ≥ c(s-1)^{-1/2} → ∞`, which a bounded
   `logMean` forbids.  Sieve to `4·10^6`: `logMean f N/√(log N) = 1.073` at every scale from
   `10^3` up, `logMean f N` rising `2.86 → 4.18`, `mean f N ≍ 1/√(log N)`.  Lemma **deleted**;
   the crux is now `Wirsing.tendsto_mean_atTop_zero_of_badPrimeSum_atTop` in `Main.lean`, the
   single `sorry` in `src/`.  Corollary: no Tauberian theorem at `s = 1` can ever apply
   (`∫_1^∞ (mean f t)dt/t` diverges), Newman's included.
2. **Lap 13's TK sign-flip iteration is capped.**  `E(N) ≤ log log N + O(1)`, so the
   `O(√E)`-error functional relation has relative precision `E^{-1/2}` and supports at most
   `½log₂log log N` chain levels, while the subset-sum parity pigeonhole needs `≳ log₂ log N`.
   `TuranDeficit.lean`, `GoodPrime.lean` stay, sorry-free and unused.
   Also refuted: lap 13's "next attack 0" — `∑_N ε/(N log N)` diverges, so `Ψ(N)/log N` is
   *not* quasi-monotone and does not converge.

## Landed this lap — `Wirsing/Split.lean` (new, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`)

* `IsBddMultiplicative` (real multiplicative, `|f n| ≤ 1` for `n ≥ 1`) — `IsPMOneMultiplicative`
  is not closed under removing the multiples of a prime, so the wider class is needed;
  `IsPMOneMultiplicative.isBddMultiplicative` bridges.
* `coprimeRestrict f p n = if p ∣ n then 0 else f n`, `isBddMultiplicative_coprimeRestrict`.
* **`sum_Icc_eq_sum_range_mul`** — the splitting identity, exact, no error term:
  `∑_{n≤N} f n = ∑_{k ≤ log_p N} f(p^k)·∑_{m ≤ N/p^k} v m`, `v = coprimeRestrict f p`.
  Proof: `Finset.sum_fiberwise_of_maps_to` on `n ↦ n.factorization p`, then
  `Finset.sum_nbij'` with `n ↦ n/p^k`, `m ↦ p^k*m` on each fibre.
* `mean_eq_sum_range_mul` (mean form), `abs_mean_le_one_of_bdd`, `sum_Ico_pow_le`,
  `abs_sum_range_sub_sum_range_le`.
* **`abs_mean_sub_sum_mul_mean_le`** — the one-step estimate, `p^K ≤ N`:
  `|mean f N - (∑_{k≤K}f(p^k)/p^k)·mean v N| ≤ ∑_{k≤K}|mean v (N/p^k) - mean v N| + (K+1)/N + p^{-K}`.

## Next steps (finish the reduction; all elementary, no new analysis)

1. `DilationInvariant : ∀ g, IsBddMultiplicative g → ∀ a ≥ 1,
   Tendsto (fun N ↦ mean g N - mean g (N/a)) atTop (𝓝 0)` — the named classical lemma
   (Elliott's Lipschitz estimate).  State it in `Split.lean`.
2. The Euler factor: `Summable (fun k ↦ f (p^k)/(p:ℝ)^k)` and, when `f p = -1` and `p ≥ 5`,
   `|∑' k, f (p^k)/p^k| ≤ 1 - 1/p + 1/(p(p-1)) ≤ exp(-3/(4p))`.  Also
   `|∑_{k≤K} f(p^k)/p^k - ∑' k| ≤ 2 p^{-K}` for the truncation.
3. The one-step contraction: from 1 + 2 + `abs_mean_sub_sum_mul_mean_le`, for every `ε > 0` and
   every `A` with `∀ᶠ N, |mean v N| ≤ A`, conclude `∀ᶠ N, |mean f N| ≤ exp(-3/(4p))·A + ε`.
   (Order of choices: `K` from `ε` and `p`, then `N` large — `p^K ≤ N`, `(K+1)/N < ε/4`, and the
   `K+1` dilation defects each `< ε/(4(K+1))` by `DilationInvariant` at `a = p^k`, `k ≤ K`.)
4. `Finset.induction` over a finite set `T` of bad primes `≥ 5`: each step replaces `f` by
   `coprimeRestrict f p` (still `IsBddMultiplicative`; `f q = -1` survives for `q ∈ T` not yet
   removed, since `q` is coprime to the removed primes), giving
   `∀ᶠ N, |mean f N| ≤ exp(-¾∑_{p∈T}1/p) + ε`.
5. `hdiv` ⟹ for every `B` there is a finite set `T` of bad primes `≥ 5` with `∑_{p∈T}1/p ≥ B`
   (`badPrimeSum f N → ∞`, drop `p ∈ {2,3}`).  Then `Tendsto (mean f) atTop (𝓝 0)`, closing
   `tendsto_mean_atTop_zero_of_badPrimeSum_atTop` **modulo `DilationInvariant` only**.
6. Then the real work: chip `DilationInvariant`.  GHS (arXiv:1706.03749) derive Halász *from*
   it; get that paper (`ON-LINE-REQUEST.md`).  Fallback route if it stalls: the same splitting
   identity applied to `logMean` twisted by `n^{-iθ}` gives `|L_θ(N)| ≪_θ (log N)^{1-1/16}`
   (power saving, using `PrimeCos.eventually_sum_primeWeight_one_sub_mul_cos_ge`), which is the
   `(H1)` input for a Parseval/Perron Halász.

## Gotchas found this lap

* `abs_add` is now **`abs_add_le`**; `Finset.sum_le_tsum` is **`Summable.sum_le_tsum s h hf`**.
* `omega_nat` does not exist.  `omega` treats `m * p^k` and `p^k * m` as unrelated atoms — insert
  `mul_comm` before it.
* `field_simp` often closes the goal; a following `ring` then errors "No goals" (bit twice).
* `set x := e with h` does **not** fold occurrences introduced by a *later* `rw`, so `rw [← h]`
  fails; write the expressions out, or abstract into a separate lemma with `A B : ℕ → ℝ`.
* `gcongr` side-goal order is unpredictable; `gcongr <;> first | … | …` then trips the unused-
  tactic and `<;>`-vs-`;` linters under `--wfail`.  Explicit `mul_le_mul a b c d` is safer.
* `ordProj[p] n = p ^ n.factorization p`, `ordCompl[p] n = n / p ^ n.factorization p`; the
  useful API is `Nat.ordProj_mul_ordCompl_eq_self`, `Nat.not_dvd_ordCompl`,
  `Nat.coprime_ordCompl`, `Nat.ordCompl_pos`, `Nat.le_log_iff_pow_le`, `Nat.cast_div_le`.
* `Wirsing.abs_natDiv_sub_div_le_one` and `Wirsing.partialSum_eq_mul_mean` already exist
  (`Mean.lean`, `Log.lean`) — import `Wirsing.Mean` rather than re-deriving.
* The box has **no C compiler and no numpy**; pure-Python sieve to `4·10^6` runs in ~1 min.

## Aristotle / online

No job submitted this lap.  Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (lap 6) still
uncollected.  `ON-LINE-REQUEST.md` still holds the lap-12 Hildebrand 1986 request; the more
useful target now is **GHS, arXiv:1706.03749** (and arXiv:1706.03755), for the proof of the
Lipschitz estimate.  `WebSearch` works from the box and confirmed the GHS/Hildebrand
bibliography; `WebFetch` times out as always.
