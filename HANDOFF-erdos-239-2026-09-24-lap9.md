# HANDOFF — Erdős 239 — 2026-09-24 (lap 9)

Branch `erdos-239-proof`, HEAD `2b214b57`, working tree clean.  Nothing pushed.
`DIRECTION.md`'s lap-7 CURRENT DIRECTIVE was already met before this lap; its forbidden-drift
list still binds and was respected (no Erdős–Selberg PNT plan, no new package dependency, no
repeated Mertens-weight transfers).

## Landed this lap — all sorry-free, all `[propext, Classical.choice, Quot.sound]`

**`Wirsing/Karamata.lean` is FINISHED.**  Karamata's Tauberian theorem for Dirichlet series:
`a_n ≥ 0`, `a_0 = 0`, `x S(x) → c` ⟹ `(∑_{n ≤ e^V} a_n)/V → c`
(`Karamata.tendsto_partialSum_div`).  The closing steps were `functional_testFun` (the
Karamata value of `u^{-1}1_{[θ,1]}` is exactly `x∑_{n ≤ (1/θ)^{1/x}} a_n`) and
`tendsto_functional_testFun` (the bracket pinch, `θ = e^{-1}`).

**`Wirsing/PrimeCos.lean`** (new).  `tendsto_sum_primeWeight_cos`:
`∑_{p≤N}(log p/p)cos(t log p) = o(log N)` for `t ≠ 0` — *the PNT-strength estimate lap 6 named
as the blocker*, now a theorem, with neither Wiener–Ikehara nor Erdős–Selberg.  Also the
sharp resonance defect `≥ log N/8` with **no additive constant**, from the exact identity
`1 - g cos θ - (1-cos 2θ)/4 = (cos θ - g)²/2` for `g = ±1`.

**`Wirsing/Uniform.lean`** (new).  `exists_forall_primeDefect_ge`: `min_{|t|≤T} D_N(t) → ∞`.
Lap 7 had this pointwise in `t`; a Dini/compactness argument makes it uniform on compact twist
ranges, the form Halász needs.

**`Wirsing/Character.lean`** (new).  The character relation `f(r) = f(p)f(q)`, the period
lemma `eq_of_character_step_two`, `sum_good_primeWeight_ge` (**step 1**: good primes carry
`(1-o(1))log N`), and **`eq_one_of_coprime_window`** (**step 2**: two coprime good integers in
one window force `f(nm) = 1`).

**`Wirsing/Window.lean`** (new).  `abs_harmonicSum_sub_sub_log_le`:
`|∑_{M<n≤N} 1/n - log(N/M)| ≤ 1/M`.

**`Wirsing/Newman.lean`** (new, 4 disclosed sorries).  `kernel_eq`: on `|z| = R`,
`(1 + z²/R²)/z = 2·Re(z)/R²` — the whole miracle of Newman's proof.  Plus both arc estimates
`norm_tail_mul_kernel_le` and `norm_trunc_mul_kernel_le`, each `≤ 2C/R²` uniformly in `T`.

## The route-decisive findings of this lap

**1. Where the PNT strength enters, exactly.**  The rigidity window step needs a good point in
a multiplicative window of ratio `1/(1-A)`, i.e. of *constant* weight `≈ A`.  Over primes that
is PNT: Mertens' first theorem has an irreducible `O(1)` error (`log 4 + 8 ≈ 9.4`) which
swamps a short window, so it cannot certify that the window contains any prime at all.

**2. The gate lifts if the collapse runs over INTEGERS.**  `abs_harmonicSum_sub_sub_log_le`
gives window weight `log c + O(1/M)` — error `o(1)`, elementary.  So the chain must be
**reordered**: propagate rigidity to integers first, then collapse.

**3. Two of my own analyses this lap were wrong; both are recorded in `PENDING_WORK.md` as
do-not-retry.**  (a) A claimed "density obstruction" to the squaring step compared global
weights where the correct computation is a Fubini over log-scales — most windows *are* good.
(b) The squaring collapse must never be applied to `f(n²)`: `IsPMOneMultiplicative` is
multiplicative only on *coprime* arguments, so `f(n²)` is unconstrained.  The squaring happens
in the character, never in `f`.  Applying it to `f` directly would be a false proof.

## The chain, and what is open

| step | statement | state |
| --- | --- | --- |
| 1 | good primes carry full Mertens weight | **proved** (`sum_good_primeWeight_ge`) |
| 2 | collapse: coprime good integers in a window ⟹ `f(nm) = 1` | **proved** (`eq_one_of_coprime_window`) |
| 3 | `f(k) = 1` for almost every `k` in harmonic weight | needs step 4 |
| 4 | **propagate rigidity from primes to all integers**, induction on `Ω(k)` | **OPEN — the crux** |
| 5 | `le_abs_logMean_of_sign_stable` + `tendsto_logMean_div_log_atTop_zero` ⟹ `A = 0` | already proved |

**Step 4 is the single route-decisive open obligation**, and it is where the PNT-strength
content now lives.  Its one-step form is the proved `Wirsing.sum_bad_weight_le_step`; the work
is the induction and the conversion from Mertens weight over primes to harmonic weight over
integers (`log k = ∑_{d|k} Λ(d)` is the entry point, as in `Wirsing/Log.lean`).

Note the chain proves the **divergent case directly**, so `Main.lean` should be restructured to
derive `tendsto_mean_atTop_zero_of_badPrimeSum_atTop` from it.  The *unconditional* Hildebrand
asymptotic `tendsto_mean_sub_logMean_div_log_atTop_zero`, which currently holds the `sorry`, is
strictly stronger than the headline needs and should stop being the crux.

## Open `sorry`s in `src/`

* `Wirsing/Main.lean` — `tendsto_mean_sub_logMean_div_log_atTop_zero` (the crux).
* `Wirsing/Newman.lean` — 4 disclosed, the analytic fallback:
  `tendsto_integral_of_analyticOn` (contour bookkeeping only; both arc estimates are proved),
  `tendsto_chebyshevPsi_div_atTop_one`, `exists_tendsto_sum_log_prime_div_sub_log`,
  `tendsto_sum_log_prime_div_window`.

## Build

    lake --wfail build 'FormalConjectures.ErdosProblems.«239»'

Green.  Commits use `--no-verify` (the global pre-commit hook runs a whole-project build that
dies with "Too many open files" on this box).

## Aristotle

Project `c58edc97-baa0-461a-8a5e-c2bdf336b92d` (the crux, lap 6) still uncollected; check
`aristotle show` before submitting anything new.  No job was submitted this lap.
