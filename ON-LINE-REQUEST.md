# Online requests

## 2026-09-24 — Hildebrand's elementary proof of Wirsing's mean value theorem

Needed: a proof outline (numbered lemmas, with statements) of

> A. Hildebrand, *On Wirsing's mean value theorem for multiplicative functions*,
> Bull. London Math. Soc. **18** (1986), 147–152.

The box cannot fetch it (`WebFetch` is firewalled; the article is paywalled on Oxford
Academic). Any of these would do:

* the paper itself (PDF or text),
* Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, §III.4
  (Wirsing's theorem, elementary proof) — statements of the intermediate lemmas,
* Granville–Soundararajan, *Multiplicative Number Theory I*, the chapter proving
  Halász/Wirsing for **real** bounded multiplicative `f`.

What I specifically need is the chain of intermediate estimates that turns the identity
`S(x) log x = ∑_{d≤x} Λ(d) f(d) S(x/d) + O(x)` into `S(x) = o(x)` when
`∑_p (1 - f(p))/p = ∞`, for `f` real with `|f| ≤ 1`.

Also useful: whether `∑_{p≤x} log p / p = log x + O(1)` (Mertens' first theorem) has landed
in mathlib master since v4.33.1.

## 2026-09-24 (lap 5) — sharpened ask: the two steps of Hildebrand's route

A web search settled the shape of [Hi86]: the paper proves the **quantitative** bound

    |(1/x) ∑_{n ≤ x} f(n)|  ≤  γ (1 + ∑_{p ≤ x} (1 - f(p))/p)^{-1/2}

for real multiplicative `f` with `|f| ≤ 1` and a universal `γ`, and the proof "uses an
inversion of the order of summation in `∑_{n ≤ x} f(n) log n` to show that

    ∑_{n ≤ x} f(n)  ~  τ (x / log x) ∑_{n ≤ x} f(n)/n,

where the last sum may be dealt with by elementary arguments or by the
Hardy–Littlewood–Karamata Tauberian theorem."

This repo has already proved `∑_{n ≤ x} f(n)/n = o(log x)` in the divergent case
(`Wirsing.tendsto_logMean_div_log_atTop_zero`, lap 5), so **only the displayed asymptotic
relation is missing**, and it is the whole of the remaining `sorry`.

What is needed, as precisely as possible:

1. The exact hypotheses and constant `τ` in `S(x) ~ τ (x/log x) L(x)`.  It is **false** for
   `f(n) = n^{iθ}`, so real-valuedness (or non-pretentiousness) must enter; where?
2. The Cauchy–Schwarz / second-moment step that produces the exponent `-1/2`.  Which sum is
   squared, and against which measure?
3. Whether the route needs `ζ(1 + it) ≠ 0` (or `∑_p (1 - \cos(t \log p))/p → ∞`) anywhere.
   If it does, that is the deep input and should be isolated as a named lemma.

Sources already consulted (titles/links only, not the text):
`encyclopediaofmath.org/wiki/Wirsing_theorems`,
`terrytao.wordpress.com/2019/12/17/254a-notes-10-mean-values-of-nonpretentious-multiplicative-functions/`,
`arxiv.org/pdf/1604.00295` (Granville–Harper–Soundararajan, *A Strengthening of Theorems of
Halász and Wirsing*) — this last one is on arXiv and **fetchable by a host session**.

## 2026-09-24 (lap 6) — the crux is now ONE asymptotic; two precise asks

The repo's remaining `sorry` has been reduced to a single statement, with `hdiv` factored
out of it entirely:

    Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero :
      f real, ±1, multiplicative  ⟹  mean f N - logMean f N / log N → 0,

i.e. exactly [Hi86]'s `∑_{n≤x} f(n) ~ (x/log x) ∑_{n≤x} f(n)/n` with `τ = 1` (the case
`f = 1` fixes the constant).  Everything else in both halves of Wirsing's theorem is proved.

**Ask 1 (the important one).**  The proof of that asymptotic in [Hi86], or in any source.
Where exactly does real-valuedness enter?  It must, since the statement is false for
`f(n) = n^{iθ}`.

**Ask 2.**  Is `∑_{p ≤ x} \log p / p = \log x - E + o(1)` (Mertens' first theorem *with the
constant*, i.e. with `o(1)` rather than `O(1)` error) known to be equivalent to PNT, or is
there an elementary proof?  This lap found that **every** attempt to localise the rigidity
argument to a bounded multiplicative window reduces to exactly this estimate: the repo's
Mertens bound has the absolute error `\log 4 + 8 ≈ 9.4`, so it says nothing about a window of
ratio below `e^{19}`.  If the `o(1)` form is elementary, the crux route in `PENDING_WORK.md`
closes; if it is PNT-equivalent, that route needs a different last step.

## 2026-09-24 (lap 12) — fetch Hildebrand [Hi86] in full

PNT is now proved in-repo (`Newman.tendsto_chebyshevPsi_div_atTop_one`, axiom-clean), so
**Ask 2 of lap 6 is closed** — no answer needed.  Ask 1 is still open and is now the only
blocker.  A direct PDF link surfaced by `WebSearch` this lap:

    https://academic.oup.com/blms/article-pdf/18/2/147/956525/18-2-147.pdf
    A. Hildebrand, "On Wirsing's mean value Theorem for Multiplicative Functions",
    Bull. London Math. Soc. 18 (1986) 147-152.

`WebFetch` times out from this box.  Please fetch that PDF (or any full text of the paper)
and drop the text under `ON-LINE-FINDINGS-hildebrand-1986.md`.

What is needed from it, in order of importance:

1. **The statement and proof of the key lemma** — the search snippet describes it as: for real
   multiplicative `-1 \le f \le 1` and `1 \le w \le \sqrt x`, the mean `(1/x)\sum_{n\le x}f(n)`
   is related to a *weighted* sum with an explicit error term.  The exact inequality, with its
   weight and error, is the missing piece: the repo's chain via
   `Wirsing.le_abs_logMean_of_sign_stable` needs the good integers to have *full harmonic
   weight*, and lap 10's deficit-budget argument shows the rigidity propagation cannot deliver
   that.  So Hildebrand must reach the asymptotic a different way, and that way is what we need.
2. Where real-valuedness is used (the statement is false for `f(n) = n^{i\theta}`).
3. Whether the proof uses PNT or sharp Mertens anywhere — both are now available in-repo.


## 2026-09-25 (lap 15) — Hildebrand [Hi86], and GHS arXiv:1706.03749

`WebSearch` from the box this lap recovered the **statement** of Hildebrand's key estimate,
which is exactly the repo's remaining open obligation `Wirsing.dilationInvariant_prime`:

> If `f` is real multiplicative with `-1 ≤ f(n) ≤ 1`, then for `1 ≤ w ≤ √x`
>
>     (1/x) ∑_{n≤x} f(n) = (w/x) ∑_{n≤x/w} f(n) + O( (log(log x / log 2w))^{-1/2} ).

The `-1/2` exponent is the Turán–Kubilius standard deviation, and the repo already has the
TK functional relation in exactly the right generality
(`Wirsing.bdd_functional_relation_on`, `Wirsing/BddGeneral.lean`):

    | σ(N)·L_S − ∑_{p∈S} (g(p)/p)·σ(⌊N/p⌋) | ≤ 3(√(L_S+1) + 1),   L_S = ∑_{p∈S} 1/p.

**What is still missing is the two or three lines that turn that relation into the Lipschitz
estimate.**  Naive attempts all fail: applying the relation at `x` and at `x/w` with the same
`S` gives `L_S·|D(x)| ≤ 2 L_S + O(√L_S)`, which is vacuous, and reindexing the prime range by
`w` changes `f(p)` to `f(p/w)`, which is meaningless.  So Hildebrand does something else.

Please fetch **either** of:

* https://academic.oup.com/blms/article-pdf/18/2/147/956525/18-2-147.pdf
  (Hildebrand, *On Wirsing's mean value theorem for multiplicative functions*, BLMS 18 (1986)
  147–152) — the whole paper is six pages; the proof of the Lipschitz estimate is what matters;
* **https://arxiv.org/abs/1706.03749** (Granville–Harper–Soundararajan, *A new proof of
  Halász's theorem, and its consequences*) — free on arXiv, and §2 contains a self-contained
  proof of the Lipschitz estimate from the same TK relation;
* failing both, https://arxiv.org/abs/math/9911246 (Granville–Soundararajan, *Decay of mean
  values of multiplicative functions*), whose §2–3 also derive it.

Drop the text under `ON-LINE-FINDINGS-hildebrand-1986.md` (or `-ghs-2019.md`).

Specifically needed: **how the choice of the prime set `S` depends on `w` and `x`**, and where
`f` real-valued is used.
