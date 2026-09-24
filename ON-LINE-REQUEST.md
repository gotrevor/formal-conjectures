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
