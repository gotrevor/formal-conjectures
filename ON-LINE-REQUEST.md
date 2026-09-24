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
