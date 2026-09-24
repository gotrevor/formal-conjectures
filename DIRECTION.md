# DIRECTION — Erdős 239

## CURRENT DIRECTIVE (set lap 11, 2026-09-24; altitude laps only may rewrite)

**Objective.** Close `Newman.tendsto_integral_of_analyticOn` — Newman's analytic (Tauberian)
theorem — which is now the *single* remaining mathematical obstruction: everything downstream
(PNT, sharp Mertens, the window step, the prime chain) is already proved from it, and the only
other open `sorry`s (`Newman.summable_psi_sub_div`,
`Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero`) are consequences.

**Mandated next move — switch the contour from a CIRCLE to a RECTANGLE.**

Lap 10 proved the Newman estimate on a *disc* (`Newman.norm_sub_integral_le`) and left as its
next action "get `G` analytic on the disc `|z| ≤ R` from analyticity on `re z ≥ 0`".
**That step is impossible**, and this is the route-decisive finding of lap 11: for every
`R > 0` the point `-R/2` lies in `closedBall 0 R` but not in `{re z ≥ 0}`, so the closed
half-plane contains no disc around `0` at all.  The disc estimate can therefore never be
applied to the hypothesis of the analytic theorem.  No "conformal adjustment" repairs this:
the near-`0` part of the contour must have `re z ≤ -δ` *bounded away from 0* (that is what
supplies the `e^{-δT}` decay for the `G` term), and a circle through a neighbourhood of `0`
has `re z` sweeping continuously through `0`.  Shifted discs `|z - c| ≤ r`, `c < r ≤ c + δ`,
were checked and fail for exactly this reason (the `1/z` factor at the contour's closest
approach to `0` blows up like `log(R/δ)/δ`).

Mathlib v4.33.1 has **no** Cauchy theorem for a general contour; its non-disc tool is
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (Cauchy–Goursat for a rectangle).
Newman's proof runs on the rectangle `Q = [-δ, R] × [-R, R]` with the *same* kernel
`k(z) = 1/z + z/R²` and the *same* estimates, all verified by hand this lap:

* right edge `x = R`: `|k| ≤ (1+√2)/R`, `|G - g_T|e^{xT} ≤ C/R` ⟹ `O(C/R)`;
* top/bottom `y = ±R`: `R² + z² = x(x ± 2iR)` ⟹ `|k| ≤ √5|x|/R²`, the *same* cancellation
  that makes the circle work ⟹ `O(C/R)` for `x > 0`, `O((M+C)δ/R²)` for `x ∈ [-δ, 0]`;
* left edge `x = -δ`: the `G` part carries `e^{-δT} → 0` (T first, δ and R fixed); the `g_T`
  part is deformed to the three outer edges of `Q' = [-R, -δ] × [-R, R]` by a *second*
  rectangle-Cauchy (`0 ∉ Q'`), where it is again `O(C/R)`.

Limits in the order `T → ∞`, then `δ → 0`, then `R → ∞`.

The two supporting facts needed, both confirmed present in mathlib this lap:
`Complex.differentiableOn_dslope` (removable singularity, for the residue) and
`Complex.hasStrictDerivAt_log` on `slitPlane` together with
`Complex.arg_neg_eq_arg_add_pi_of_im_neg` (to evaluate `∮_{∂Q} dz/z = 2πi` edge by edge).

**Forbidden drift.**
* Do **not** try again to obtain `G` analytic on a full disc `|z| ≤ R`, in any disguise
  (compactness, conformal adjustment, shifted or smaller discs).  It is refuted above.
* Do **not** resume the elementary Selberg-symmetry / Erdős–Selberg PNT plan.
* Do **not** add `PrimeNumberTheoremAnd` (or any package) as a dependency.  Its source under
  `.lake/packages/` may be *read* for method, never imported.
* Do **not** repeat the refuted Mertens-weight transfers, window chaining, `logProfile`
  recursion, or the lap-10 rigidity-by-`Ω(k)`-induction route.

**Why.** Every remaining `sorry` in the project sits under this one theorem, the disc route
to it is provably unreachable, and the rectangle route is the only contour shape mathlib
supports.  The circle lemmas of lap 10 that are not contour-specific
(`norm_integral_Ioi_le`, `norm_integral_Ioc_le`, `integral_Ioi_sub_integral_Ioc`,
`integrableOn_laplace`, `integrableOn_laplace_Ioc`, `differentiable_truncLaplace`,
`neg_mul_exp_mul_le`) are reused verbatim; only the circle-specific kernel bounds and
`norm_sub_integral_le` become unused, and they stay in place, sorry-free.

### Directive history
* lap 4 (2026-09-24) — switch the crux attack from the `logProfile` multi-scale recursion to
  the potential route `Φ(N) = ∑_{n≤N} |L(n)|/n`.  **Met** (lap 5).
* lap 7 (2026-09-24) — correct the false "no analytic machinery in mathlib" premise; target
  the non-pretentiousness input `∑_p (1 - f(p)\cos(t\log p))/p = ∞` for all `t`, from
  mathlib's `riemannZeta`.  **Met** (lap 7-8).
* lap 11 (2026-09-24) — the disc contour for Newman's analytic theorem is unreachable
  (`{re z ≥ 0}` contains no disc around `0`); rebuild the contour as a **rectangle** on
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

---

## Standing charter

Prove `Erdos239.erdos_239` (`FormalConjectures/ErdosProblems/239.lean`) — Wirsing's mean value
theorem for `±1`-valued multiplicative functions — without changing its statement, docstring,
`answer(True)` or attributes.  All helper mathematics lives in
`FormalConjectures/ErdosProblems/Wirsing/` and `FormalConjecturesForMathlib/`.

The two halves:
1. **divergent case** (`∑_p (1-f p)/p = ∞ ⇒ mean 0`) — the crux, currently open; its
   remaining content is the single `sorry`
   `Wirsing.tendsto_mean_sub_logMean_div_log_atTop_zero` in `Main.lean`;
2. **convergent case** (Wintner) — **done** (lap 6), sorry-free.
