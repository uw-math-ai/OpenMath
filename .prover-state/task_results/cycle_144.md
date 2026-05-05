# Cycle 144 Results

## Worked on

`thm:550A` n = 3 stepping stone:
`OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_three`,
following the cycle-144 strategy (Priority 1) verbatim. No backup
branches activated.

## Approach

Followed the strategy's Step 0–3 outline.

**Paper algebra (Step 1).** With the doubly companion matrix
```
X = [[-α 0,  -α 1,  -α 2 - β 2],
     [ 1,     0,    -β 1      ],
     [ 0,     1,    -β 0      ]],
```
expanded `det(I − zX)` via Sarrus / cofactor formula (`det_fin_three`):
```
det(I − zX) = 1 + (α 0 + β 0)·z + (α 0·β 0 + α 1 + β 1)·z²
                + (α 0·β 1 + α 1·β 0 + α 2 + β 2)·z³.
```
Computed `α(z) · β(z)` symbolically (cubic × cubic = sextic):
```
α(z)·β(z) = 1 + (α 0 + β 0)·z + (α 0·β 0 + α 1 + β 1)·z²
              + (α 0·β 1 + α 1·β 0 + α 2 + β 2)·z³
              + (α 0·β 2 + α 1·β 1 + α 2·β 0)·z⁴
              + (α 1·β 2 + α 2·β 1)·z⁵ + (α 2·β 2)·z⁶.
```
**The z⁰…z³ coefficients cancel exactly** — this is the textbook
content of Theorem 550A's `O(z^{n+1})` claim. Residue:
```
det(I − zX) − α(z)·β(z) = z⁴ · (a + z·b + z²·c)
where a = -(α 0·β 2) - β 0·α 2 - β 1·α 1,
      b = -(β 1·α 2) - α 1·β 2,
      c = -(α 2·β 2).
```
Note: at `n = 1` the leading coefficient was `−α 0·β 0`; at `n = 2`,
`−(α 0·β 1 + α 1·β 0)`; at `n = 3`, `−(α 0·β 2 + α 1·β 1 + α 2·β 0)`.
Three data points confirm the convolution pattern
`−Σᵢ αᵢ · β_{n−i}` for the leading `z^{n+1}` term.

**Lean encoding (Step 2).** The cycle-140 (`n = 2`) proof used
`unfold doublyCompanionMatrix; norm_num [Fin.sum_univ_two,
Matrix.det_fin_two]; ring_nf; suffices … ; convert … ring`. This
template did NOT transfer cleanly to `n = 3`: `simp only` /
`norm_num` left unresolved `if h : 2 = 0 then …` branches inside the
matrix entries (the `j.val + 1 = n` condition for the corner case at
`(0, 2)` and the last-column case at row-2). Pivoted to the cycle
138 (`n = 1`) `_one_eq` style: pre-reduce `doublyCompanionMatrix α β`
to an explicit `!![…]` form via `ext i j; fin_cases i <;> fin_cases j
<;> simp [doublyCompanionMatrix]`. Then a second `ext i j; fin_cases
…` block reduces `1 − z • X` to its expanded `!![…]` form. A single
`Matrix.det_fin_three` + `simp [alphaPoly, betaPoly,
Fin.sum_univ_three]; ring` closes the polynomial identity proving the
factored residue form.

**Bound chain (Step 3).** `IsBigO.of_bound C` with
`C := ‖a‖ + ‖b‖ + ‖c‖`. Localised to `‖z‖ < 1` neighborhood via
`Metric.eventually_nhds_iff`. Bound via:
* `‖a + y·b + y²·c‖ ≤ ‖a + y·b‖ + ‖y²·c‖` (`norm_add_le`)
* `‖a + y·b‖ ≤ ‖a‖ + ‖y·b‖` (`norm_add_le`)
* `‖y·b‖ ≤ ‖b‖` (`mul_le_of_le_one_left` + `‖y‖ ≤ 1`)
* `‖y²·c‖ ≤ ‖c‖` (`mul_le_of_le_one_left` + `‖y‖² ≤ 1²`)
* close `‖inner‖ ≤ C` via `linarith`.
Then `‖z⁴‖ · ‖inner‖ ≤ ‖z⁴‖ · C = C · ‖z⁴‖`.

## Result

**SUCCESS** — `doublyCompanionMatrix_det_factorization_n_three`
landed axiom-clean.

`lean_verify
OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_three`
returns `[propext, Classical.choice, Quot.sound]`.

`lake build OpenMath.Chapter5.Section550` clean (`✔ Built
OpenMath.Chapter5.Section550 (4.7s)`, 2718/2718 jobs).

Sorry count remains at 0; net advance: one new axiom-clean public
theorem.

## Faithfulness check

Entity `thm:550A`, statement quoted from
`extraction/formalization_data/entities/thm_550A.json`:

> The coefficients in the characteristic polynomial of `X`,
> `det(wI − X) = wⁿ + γ₁wⁿ⁻¹ + γ₂wⁿ⁻² + ⋯ + γₙ`, are given by
> `1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(zⁿ⁺¹)`.

Lean statement at `n = 3` captures: **same content** at the `n = 3`
specialisation. `det(I − zX) − α(z)·β(z) = O(z⁴) = O(z^{n+1})` near
`z = 0`, exactly Butcher's claim with `n = 3`. The intermediate
identification `1 + γ₁z + ⋯ + γₙzⁿ = det(I − zX)` (relating the
characteristic-polynomial coefficients to the reciprocal-determinant
expansion) is an algebraic equality that holds termwise without
`O(z^{n+1})` — our statement focuses on the second equation
`det(I − zX) = α(z)·β(z) + O(z^{n+1})`, which is the asymptotic claim
the textbook then uses in §551–§553.

* No new `def` introduced this cycle.
* No new `class` or `structure` introduced.
* Tautology check: conclusion `IsBigO ...` does not appear as a
  hypothesis (the only hypotheses are the `α β : Fin 3 → ℂ` data).
* Identity check: proof is multi-step, not `exact h` — closes a
  genuine algebraic identity (cancellation of `z⁰…z³` coefficients in
  `det(I − zX) − α(z)·β(z)`) and a genuine asymptotic bound.
* Hypothesis strength check: only `α β : Fin 3 → ℂ` — minimal.
* Definition smuggling check: N/A (no new `def`).
* Absent theorem check: no comments promise unwritten content.

## Dead ends

1. **Direct application of cycle-140 `n = 2` template**
   (`unfold doublyCompanionMatrix; simp only [Matrix.det_fin_three,
   Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_succ,
   Fin.sum_univ_zero]; ring_nf; suffices … ; convert … ring`).
   Compiled to `ring_nf` (residue normalised correctly to
   `-(z^4·α0·β2) - z^4·β0·α2 + (-(z^4·β1·α1) - z^5·β1·α2)
     + (-(z^5·α1·β2) - z^6·α2·β2)`), but the next `convert h_factor
   using 2; ring` step type-mismatched: `funext` was given a `∀ hj :
   ↑0 + 1 = 3, ...` term whose left-hand side still contained
   `if h : 2 = 0 then ... else ...` from unreduced
   `doublyCompanionMatrix` branches at the corner cell.
   `simp only` over the doubly-companion definition did not decide the
   nested `j.val + 1 = n` conditions for n = 3 the way it did for
   n = 2 (where `Fin.sum_univ_two` + `Matrix.det_fin_two` rolled the
   simpler 2×2 expansion). Pivoted to the explicit-`!![…]` matrix
   approach (cycle-138 `_one_eq` style), which sidesteps the
   if-then-else reduction by computing the matrix once via
   `fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]`.

2. **`add_le_add_right (norm_add_le _ _) _`** to chain the
   triangle-inequality applications. The Mathlib `add_le_add_right`
   in this scope produced `c + ‖a‖ + ‖b‖ ≥ c + ‖a + b‖` (left
   addition) instead of the expected `‖a+b‖ + c ≤ (‖a‖ + ‖b‖) + c`
   form — same dispatch quirk noted in
   `feedback_add_le_add_left_dispatch.md`. Replaced with `linarith
   [h1, h2]` over the two intermediate `norm_add_le` `have`s, which
   closed cleanly.

3. **`mul_le_mul_of_nonneg_left h_inner (by positivity)`** failed
   with `failed to synthesize Zero ?m.…` because the goal RHS `C *
   ‖y⁴‖` had `‖y⁴‖` on the right of `C`, and the lemma expected the
   common factor on the left. Restructured into a `calc` with an
   explicit `mul_comm` step, which closed cleanly.

## Discovery

**The `_one_eq` style explicit-`!![…]` matrix expansion is the
robust template for `det_fin_n` proofs over the doubly-companion
definition at small `n`.** The cycle-140 `unfold + norm_num
[Fin.sum_univ_two]` shortcut works specifically because at n = 2 the
piecewise definition has only 2 branches (row 0 with j = 1 → corner;
others → sub-diagonal or zero) and the `if-then-else` chains decide
fully. At n = 3 there are 3 distinct positional roles (corner,
last-column non-zero rows, sub-diagonal) with overlapping `if h :
j.val + 1 = n` conditions — `simp only` doesn't reliably reduce these
together. Pre-extracting the matrix via `fin_cases` yields a clean
`!![…]` literal that all subsequent tactics handle uniformly.

This template should generalise to n = 4, 5, … if a future cycle
wants more concrete data points before tackling general `n`. Each
new `n` needs only:
* `ext + fin_cases × 2 + simp [doublyCompanionMatrix]` to extract X
  as `!![…]`;
* a second `fin_cases` block to expand `1 − z • X`;
* `Matrix.det_fin_n` (exists for n ≤ 5 in Mathlib, I believe);
* `simp [alphaPoly, betaPoly, Fin.sum_univ_n]; ring` to close the
  polynomial identity;
* a triangle-inequality chain whose length scales linearly with the
  number of higher-order monomials (`(n+1)+(n+2)+…+2n`, so 3 terms
  for n = 3, 5 terms for n = 4).

## Suggested next approach

For Planner cycle 145, several open paths in priority order:

1. **`thm:550A` n = 4 stepping stone.** Mechanical extension of the
   `_n_three` template per the discovery above. ~120–150 LOC,
   axiom-clean, single cycle. A fourth data point would solidify the
   leading-coefficient pattern further. Risk: triangle-inequality
   chain has 5 terms instead of 3 — slightly more boilerplate but no
   new infrastructure.

2. **`def:530A` r = 3 heterogeneous-stages witness** (Cycle 144's
   Backup A, deferred). Adds `nontrivialThreeStageGRK`,
   `mixedStages3`, `mixedMethod3`, `mixedStartingMethod3` plus the
   non-degeneracy and stage-distinctness witnesses. ~80–100 LOC,
   axiom-clean. Builds on cycle 141's r = 2 design.

3. **`def:520F` r = 2 negative L-stable witness**
   (`padded2DImplicitMidpointGLM_not_isLStable`, Cycle 144's Backup
   B, deferred). Lifts cycle 137's r = 1 negative witness to r = 2
   via the same padding scheme as `padded2DBackwardEulerGLM`. ~120
   LOC, axiom-clean.

4. **General-`n` `thm:550A` via cofactor expansion induction** —
   still multi-cycle infrastructure investment per
   `.prover-state/issues/thm_550A_general_n.md`. With three concrete
   `n` data points now in hand (`n = 1, 2, 3`), an induction proof
   would have a strong base case to anchor.

5. **`def:530B` / `def:530C` (Order relative to starting method)** —
   off-table per cycle 142/143 strategy guidance; multi-cycle
   infrastructure.

Recommendation: paths (1), (2), or (3) all give axiom-clean
single-cycle progress. Path (1) is the most direct continuation of
this cycle's work; path (2) opens variety on the §530 side.
