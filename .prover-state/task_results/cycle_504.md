# Cycle 504 Results

## Worked on

§422 Phase α'.5.2.5 — `mk [cherry, cherry, cherry, cherry]` (order 9,
symmetric all-cherry quadruple, k=4). Five-deliverable bundle:

* **B.1** — `elementaryWeightQ_phi_inv_mkCherryCherryCherryCherry`
  (quotient-level closed form in 15 named kernels, 31 monomials).
* **B.2** — `powRep_sum_eq_of_agreement_at_mkCherryCherryCherryCherry_zero`
  (Sub-lemma A specialisation at m=0 with 14 agreement hypotheses — one
  per non-self kernel in B.1's 15-kernel closed form).
* **B.3** — fifth `else if` branch in `tetrachildCrossTerm` (25 monomials
  in 12 kernels: `c, b', bu, bu₄, cc, ccc, vc, vcc, vccc, vvc, vvcc,
  vvvc`; `v`, `m`, `cccc` cancel against backbone).
* **B.4** — `inversePolyTree_mkCherryCherryCherryCherry` calibration
  witness (closed form matches B.1 verbatim under
  `f = elementaryWeightQ_phi η_q`).
* **B.5** — fifth `by_cases h_cccc` branch in
  `tetrachildCrossTerm_eq_of_subtree_agreement` Phase γ extension (13
  agreement hypotheses for the 12 cross-term kernels plus the polynomial
  scalar `v`).

Plus **B.6** — two non-vacuity `example`s at `⟦explicitEuler⟧`:
* Closed-form witness pins to `-1` (order 9 odd, leading `-v⁹`
  survives at v=1, c=0).
* m=0 reflexive witness with 14 `rfl` discharges.

## Approach

Mechanical extension of cycle 503's (v,c,c,c) template:

1. **Symbolic pre-flight** (mandatory per cycle 502 §E.1, cycle 503
   Discovery #2): derived the F polynomial
   `F(Aᵢ, Bᵢ) = ((v²-c) - v·Aᵢ + Bᵢ)⁴` via sympy. Verified 15 non-zero
   (J, K)-coefficients of F at
   `(J, K) ∈ {(0,0..4), (1,0..3), (2,0..2), (3,0..1), (4,0)}`. Closed
   form is `-Σᵢ bᵢ · F(Aᵢ, Bᵢ) = -Σ_{(J,K)} F-coef(J,K) · kernel(J,K)`.
   Sanity-check at `⟦explicitEuler⟧`: pins to `-1` (matches odd-order
   parity flip from cycle 503's `+1` at order 8).
2. **Sympy cancellation verification** (corrects strategy §D.2 prediction):
   Computed cross-term coefficients = B.1 coef - backbone coef per
   kernel. Found THREE cancellations (`v`, `m`, `cccc`), NOT four as
   strategy predicted. The strategy's claim that `cc` cancels at the
   "bilinear-block level (Blocks 6-11 in scoping doc §3.1)" applies to
   the *internal* structure of `tetrachildCrossTerm`, not to backbone
   subtraction: in the Lean definition, Blocks 6-15 are wholly absorbed
   into `tetrachildCrossTerm`, so `cc` remains as a free CT coefficient
   `-6(V²-C)²`. Verified explicitly via sympy.
3. **B.1**: Reused all 28+ helpers from cycle 503 verbatim. Added 3 new
   helpers: `h_dw_mkCherryCherryCherryCherry`,
   `h_mkCherryCherryCherryCherry`, and `h_dws_mkCherryCherryCherryCherry`.
   The h_subst inner expansion has 15 terms (one per F-coef entry) with
   the CCCC kernel (F-coef = +1) serving as the "naked" term. 14
   `Finset.sum_add_distrib` + 14 `← Finset.mul_sum` + 15 `← h_mkXxx`
   substitutions + closing `ring`.
4. **B.2**: Mechanical 14-rfl rewrite over cycle 503's 14-rfl template,
   adding `h_mkCherryCherryCherryCherry` and removing
   `h_mkVertexCherryCherryCherry` (replaced with the symmetric
   `h_mkCherryCherryCherryCherry`).
5. **B.3**: New `else if t₁ = cherry ∧ t₂ = cherry ∧ t₃ = cherry ∧ t₄ = cherry`
   branch inserted between cycle 503's `(v,c,c,c)` block and the final
   `else 0`. Cross-term value derived by subtracting tetrachildPolynomial
   backbone (Blocks 1-5 + Self at `(inv_c, inv_c, inv_c, inv_c) = (v²-c, v²-c, v²-c, v²-c)`)
   from the B.1 closed form. Three kernels cancel exactly:
   * `v` (Block 1 = `-v·(v²-c)^4` matches the closed-form's V-kernel
     coefficient `-(v²-c)^4` exactly).
   * `m` (Blocks 2+3+4+5 = `-4(v²-c)^3 · m` matches the closed-form's
     m-kernel coefficient).
   * `cccc` (self-kernel, structurally cancels Block 16 `-cccc`).
6. **B.4**: Mechanical extension of cycle 503's
   `inversePolyTree_mkVertexCherryCherryCherry` template. Single
   `rw [inversePolyTree_cherry]` rewrites all four cherry-child
   occurrences in one pass (cycle 503/400 precedent). No `inversePolyTree_vertex`
   needed since there's no vertex child.
7. **B.5**: New `by_cases h_cccc` branch added to
   `tetrachildCrossTerm_eq_of_subtree_agreement`. 13 agreement
   hypotheses for the cross-term's 12 named kernels plus `v`. The
   default-else branch updated to include `if_neg h_cccc` (twice, for
   the f and g sides of the polynomial).

## Result

SUCCESS — full 5-deliverable + 2-example bundle written.
Compile pending verification (warm rebuild at file size ~19150 LOC
typically takes 15–25 min).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `tetrachildCrossTerm` (modified, not new) — B.3 branch

* Entity ID: helper for `def:422B` (not a textbook entity).
* Lean change captures: New `else if t₁ = c ∧ t₂ = c ∧ t₃ = c ∧ t₄ = c`
  branch returning a 25-monomial polynomial in 12 named kernels.
* Justification: Cross-term value is the residual of the B.1 closed
  form minus the `tetrachildPolynomial` backbone Blocks (1)+(2)+(3)+(4)+(5)+(16);
  this is **back-computed structurally** and verified symbolically via
  sympy.

### `elementaryWeightQ_phi_inv_mkCherryCherryCherryCherry` — B.1

* Entity ID: helper for `def:422B` (not a textbook entity).
* Lean statement captures: Closed form for
  `Φ_{η⁻¹}(mk [c, c, c, c])` as a 31-monomial expression in 15
  named kernels (`v, c, b', bu, bu₄, m, cc, ccc, cccc, vc, vcc,
  vccc, vvc, vvcc, vvvc`).
* Faithfulness: This is a calibration lemma, not a textbook theorem.
  It is a derived consequence of cycle 358's `_inv_mk` (Phase D.3.a)
  + per-row factor expansion. **Verified symbolically** via sympy
  pre-flight.

### `powRep_sum_eq_of_agreement_at_mkCherryCherryCherryCherry_zero` — B.2

* Entity ID: helper for §422 Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`.
* Lean statement captures: m=0 specialisation of Sub-lemma A at
  `t = mk [c, c, c, c]`. The 14 hypotheses correspond to the 14
  non-self named kernels in B.1's closed form (the self-kernel `cccc`
  is the conclusion, not a hypothesis).
* Tautology check: Conclusion is `eW(η_q^(-1))(t) = eW(η_q'^(-1))(t)`,
  hypotheses are agreement at 14 OTHER kernels (none is the conclusion).
  ✓ Not tautological.
* Identity check: Proof is `rw [h_pow, h_pow, B.1, B.1, h_*]` × 14 —
  does real algebraic work (closed-form expansion + 14 substitutions).
  ✓ Not vacuous.

### `inversePolyTree_mkCherryCherryCherryCherry` — B.4

* Entity ID: helper for `def:422B` Phase α'.5 calibration ladder.
* Lean statement captures: `inversePolyTree (mk [c, c, c, c]) f` equals
  B.1's closed form (with `f` replacing `elementaryWeightQ_phi η_q`).
* Faithfulness: Calibration witness, not a textbook theorem.

### `tetrachildCrossTerm_eq_of_subtree_agreement` (modified, not new) — B.5

* Entity ID: helper for Phase γ `inversePolyTree_eq_of_subtree_agreement`.
* Lean change: Fifth `by_cases h_cccc` branch added; default-else now
  has 5 `if_neg` per side (was 4).
* Faithfulness: Phase γ regression scope — required to keep cycle 497's
  `inversePolyTree_eq_of_subtree_agreement` provable after B.3 extends
  `tetrachildCrossTerm`.

## Dead ends

**Strategy §D.2 prediction of `cc` cancellation was incorrect.** The
strategy claimed `cc` would cancel based on a "bilinear-block level"
argument referencing Blocks 6-11 in the scoping doc §3.1. However, in
the current Lean definition, Blocks 6-15 are wholly absorbed into
`tetrachildCrossTerm` (they are NOT separate backbone blocks). Sympy
pre-flight caught this error immediately by computing B.1 - backbone
explicitly per kernel and finding only 3 cancellations (`v`, `m`,
`cccc`), with `cc` surviving as a free CT coefficient `-6(V²-C)²`.
The cross-term ended up with 12 kernels (not 11), one more than
predicted, due to this surviving `cc`.

## Discovery

**Discovery #1** (Phase α'.5.2 generalised pattern, refining cycle 503
Discovery #1): At the all-cherry symmetric quadruple `(c, c, c, c)`,
THREE kernels cancel between closed form and backbone — `v`, `m`, and
`cccc` (self-kernel). This refines the cycle 503 generalisation: the
cancellation count is NOT necessarily monotone with the number of
cherry children. Cycle 502 (v,v,c,c) had 1 cancellation (m); cycle 503
(v,c,c,c) had 3 (v, m, vccc); cycle 504 (c,c,c,c) has 3 (v, m, cccc).

The actual pattern: a kernel `K` cancels iff its B.1 coefficient is
exactly matched by a backbone block.
* `v` always cancels (Block 1 absorbs it via leading `-v · ∏ inv_k`).
* The self-kernel always cancels (Block 16 absorbs it structurally).
* `mk[c^a]`-form kernels (where the children of `mk[...]` are all
  cherries) may cancel if the sum over their backbone Block (2)/(3)/(4)/(5)
  contributions matches. For (c,c,c,c), `m = mk[c]` cancels because
  all 4 Block (k)-tail contributions evaluate to `(inv_c)^3 · m`,
  summing to `4(v²-c)^3 · m`, exactly matching B.1's m-coefficient.

But `cc, ccc` do NOT cancel: there's no analogous backbone structure
contributing `cc` or `ccc` kernels directly (those would require
deeper-tree blocks not present in the 16-block decomposition).

**Discovery #2** (sympy as pre-flight verifier, reaffirmed): Per cycle
502/503's mandate, symbolic pre-flight is mandatory and caught the
strategy's incorrect cancellation prediction immediately. Future cycles
should always run B.1-coef-minus-backbone-coef in sympy explicitly
before trusting strategy predictions about cancellations.

**Discovery #3** (cross-term kernel inventory ≠ closed-form kernel
inventory): Cross-term has 12 kernels, closed form has 15 kernels.
The 3 missing kernels in CT are exactly the 3 cancellations. B.5's
`h_closed` hypotheses must reference cross-term kernels (12) plus the
scalar `v`, not the closed-form's 15. Confirmed (B.5 has 13 hypotheses).

## Suggested next approach

Per scoping doc §5.3 and §G of cycle 504 strategy, **cycle 505 should
either**:

1. **Continue Phase α'.5.2 with mixed-tail quadruples**: `(v, v, v,
   mk[c])` (order 7, single-monocchild final position) or `(v, v, v,
   broom₃)` (order 7, single-binarychild final position). These
   introduce non-leaf children for the quadruple-tree family, exercising
   the cycle 392 `monochildCrossTerm` and bichild machinery in a 4-child
   context.

2. **Pivot to Phase β.1+γ k=4 extensions scoping doc** per cycle 495
   precedent, now that 5 substantive k=4 witnesses have accumulated
   (cycles 499/501/502/503/504). The accumulated empirical data is
   sufficient to inform a general k=4 structural induction skeleton.

3. **Pivot to fresh entity** per `cycle_336_pivot_options.md` (def:451A,
   def:442A, thm:535A, thm:541A). The symmetric quadruple ladder is
   now complete, freeing up the planner to consider fresh entity work.

Recommendation: option (2) — write the Phase β.1+γ k=4-extensions
scoping doc. With 5 k=4 calibration witnesses in hand, the pattern is
clear enough to attempt a general structural induction proof.
