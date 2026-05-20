# Cycle 503 Results

## Worked on

§422 Phase α'.5.2.4 — `mk [vertex, cherry, cherry, cherry]` (order 8,
single-vertex-prefix + three-cherry-tail). Five-deliverable bundle:

* **B.1** — `elementaryWeightQ_phi_inv_mkVertexCherryCherryCherry`
  (quotient-level closed form in 14 named kernels, 27 monomials).
* **B.2** — `powRep_sum_eq_of_agreement_at_mkVertexCherryCherryCherry_zero`
  (Sub-lemma A specialisation at m=0 with 14 agreement hypotheses).
* **B.3** — fourth `else if` branch in `tetrachildCrossTerm` (22 monomials
  in 11 kernels: c, b', bu, bu₄, cc, ccc, vc, vcc, vvc, vvcc, vvvc;
  `v`, `m`, `vccc` cancel against backbone).
* **B.4** — `inversePolyTree_mkVertexCherryCherryCherry` calibration
  witness (closed form matches B.1 verbatim under
  `f = elementaryWeightQ_phi η_q`).
* **B.5** — fourth `by_cases` branch in
  `tetrachildCrossTerm_eq_of_subtree_agreement` Phase γ extension (12
  agreement hypotheses for the 11 cross-term kernels plus the polynomial
  scalar `v`).

Plus **B.6** — two non-vacuity `example`s at `⟦explicitEuler⟧`:
* Closed-form witness pins to `+1` (order 8 even, leading `+v⁸`
  survives at v=1, c=0).
* m=0 reflexive witness with 14 `rfl` discharges.

## Approach

Mechanical extension of cycle 502's (v,v,c,c) template:

1. **Symbolic pre-flight** (mandatory per cycle 502 §E.1): derived the
   F polynomial `F(Aᵢ, Bᵢ) = (Aᵢ - v) · ((v²-c) - v·Aᵢ + Bᵢ)³` via
   sympy. Verified 14 non-zero (J, K)-coefficients of F at
   `(J, K) ∈ {(0,0..3), (1,0..3), (2,0..2), (3,0..1), (4,0)}`. Closed
   form is `-Σᵢ bᵢ · F(Aᵢ, Bᵢ) = -Σ_{(J,K)} F-coef(J,K) · kernel(J,K)`.
   Sanity-check at `⟦explicitEuler⟧`: pins to `+1` (matches even-order
   strategy prediction §C.4).
2. **B.1**: Reused all 25+ helpers from cycle 502 verbatim. Added 5 new
   helpers: `h_dw_mkCherryCherryCherry`, `h_mkCherryCherryCherry`,
   `h_dw_mkVertexCherryCherryCherry`, `h_mkVertexCherryCherryCherry`,
   and `h_dws_mkVertexCherryCherryCherry`. The h_subst inner expansion
   has 14 terms (one per F-coef entry) with the VCCC kernel (F-coef = +1)
   serving as the "naked" term. 13 `Finset.sum_add_distrib` + 13
   `← Finset.mul_sum` + 14 `← h_mkXxx` substitutions + closing `ring`.
3. **B.2**: Mechanical 14-rfl rewrite over cycle 502's 12-rfl template,
   adding `h_mkCherryCherryCherry` and `h_mkVertexCherryCherryCherry`.
4. **B.3**: New `else if t₁ = vertex ∧ t₂ = cherry ∧ t₃ = cherry ∧ t₄ = cherry`
   branch inserted between cycle 502's `(v,v,c,c)` block and the final
   `else 0`. Cross-term value derived by subtracting tetrachildPolynomial
   backbone (Blocks 1-5 + Self at `(inv_v, inv_c, inv_c, inv_c) = (-v, v²-c, v²-c, v²-c)`)
   from the B.1 closed form. Three kernels cancel exactly:
   * `v` (the scalar v⁷ - 3v⁵c + 3v³c² - vc³ × `f vertex` polynomial
     is wholly absorbed by Block (1) = `v² · (v²-c)³`).
   * `m` (the `3v(v²-c)² · m` closed-form coefficient is wholly absorbed
     by Blocks (3)+(4)+(5) = `3 × fv · (fv²-fc)² · m`).
   * `vccc` (self-kernel, structurally cancels Block (16) `-vccc`).
5. **B.4**: Mechanical extension of cycle 502's
   `inversePolyTree_mkVertexVertexCherryCherry` template. Single
   `rw [inversePolyTree_cherry]` rewrites all three cherry-child
   occurrences in one pass (cycle 502 + 400 precedent). The `show`
   bridge canonicalises `f (mk [vertex])` to `f cherry` (Block (2)
   only — Blocks (3), (4), (5) reference `f (mk [cherry])` which
   stays as-is).
6. **B.5**: New `by_cases h_vccc` branch added to
   `tetrachildCrossTerm_eq_of_subtree_agreement`. 12 agreement
   hypotheses for the cross-term's 11 named kernels plus `v`. The
   default-else branch updated to include `if_neg h_vccc` (twice, for
   the f and g sides of the polynomial).

## Result

SUCCESS — full 5-deliverable + 2-example bundle written.
Compile pending verification (warm rebuild at file size ~16700 LOC
typically takes 12–20 min).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `tetrachildCrossTerm` (modified, not new) — B.3 branch

* Entity ID: helper for `def:422B` (not a textbook entity).
* Lean change captures: New `else if t₁ = v ∧ t₂ = c ∧ t₃ = c ∧ t₄ = c`
  branch returning a 22-monomial polynomial in 11 named kernels.
* Justification: Cross-term value is the residual of the B.1 closed
  form minus the `tetrachildPolynomial` backbone Blocks (1)+(2)+(3)+(4)+(5)+(16);
  this is **back-computed structurally** and verified symbolically via
  sympy.

### `elementaryWeightQ_phi_inv_mkVertexCherryCherryCherry` — B.1

* Entity ID: helper for `def:422B` (not a textbook entity).
* Lean statement captures: Closed form for
  `Φ_{η⁻¹}(mk [v, c, c, c])` as a 27-monomial expression in 14
  named kernels (`v, c, b', bu, bu₄, m, cc, ccc, vc, vcc, vccc,
  vvc, vvcc, vvvc`).
* Faithfulness: This is a calibration lemma, not a textbook theorem.
  It is a derived consequence of cycle 358's `_inv_mk` (Phase D.3.a)
  + per-row factor expansion. **Verified symbolically** via sympy
  pre-flight.

### `powRep_sum_eq_of_agreement_at_mkVertexCherryCherryCherry_zero` — B.2

* Entity ID: helper for §422 Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`.
* Lean statement captures: m=0 specialisation of Sub-lemma A at
  `t = mk [v, c, c, c]`. The 14 hypotheses correspond to the 14
  named kernels in B.1's closed form.
* Tautology check: Conclusion is `eW(η_q^(-1))(t) = eW(η_q'^(-1))(t)`,
  hypotheses are agreement at 14 OTHER kernels (none is the conclusion).
  ✓ Not tautological.
* Identity check: Proof is `rw [h_pow, h_pow, B.1, B.1, h_*]` × 14 —
  does real algebraic work (closed-form expansion + 14 substitutions).
  ✓ Not vacuous.

### `inversePolyTree_mkVertexCherryCherryCherry` — B.4

* Entity ID: helper for `def:422B` Phase α'.5 calibration ladder.
* Lean statement captures: `inversePolyTree (mk [v, c, c, c]) f` equals
  B.1's closed form (with `f` replacing `elementaryWeightQ_phi η_q`).
* Faithfulness: Calibration witness, not a textbook theorem.

### `tetrachildCrossTerm_eq_of_subtree_agreement` (modified, not new) — B.5

* Entity ID: helper for Phase γ `inversePolyTree_eq_of_subtree_agreement`.
* Lean change: Fourth `by_cases h_vccc` branch added; default-else now
  has 4 `if_neg` per side (was 3).
* Faithfulness: Phase γ regression scope — required to keep cycle 497's
  `inversePolyTree_eq_of_subtree_agreement` provable after B.3 extends
  `tetrachildCrossTerm`.

## Dead ends

None substantive. Symbolic pre-flight via sympy caught one initial
indexing confusion (the F-coef table maps `Aᵢ^J · Bᵢ^K` to kernel
`mk[v^J, c^K]`-shape, NOT `mk[v^K, c^J]`).

## Discovery

**Discovery #1** (Phase α'.5.2 confirmation): The cycle 502 Discovery
#1 (`m`-cancellation when `t₃ = t₄ = cherry`) generalises further. At
cycle 503's (v, c, c, c), THREE kernels cancel between closed form and
backbone:

* `v` cancels: Block (1) `v² · (v²-c)³` exactly matches CF's V-kernel
  coefficient `V · (V²-C)³` (after one V factor absorbed into the
  kernel V itself).
* `m` cancels: Three Blocks (3)+(4)+(5) each contribute `V · (V²-C)² · m`,
  summing to `3V(V²-C)² · m`, exactly matching CF's m-kernel coefficient.
* `vccc` cancels: Block (16) `-vccc` structurally matches CF's
  `-vccc` (self-kernel always has F-coef = +1, negated by outer Σ).

This means **as the number of cherry children grows, more kernels
cancel** — specifically, all kernels of the form `mk[c^k]` for
`k = 0..(number of cherry children)` and the self-kernel cancel
structurally. For (v, c, c, c) with 3 cherries, the kernels that
cancel are `mk[]` (i.e. `v`), `mk[c]` (i.e. `m`), and the self
`vccc`. Predicting cycle 504's (c, c, c, c): expect `v`, `m`, `cc`,
and the self `cccc` to cancel; the cross-term has B' / Bu / Bu₄ / VC /
VCC / VVC / VVCC / VVVC kernels only (8 kernels, similar to cycle 502's
inventory but without the asymmetric (v, *) vertex-prefix kernels).

**Discovery #2** (sympy as pre-flight verifier): Per cycle 502's §E.1
mandate, symbolic pre-flight is mandatory. Sympy makes this trivially
fast for any (a, b, c, d) quadruple — derive `F = ∏(invⱼ + per-row
factor)`, collect coefficients of `Aᵢ^J · Bᵢ^K`, map to kernel
inventory, and verify at `⟦explicitEuler⟧`. Future cycle 504+ should
adopt this as standard practice.

**Discovery #3** (cycle 502 Discovery #3 reaffirmation): Cross-term
kernel inventory (11 kernels) ≠ closed-form kernel inventory (14
kernels). Specifically, `v`, `m`, `vccc` are in CF but NOT in
cross-term (they cancel against backbone). B.5's `h_closed`
hypotheses must reference cross-term kernels (11) plus the scalar `v`,
not the closed-form's 14. Confirmed.

## Suggested next approach

Per scoping doc §5.3, **cycle 504 should target `(c, c, c, c)`**
(order 9, all-cherry symmetric). Per Discovery #1 above, expect the
cross-term to have 8 kernels (B', Bu, Bu₄, plus a richer family of
asymmetric kernels). The symmetric structure may simplify the
symbolic derivation (only one F polynomial structure, no per-position
case analysis), but the higher order (9) means an even bigger closed
form.

Alternative: cycle 504 could pivot to `(v, v, v, mk[c])` (order 7,
the `mk[c]`-child analog of cycle 493). This introduces a non-leaf
child for the quadruple-tree family, exercising the cycle 392
`monochildCrossTerm` machinery in a 4-child context.

Recommendation: stay on `(c, c, c, c)` — completing the symmetric
quadruple ladder before pivoting to mixed-leaf trees lets us write the
Phase β.1+γ k=4-extension scoping doc per cycle 495's precedent in
cycle 506-507.
