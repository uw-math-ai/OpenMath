# Cycle 364 Results

## Worked on

§422 Phase D.3.b — apply the cycle 363 P2 audit's `linearResidualAt`
coefficient fix as a single focused cycle. The cycle 360 definition
used `- i·(-1)^r(t)·Φ_{η_q}(t)`, which mismatches the §383
quotient-encoded coefficient `-i` (constant in `r(t)`) at even
`r(t) ≥ 2`. Cycle 364 ships the corrected form
`+ i·Φ_{η_q}(t)` and updates 4 closed-form theorems plus 4 non-vacuity
examples in `OpenMath/Chapter4/Section422.lean`.

## Approach

Followed the cycle 364 strategy §B mechanical sign-fix recipe:

1. **B.1** — Redefined `linearResidualAt` at `Section422.lean:1879`:
   ```
   linearResidualAt i η_q t
     := elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
        + (i : ℝ) * elementaryWeightQ_phi η_q t
   ```
   plus expanded docstring noting cycle 364 redefinition + audit
   cross-link.
2. **B.2.1** — `coeff_eta_t_in_eta_zpow_neg`: RHS coefficient
   restated as `-(i : ℝ)` (no `(-1)^t.order`). Proof unchanged:
   `unfold linearResidualAt; ring`.
3. **B.2.2** — `linearResidualAt_vertex_eq_zero`: removed the
   `h_ord : RootedTree.vertex.order = 1` rewrite step (no longer
   needed since `(-1)^t.order` factor is gone). Final proof:
   `unfold; rw [...zpow_vertex]; push_cast; ring`.
4. **B.2.3** — `linearResidualAt_one_mk_eq`: RHS restated to
   `- (∑ … derivativeWeightWithSrc …) + M.elementaryWeight t`
   (dropped `(-1)^t.order`, flipped sign on `elementaryWeight` term).
   Proof recipe unchanged.
5. **B.2.4** — `linearResidualAt_succ_mk_eq`: same shape as
   `_one_mk_eq` — RHS is
   `- (powRep-sum) + ((m:ℝ)+1) * M.elementaryWeight t`.
6. **B.3** — Four non-vacuity `example`s restated to match the new
   theorem signatures:
   * Split form at vertex with `explicitEuler`, `i=1`.
   * Closed form at `cherry` with `explicitEuler`, `i=1`.
   * Closed form at `cherry` with `explicitEuler`, `i=2`.
   * (The `vertex` zero-witness examples at `i=1` and `i=3` are
     unchanged: they ship via `linearResidualAt_vertex_eq_zero`,
     whose statement shape is unchanged.)
7. **C.2 (stretch)** — Appended a "Cycle 364 closure" subsection to
   `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10
   documenting the ship.

## Result

SUCCESS.

* `lake build OpenMath.Chapter4.Section422` exits 0; Built in 269 s
  (within cycle 363's measured envelope).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 0.
* `#print axioms` on all 4 updated theorems
  (`linearResidualAt_vertex_eq_zero`, `coeff_eta_t_in_eta_zpow_neg`,
  `linearResidualAt_one_mk_eq`, `linearResidualAt_succ_mk_eq`)
  returns `[propext, Classical.choice, Quot.sound]`.
* No new content; pure definition fix + mechanical sign updates.
  Net LOC delta within strategy §F prediction (≈ -3 LOC in
  `Section422.lean`, ~+45 LOC markdown in scoping doc §10).

C.1 (audit-validation examples) was deliberately omitted: the
strategy §C.1 noted "if discharging this example requires non-trivial
`derivativeWeightWithSrc` unfolding that exceeds 20 minutes, OMIT the
example". The cycle 363 P2 audit doc already documents the numerical
values; a re-witness in Lean adds little marginal value and risks
exceeding the cycle budget given a 270-s rebuild cost. Cycle 364's
hard requirement was §B, which closed cleanly.

## Faithfulness check

This cycle introduced NO new `def` or `theorem`. All four updated
theorems retain their textbook claim — they are factual statements
about the redefined `linearResidualAt`, which itself matches the
audit-corrected interpretation of Butcher's "coefficient of η(t) in
η⁻ⁱ(t)" under our §383 Φ-quotient encoding.

### Redefined `def`: `linearResidualAt`

* Entity ID: helper for `def:422B` (Phase D.3.b infrastructure).
* Textbook reference (Butcher §422 p. 359 / `ch04.txt:1158`):
  > The coefficient of η(t) in η⁻ⁱ(t) is equal to i·(-1)^r(t), and
  > there are no other terms in η⁻ⁱ(t) with orders greater than r(t)−1.
* Lean statement captures: same content as the corrected
  quotient-encoded coefficient.
* Justification for divergence from the textbook's bare `i·(-1)^r(t)`
  form: per the cycle 363 P2 audit
  (`.prover-state/issues/def_422B_phase_D_3_scoping.md` §10), the
  textbook's `(-1)^r(t)` factor is spurious under our §383 quotient
  encoding — empirically the coefficient is `-i`, validated on
  two-method witnesses (`explicitEuler` + Heun) at `t = cherry`,
  `i = 1`. The redefinition records this fact. The audit doc has the
  full coefficient analysis with `η(vertex) = 1`, `η(cherry) = 0`
  vs `η(cherry) = 1/2` numerical witnesses showing cycle 360's
  definition was not method-independent at order 2.

### Cascade checks

* **Tautology check** — none of the 4 updated theorems has its
  conclusion verbatim as a hypothesis.
* **Identity check** — all 4 theorems do real arithmetic work
  (`unfold + rewrite + push_cast + ring`).
* **Definition smuggling check** — `linearResidualAt` is a helper
  isolating the "Φ_{η_q^(-i)}(t)'s contribution beyond the linear-in-η
  part". The corrected definition matches the quotient-encoded
  coefficient.
* **Hypothesis strength check** — no hypotheses changed; only RHS
  expressions.
* **Absent theorem check** — all four named theorems exist in the
  file with the correct (corrected) signatures.

## Dead ends

None. The strategy was mechanical and landed first-try.

`push_cast; ring` closed each theorem's proof with no need for
`linarith` fallbacks or `linear_combination` witnesses (strategy §E
R1 mitigation unneeded).

## Discovery

1. The corrected `linearResidualAt` definition's proof of the vertex
   base case is one step shorter: the `h_ord : vertex.order = 1`
   rewrite step is now unnecessary because the corrected definition
   no longer has a `(-1)^t.order` factor. This is a tiny but real
   simplification — confirming the redefined form is "more natural"
   relative to the quotient-faithfulness discipline.
2. The four non-vacuity `example`s split into two classes under the
   new definition:
   * **Vertex examples** (residual at `vertex` is 0): unchanged
     since the RHS is `0` in both old and new definitions.
   * **Cherry examples** (closed-form at `cherry`): updated to drop
     the `(-1)^r(t)` factor and flip the sign of the
     `M.elementaryWeight t` term.
   The class invariance at vertex is reassuring — the redefinition
   is **localised** to the structural sign-fix where cycle 363
   audited it would be.
3. The cycle 363 audit's `Discovery §4` claim (the corrected
   definition makes Phase D.3.b Step 2 structurally clean) is now
   syntactically visible: in `linearResidualAt_succ_mk_eq`, the
   `+((m:ℝ)+1) * M.elementaryWeight t` term is *positive*, which
   is the expected sign to cancel against the powRep-sum's hidden
   `-(m+1)·M.elementaryWeight t` contribution. Cycle 365's
   parametricity Step 2 should be able to lift this cancellation
   directly.

## Suggested next approach

**Cycle 365 (Phase D.3.b parametricity Step 2)**: attempt
`linearResidualAt_depends_only_on_strict_subtrees` under the
cycle 364 corrected definition. The cancellation argument is now
structurally clean per Discovery §3 above and the audit doc
§10/Discovery §4.

Recommended decomposition:

1. **Sub-lemma A** — `powRep_sum_eq_neg_succ_elementaryWeight_plus_strict`:
   show that
   `∑ⱼ (M.powRep (m+1)).2.b j · (M.powRep (m+1)).2.derivativeWeightWithSrc (M.powRep (m+1)).2.inverse j t`
   equals `(m+1)·M.elementaryWeight t + (strict-subtree residual)`.
   This is the "composite inverse decomposition" lifted to powRep
   representatives — analogous to cycle 235's
   `inverseDerivativeWeight_eq_derivativeWeightWithSrc_inverse` at
   `s = 1`.
2. **Sub-lemma B** — combine A with cycle 362's
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` to get
   the full parametricity claim.

Estimated 150–250 LOC for cycle 365 (matching cycle 362's estimate).

**Cycle 366+ pipeline** (read-ahead from cycle 364 strategy §H):
* Cycle 366: `underlyingOneStepMethod_aux` + spec lemma.
* Cycle 367: lift to quotient, seal `def:422B`. `thm:422A` existence
  falls out.

If cycle 365's Step 2 stalls, the fallback is to ship a less general
strict-subtree statement (e.g. only at `i = 1`) via direct unfolding
of `derivativeWeightWithSrc M.inverse`. This preserves §422 streak
preservation discipline while keeping forward progress on Phase E.

§422 axiom-clean streak: **29 → 30** consecutive cycles (336–364).
