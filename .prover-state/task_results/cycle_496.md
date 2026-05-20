# Cycle 496 Results

## Worked on

§422 Phase β.1 ship: per-tree dispatch theorem for `inversePolyTree`
over the 14-tree ladder. Deliverable per the cycle 495 scoping doc
`.prover-state/issues/def_422B_phase_beta_gamma_scoping.md` §5.1.

**One new public theorem** in `OpenMath/Chapter4/Section422.lean`:
`elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder` (~75 LOC
including docstring + signature + 14-way `rcases` body), placed
immediately after cycle 377's 8-tree
`elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` (line 11538).

## Approach

Per the strategy headline, this is a **mechanical 14-way dispatch**:

```
rcases ht_ladder with h | h | … | h     -- 14-way
all_goals subst h                        -- specialise t per branch
· rw [_inv_<tree>, inversePolyTree_<tree>]   -- per-branch closure
```

Each branch's pair of rewrites collapses both sides of the target
equation
`elementaryWeightQ_phi η_q⁻¹ t = inversePolyTree t (elementaryWeightQ_phi η_q)`
to a syntactically identical closed-form polynomial in
`elementaryWeightQ_phi η_q` evaluated at named subtrees of `t` — closure
is implicit `rfl` after the `rw` cascade (Lean's `rw` tactic closes a
goal reduced to definitional equality).

The 14 calibrations consumed:

| # | Tree | `_inv_<tree>` cycle | `inversePolyTree_<tree>` cycle |
|---|------|---------------------|-------------------------------|
| 1 | `vertex` | 341 | 387 |
| 2 | `cherry` | 367 | 387 |
| 3 | `broom₃` | 368 | 389 |
| 4 | `mk [cherry]` | 369 | 394 |
| 5 | `bushy` | 370 | 400 |
| 6 | `mk [broom₃]` | 371 | 392 |
| 7 | `mk [vertex, cherry]` | 372 | 390 |
| 8 | `mk [mk [cherry]]` | 378 | 395 |
| 9 | `mk [cherry, cherry]` | 384 | 388 |
| 10 | `mk [broom₃, cherry]` | 386 | 389 |
| 11 | `mk [vertex, vertex, cherry]` | 403 | 403 |
| 12 | `mk [vertex, cherry, cherry]` | 491 | 492 |
| 13 | `mk [vertex, vertex, mk [cherry]]` | 493 | 493 |
| 14 | `mk [vertex, vertex, broom₃]` | 494 | 494 |

**Pre-flight verification** (strategy §"Pre-flight verification"):
ran `grep -nE "^theorem (elementaryWeightQ_phi_inv|inversePolyTree)_"`
on Section422.lean and confirmed all 14 `_inv_<tree>` + all 14
`inversePolyTree_<tree>` witnesses exist. Inspected each pair's
closed-form RHS to confirm algebraic alignment — every pair matches
verbatim under the substitution `f := elementaryWeightQ_phi η_q`, by
construction (the cycle 387–494 calibrations were designed to match
the cycle 367–494 `_inv_<tree>` shapes).

**Did NOT** attempt to close the cycle 365 grandfathered sorry at
`Section422.lean:2279`; per the strategy §"What NOT to try", that
closure is gated on Phase β.2 + γ + δ + ε (cycles 497–~501 per the
scoping doc §5).

**Did NOT** raise `maxHeartbeats` or introduce any new calibration
witness; the 14 needed are all pre-existing.

## Result

**SUCCESS.**

1. New theorem `elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder`
   compiles axiom-clean under `lake env lean OpenMath/Chapter4/Section422.lean`.
2. `#print axioms` returns `[propext, Classical.choice, Quot.sound]`
   (default Lean 4 trio; no new axioms).
3. Sorry count unchanged at 5 (4 docstring + 1 grandfathered cycle
   365). Verified via `grep -c sorry Section422.lean`.
4. `extraction/formalization_data/lean_status.json`'s `def:422B`
   `cycle_completed_at` bumped 495 → 496 (status remains `partial`).
5. `plan.md`'s `def:422B` row appended with a cycle 496 sentence
   summarising the Phase β.1 ship.
6. §422 axiom-clean streak: 68 substantive + 5 doc (336–495) →
   **69 substantive + 5 doc** (336–496).

## Faithfulness check

**One new theorem** introduced:
`elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder`.

- **Entity ID**: N/A — Phase β.1 is **infrastructure**, not a
  textbook entity. The deliverable does not correspond to any
  `extraction/formalization_data/entities/<id>.json` row. (Per the
  strategy §"Faithfulness check obligations", Phase β.1 is
  infrastructure validation for `def:422B`'s sorry closure plan, not
  a new textbook theorem.)
- **Lean statement captures**: a real algebraic identity bridging
  the quotient-level inverse `elementaryWeightQ_phi η_q⁻¹ t` and the
  recursive polynomial `inversePolyTree t (elementaryWeightQ_phi η_q)`
  over the 14-tree calibration ladder. NOT a tautology — the
  conclusion is genuinely different from any hypothesis.
- **Tautology check**: conclusion `LHS = inversePolyTree t …` does
  not appear as a hypothesis. Hypotheses are `η_q` (a quotient
  group element), `t` (a rooted tree), and `ht_ladder` (a 14-way
  disjunction membership predicate). PASS.
- **Identity check**: proof is NOT a single `exact h` or `id`;
  it is a 14-way case-split with non-trivial `rw` cascades per
  branch (each invoking one `_inv_<tree>` + one
  `inversePolyTree_<tree>` named theorem). PASS.
- **Hypothesis strength check**: `ht_ladder` is essential — without
  it, `inversePolyTree` returns the default `0` off-ladder (per the
  cycle 374 pattern-match definition's default branch and the
  cycle 399 `mk`-triple-children branch's default `0`), but
  `elementaryWeightQ_phi η_q⁻¹ t` is generically nonzero. The
  statement is false without `ht_ladder`. PASS.
- **Definition smuggling**: no new `def` or `structure` introduced;
  no smuggling possible. PASS.

## Dead ends

None — the strategy's recipe (rcases + per-branch `rw [..., ...]`)
worked first-try as described. No `ring` or `show` bridge needed:
each pair of rewrites produces a definitionally-`rfl` goal that the
`rw` cascade closes automatically.

The strategy listed potential pitfalls (order-6 branches' 9–10
named kernels possibly needing `show` bridges per memory
`feedback_ring_def_opacity.md`); these did not materialise because
the calibration witnesses (cycles 491–494) were carefully designed
to match the `_inv_<tree>` shapes verbatim under `f :=
elementaryWeightQ_phi η_q`. Closure is genuinely mechanical.

## Discovery

1. **The `rw [_inv_<tree>, inversePolyTree_<tree>]` pattern closes
   without `ring` for all 14 branches.** This is stronger than the
   strategy anticipated: the closed forms match syntactically (not
   just algebraically) after both rewrites. No `ring`-mediated
   algebraic reconciliation is required on any of the 14 branches.

   This is because the cycle 387–494 calibration witnesses were
   each written to produce the **exact same RHS** as the
   corresponding cycle 367–494 `_inv_<tree>` theorem (modulo the
   substitution `f ↔ elementaryWeightQ_phi η_q`). The Phase α'.4–5
   workers absorbed all the `ring`-level reconciliation into the
   calibration proofs themselves, leaving Phase β.1 to be a pure
   dispatch.

2. **`rw` is enough; no `exact rfl` needed at the end of each
   branch.** Lean's `rw` tactic closes goals that reduce to `rfl`
   after the rewrite. The final `rw [..., ...]` per branch produces
   `<closed_form> = <closed_form>` which is reflexively true; the
   `rw` machinery closes it implicitly.

3. **The `inversePolyTree t (elementaryWeightQ_phi η_q)` signature
   (without the `fun s => …` η-expansion mentioned in the strategy
   §"What to ship" example) works fine.** Lean unifies the two forms
   automatically. The signature is cleaner without the lambda
   wrapper.

## Suggested next approach

**Cycle 497 should ship Phase β.2** (structural induction on
`t : RT` lifting Phase β.1 to the full type), per the cycle 495
scoping doc §5.2.

Concrete target (paraphrasing the scoping doc):

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolyTree t (elementaryWeightQ_phi η_q) := by
  -- Structural induction on `t`.
  -- Base/small-tree cases dispatch through cycle 496's
  -- `_eq_inversePolyTree_on_ladder` for the 14-tree match.
  -- For `mk (_::_::_::_::_)` quadchild+ trees (Risk R6), both
  -- sides evaluate to `0`:
  --   * RHS: `inversePolyTree` default `0` branch (cycle 399).
  --   * LHS: need new lemma
  --     `elementaryWeightQ_phi_inv_mkBigArity (η_q : …) (cs : List RT)
  --      (hcs : cs.length ≥ 4) :
  --      elementaryWeightQ_phi η_q⁻¹ (mk cs) = 0`
  --     — this is the substantive net-new infrastructure for cycle 497.
  sorry
```

The cycle 495 scoping doc §5.2 estimates Phase β.2 at 300–500 LOC
including the in-line R6.B `mkBigArity` helper. R6 is marked HIGH
risk because Butcher's textbook does not provide an explicit
"quadchild trees collapse to 0" identity; the cycle 497 worker may
need to derive it from the cycle 399 `mk`-children dispatch's
default branch and a corresponding LMM-side identity. Allow scope
expansion if the R6.B helper requires more than 200 LOC.

**Cycle 497 should also**:
1. Verify cycle 496's `_eq_inversePolyTree_on_ladder` integrates as
   the small-tree dispatch site in the structural induction without
   modification.
2. Consider extracting `mkBigArity` to a private helper if its body
   exceeds 100 LOC, per the cycle 365 sorry's `dws`-level pattern.

**Cycles 498–~501**: Phase γ (cycle 498), Phase δ.B (cycles
499–500), Phase ε (cycle ~501) per the scoping doc §5. Risk R9
(Phase δ.B HIGH) is the remaining substantive challenge.

**Pre-cycle-496 streak**: 68 substantive + 5 doc.
**Post-cycle-496 streak**: **69 substantive + 5 doc** (cycles
336–496).
**Projected post-cycle-~501**: 73–76 substantive + 5 doc, with the
cycle 365 sorry closed and `Section422.lean` fully sorry-free.
