# Cycle 378 Results

## Worked on

§422 Sub-lemma A 8-tree ladder extension — depth-3 single-child ladder
`mk [mk [cherry]]` (8th tree, order-4). Six deliverables per cycle 378
strategy:

1. Closed-form theorem `elementaryWeightQ_phi_inv_mkMkCherry`.
2. m=0 corollary `powRep_sum_eq_of_agreement_at_mkMkCherry_zero`.
3. Phase α.4 branch in `inversePolynomial`.
4. Phase α.4 calibration witness.
5. Phase β.4 bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`.
6. Phase β aggregator refresh (7-way → 8-way) + Phase γ extension
   (`inversePolynomial_eq_of_subtree_agreement` new `by_cases` block +
   default branch grew `if_neg h_mkMkCherry` per side).

## Approach

Followed cycle 371's `mk [broom₃]` template (depth-2 ladder closed form)
with one extra unfold layer to handle the depth-3 structure
`mk [mk [cherry]]`. Key new helpers in the closed-form proof:

* `h_inv_mkCherry` — representative-form lift of cycle 369's quotient
  theorem `elementaryWeightQ_phi_inv_mkCherry`.
* `h_dw_mkMkCherry`, `h_mkMkCherry` — derivative/elementary weight
  closed form `Σⱼ Aᵢⱼ · Σ_k A_jk · Σ_l A_kl`.
* `h_dws_mkMkCherry` — `derivativeWeightWithSrc M.inverse i (mk [mk [cherry]])`
  via one outer cons-case unfold + cycle 369's `h_dws_mkCherry` for the
  inner layer.

The `h_subst` body required pre-distributing the inner sum
`Σⱼ Aᵢⱼ · (inv_c + inv_v · Σ_k A_jk + Σ_k A_jk · Σ_l A_kl)` into three
separate terms via `Finset.sum_add_distrib` × 2 + `← Finset.mul_sum` × 2
so `ring` could match the 4-term per-summand decomposition.

After `_inv_mk + _mk × 4 + h_sum` and `ring`, the closed form
`v⁴ − 3v²c + c² + 2vm − M_mkMkCherry` falls out cleanly.

The Phase γ extension required a NEW `by_cases h_mkMkCherry` block
mirroring cycle 377's `mk [vertex, cherry]` block; the default branch
gained one more `if_neg h_mkMkCherry` per side (forced by the cycle 377
precedent's documented pre-flight `lake build` break — observed and
patched exactly as predicted).

Aristotle: not used this cycle. The deliverables are all mechanical
extensions of established cycle 369/371/372/377 patterns; the closed-form
recipe is well-templated and Aristotle's free compute is better reserved
for genuinely novel proofs (the body of cycle 365's `_strict_subtree_agreement`
sorry is the obvious candidate, gated on Phase α').

## Result

**SUCCESS** — all 6 deliverables shipped, `lake build OpenMath.Chapter4.Section422`
exits 0, `grep -c sorry` = 5 (4 docstring + 1 grandfathered, unchanged).

Axiom check on the 4 new public theorems + 1 touched aggregator:

| Symbol | Axioms |
|---|---|
| `elementaryWeightQ_phi_inv_mkMkCherry` | `[propext, Classical.choice, Quot.sound]` |
| `powRep_sum_eq_of_agreement_at_mkMkCherry_zero` | `[propext, Classical.choice, Quot.sound]` |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry` | `[propext, Classical.choice, Quot.sound]` |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` (refreshed 7→8) | `[propext, Classical.choice, Quot.sound]` |
| `inversePolynomial_eq_of_subtree_agreement` (extended) | `[propext, Classical.choice, Quot.sound]` |

§422 axiom-clean streak: **43 substantive + 1 doc** (cycles 336–378).
Section422.lean: 4954 → 5594 LOC (+~640).

Non-vacuity witnesses on `⟦explicitEuler⟧`:
* `Φ_{⟦explicitEuler⟧⁻¹}(mk [mk [cherry]]) = 1` — verified.
* Reflexive m=0 witness with `rfl rfl rfl rfl` (four agreement hyps). — verified.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `elementaryWeightQ_phi_inv_mkMkCherry`
- **Entity ID**: infrastructure theorem, no Butcher entity ID (Phase D.3
  Sub-lemma A ladder data point per `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`).
- **Statement**: algebraically-derived closed form
  `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry`.
- **Lean statement captures**: derivation matches the cycle 358 `_inv_mk`
  + per-summand `derivativeWeightWithSrc` unfold + sum algebra exactly.
  Sanity check on `⟦explicitEuler⟧`: predicted value = 1, witnessed = 1. ✓
  Re-derivation on paper before shipping (per Risk register R1)
  confirmed `v⁴ − 3v²c + c² + 2vm − M` is correct.

### `powRep_sum_eq_of_agreement_at_mkMkCherry_zero`
- **Entity ID**: infrastructure corollary of the closed form (m=0
  specialisation of cycle 365's Sub-lemma A signature).
- **Statement**: four-hypothesis specialisation
  `(h_vertex, h_cherry, h_mkCherry, h_mkMkCherry) ⇒ Φ at mk [mk [cherry]] coincide`.
- **Lean statement captures**: matches the closed form's
  four-tree dependency set. Deliberately OMITS `h_broom₃` — the closed
  form does not depend on `broom₃`, so requiring agreement at `broom₃`
  would be a hypothesis strictly stronger than the textbook needs.
  Documented in the docstring with explicit comparison to cycles 371/372
  (which carried a strictly unused `h_broom₃` for ladder uniformity).
  This is a **faithfulness improvement** over the cycle 371/372
  templates.

### `inversePolynomial` (Phase α.4 branch extension)
- **Statement extension**: appends an 8th `else if` branch for
  `mk [mk [cherry]]` returning `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry`.
- **Lean statement captures**: matches the closed form of
  `elementaryWeightQ_phi_inv_mkMkCherry` by construction. Calibration
  witness `(example with 7 if_neg + if_pos rfl)` verifies the branch
  evaluates as expected.

### `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`
- **Entity ID**: Phase β.4 bridge.
- **Statement**: equality between the §383 inverse class image and the
  closed-form polynomial.
- **Lean statement captures**: matches the per-tree pattern from
  cycles 375/377. Proof routes through 7 `if_neg` + `if_pos rfl`
  + `elementaryWeightQ_phi_inv_mkMkCherry η_q`.

### `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` (refresh)
- **Signature change**: 7-way disjunction → 8-way (added `mk [mk [cherry]]`).
- Preserves the cycle 375/377 type signature with one new disjunct.

### `inversePolynomial_eq_of_subtree_agreement` (extension)
- **Signature change**: unchanged.
- **Proof change**: added one new `by_cases h_mkMkCherry` block between
  the cycle 377 `mk [vertex, cherry]` block and the default branch;
  default branch gained `if_neg h_mkMkCherry` per side.

### Tautology / Identity / Hypothesis strength checks

- **Tautology check**: no theorem's conclusion is verbatim a hypothesis. ✓
- **Identity check**: no theorem closes by `exact h` for a pre-existing
  `h` without intermediate work. ✓
- **Hypothesis strength check**: m=0 corollary's hypothesis set is
  MINIMAL (four hypotheses matching the closed form's four-tree
  dependency set; no spurious `h_broom₃` carried over from cycles
  371/372). ✓
- **Definition smuggling check**: `inversePolynomial`'s 8th branch
  encodes the algebraically-derived closed-form expression; not a
  redefinition of any named mathematical concept. ✓

## Dead ends

None. The closed-form derivation matched the strategy's pre-computed
value on first compile; the Phase γ default-branch break occurred
exactly as predicted by the strategy; the m=0 corollary discharged its
hypotheses via the standard `zero_add + Nat.cast_one + zpow_neg_one`
chain per memory `feedback_neg_natCast_int_negsucc_rfl.md`.

## Discovery

### D1 — `mk [mk [cherry]]` closed form genuinely does not depend on `broom₃`

The closed form `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry` has no `broom₃`
term, in contrast to cycles 371's `mk [broom₃]` and 372's
`mk [vertex, cherry]` which both have `+ v·broom₃` terms.

This is consistent with the empirical pattern emerging across the 8-tree
ladder:
* depth-1 (vertex, cherry, broom₃): closed form depends only on subtrees.
* depth-2 (mk [cherry], bushy, mk [broom₃], mk [vertex, cherry]):
  closed forms can have non-subtree terms (e.g. `mk [broom₃]` and
  `mk [vertex, cherry]` both depend on `broom₃`).
* depth-3 (mk [mk [cherry]]): single-child ladder, the dependency set
  appears to follow the chain of left-most descendants
  (v, c, mk [cherry], mk [mk [cherry]]) without lateral coupling.

For Phase α' coefficient identification, this suggests that single-child
ladder cases have a particularly clean recursive structure. The four
trees in the ladder of single-child depth (v, c, mk [cherry],
mk [mk [cherry]]) have closed forms with coefficients
`{(-1), (-1, 1), (-1, 2, -1), (-1, 3, -1, 2)}` (signed by depth).
Specifically:
* `v ↦ −v`
* `c ↦ v² − c`
* `mk[c] ↦ −v³ + 2vc − mc`
* `mk[mk[c]] ↦ v⁴ − 3v²c + c² + 2v·mc − mmc`

The pattern in coefficient counts: 1, 2, 3, 5. The factor-by-factor
products suggest Catalan- or Schröder-like growth, which may give
Phase α' a cleaner combinatorial recipe than the general trees.

### D2 — Pre-flight build break occurred exactly as predicted

Per the strategy's Step 4 directive: after inserting the Phase α.4
branch, `lake build` broke the Phase γ default branch with the goal
shape predicted by the strategy
(`if t = mk [mk [cherry]] then ... else 0 = ...`). The fix was exactly
the prescribed `if_neg h_mkMkCherry` per side. This validates the
"forced by build" approach as a reliable mechanical pattern; cycle 379+
should expect the same shape if it adds a 9th branch.

## Suggested next approach

### Option A (recommended) — Phase α' (recursive `inversePolynomial`) scoping

The 8-tree ladder is now closed and provides 8 closed-form data points
for Phase α' analysis. The depth-3 single-child case (cycle 378)
illuminates the "subtree-chain" pattern (D1 above), which gives a
candidate recipe for the single-child branch of the recursion. A cycle
379 scoping doc could:

1. Catalog the 8 closed forms and their coefficient patterns.
2. Identify the structural rule for the single-child ladder
   (`v, c, mk[c], mk[mk[c]], ...` extending to `mk^n [vertex]`).
3. Identify the structural rule for the two-child symmetric ladder
   (`vertex, cherry, broom₃, bushy, ...`).
4. Identify the structural rule for the heterogeneous-child cases
   (`mk [vertex, cherry], mk [broom₃, cherry], ...`).
5. Propose a recursive form for `inversePolynomial` that subsumes all
   3 patterns and matches the 8 closed forms by `rfl` after unfold.

This is a multi-cycle research effort (likely 3-5 cycles for the
scoping + 5-10 cycles for the recursive `inversePolynomial` redefinition
+ matching proof migration). Cycle 379 should start with the scoping
doc only.

### Option B — Extend the ladder to a 9th tree

Candidates: `mk [vertex, vertex, vertex]` (3-child symmetric, order 4),
`mk [cherry, cherry]` (2-child symmetric, order 5), or `mk [vertex,
broom₃]` (2-child asymmetric, order 5). Each adds one more empirical
data point for Phase α' but is mechanical extension of cycles 371/372
templates. Probably less valuable than Option A's scoping.

### Option C (NOT recommended) — Phase δ on the 8-tree ladder

The cycle 366 / 378 strategies both explain why Phase δ on the ladder
is blocked: the `Φ_{η_q^(-(m+1))}(t) = Φ_{η_q'^(-(m+1))}(t)` induction
step expands via cycle 358 `_mul_mk` to a sum involving
representative-specific `M.b` and `derivativeWeightWithSrc M` data, and
comparing across η_q and η_q' requires the Phase α' machinery. Don't
attempt without Phase α' in place.

### Risk register update for cycle 379+

* **R1 (closed-form value verification)**: not applicable to a scoping
  doc (Option A).
* **R3 (Phase γ default branch grows by 1)**: will fire again on cycle
  379 IF that cycle extends `inversePolynomial`. Forced fix is well-
  understood.
* **R6 (NEW) — Phase α' recursive shape design**: the recursive form
  must handle non-leaf children that ARE in the ladder (e.g.,
  `mk [cherry]`'s contribution to `mk [vertex, cherry]`'s closed form).
  A naive subtree-product recursion will not capture this; an analysis
  of multi-child mixing (perhaps via a "tree composition" operator) may
  be needed. Cycle 379 scoping should explicitly identify this risk
  before committing to a recursive shape.
