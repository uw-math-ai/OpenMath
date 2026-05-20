# Cycle 495 Results

## Worked on

§422 Phase β/γ scoping doc for closing the cycle 365 grandfathered
sorry at `OpenMath/Chapter4/Section422.lean:2279`
(`powRep_sum_eq_of_strict_subtree_agreement` general body).

**Deliverable**: one markdown file at
`.prover-state/issues/def_422B_phase_beta_gamma_scoping.md` (779 LOC,
§§1–11), plus a `lean_status.json` cycle-completed-at bump and a
`plan.md` cycle-495 note. No Lean code touched.

## Approach

Per the cycle 495 strategy headline, this is a **markdown-only
scoping cycle** mirroring the cycle 373 / 379 / 385 / 398 / 402
precedents. The strategy explicitly instructed: do NOT write Lean
code, do NOT ship Phase α'.5.2 witnesses, do NOT pivot to a fresh
entity. The sole deliverable is the scoping doc itself.

Process followed:

1. **Read the strategy** (`.prover-state/strategy.md`, 346 LOC) and
   the cycle 494 task results (the chain of cycles 386–494 has been
   building empirical surface; cycle 495 is the strategic pivot
   point from "accumulate" to "consume").
2. **Located the cycle 365 sorry** at `Section422.lean:2272–2279`
   (`powRep_sum_eq_of_strict_subtree_agreement`); confirmed it's the
   sole code-level sorry (`grep -c sorry` = 5 = 4 docstring + 1
   code).
3. **Surveyed prior scoping docs** (`def_422B_path.md`,
   `def_422B_phase_D_3_scoping.md`,
   `def_422B_subLemmaA_inductive_plan.md`,
   `def_422B_phase_alpha_prime_scoping.md`,
   `def_422B_phase_alpha_prime_family_C_scoping.md`,
   `def_422B_phase_alpha_prime_family_bushy_scoping.md`,
   `def_422B_phase_alpha_prime_5_scoping.md`) for tone, structure,
   and LOC envelope (sizes range 894–1399 LOC; targeted middle of
   range).
4. **Identified Phase γ precedent** at `Section422.lean:11578`
   (cycle 376's `inversePolynomial_eq_of_subtree_agreement`, the
   8-tree closed-subtree agreement) and Phase β.1 precedent at
   `Section422.lean:11513` (cycle 377's
   `_inv_eq_inversePolynomial_on_ladder`, the 8-tree per-tree
   dispatch). Both are direct templates for the new
   `inversePolyTree`-level Phase β.1 / γ deliverables.
5. **Surveyed the 14-tree calibration ladder** (cycles 367–494's
   `_inv_<tree>` theorems + cycles 387–494's
   `inversePolyTree_<tree>` calibration witnesses) to confirm
   sufficient empirical surface for the Phase β.1 dispatch.
6. **Wrote the scoping doc** following the §1–§9 structure mandated
   by the strategy, plus appended §10 (expected supervisor
   scoring) and §11 (§422 streak status) per the cycle 402
   precedent.

The doc decomposes the cycle 365 closure into **5 single-cycle
deliverables**:

* **Phase β.1** (~200–300 LOC): per-tree dispatch over the 14-tree
  ladder. Direct mechanical extension of the existing cycle 377
  `_eq_inversePolynomial_on_ladder` (8 trees → 14 trees;
  `inversePolynomial` → `inversePolyTree`).
* **Phase β.2** (~300–500 LOC): structural induction on `t : RT` to
  lift Phase β.1 to the full type. Includes inline `R6.B` for the
  `mk (_::_::_::_::_)` quadchild-zero arm.
* **Phase γ** (~200–350 LOC): `inversePolyTree`-level closed-subtree
  agreement. Direct generalisation of cycle 376's
  `inversePolynomial_eq_of_subtree_agreement` template.
* **Phase δ.B** (~300–500 LOC, possibly split across 2 cycles):
  inverse-power `Nat.rec` lift from `η_q⁻¹` to `η_q^(-(m+1))`.
* **Phase ε** (~50–150 LOC): final closure of the cycle 365 sorry.

Total estimate: 5–8 cycles (cycles 496–~503).

## Result

**SUCCESS.**

1. Scoping doc shipped at
   `.prover-state/issues/def_422B_phase_beta_gamma_scoping.md` (779
   LOC, well within the strategy's 600–1000 LOC target).
2. `extraction/formalization_data/lean_status.json` bumped
   `def:422B`'s `cycle_completed_at` from 494 → 495 (status remains
   `partial`).
3. `plan.md`'s `def:422B` row appended with a cycle 495 sentence
   summarising the scoping doc and the cycle 496+ entry point.
4. Sorry count unchanged at 5 (4 docstring + 1 grandfathered cycle
   365 code sorry) — verified by `grep -c sorry
   OpenMath/Chapter4/Section422.lean`.
5. No Lean file changes — verified by `git diff --stat` showing only
   `.prover-state/`, `plan.md`, and `lean_status.json` paths.

## Faithfulness check

**N/A — no new Lean entities introduced this cycle.**

No new `def`, `structure`, or `theorem` was added; no existing Lean
file was modified. The scoping doc is pure markdown.

The doc's §2 quotes the cycle 365 sorry verbatim from
`Section422.lean:2272–2279` (not paraphrased). The doc's §3.1
catalogs the 14 calibration witnesses by cycle, tree, order, and
kernel count — drawn from the `git log` ship records and the
`Section422.lean` `^theorem elementaryWeightQ_phi_inv_` grep list,
both verifiable in-repo. The doc's §3.2 / §3.3 quote the existing
cycle 376 / 377 theorem signatures from
`Section422.lean:11513–11537` and `Section422.lean:11578–11595`
verbatim (the templates Phase β.1 / γ generalise from).

The doc's §4 / §5 proposed signatures (Phase β.1, β.2, γ, δ.B, ε)
are **provisional Lean sketches**, not commitments — they may be
refined by cycle 496+ workers based on what `inversePolyTree`'s
recursion actually consumes at the structural-induction step.

## Dead ends

None — the strategy's headline decision (Option 1: Phase β/γ
scoping) was followed directly without deviation. The §"Why Phase
β/γ scoping over the alternatives" rationale was preserved in the
doc's §1 / §11 framing.

## Discovery

1. **Cycle 376's `inversePolynomial_eq_of_subtree_agreement`
   already exists** as the 8-tree precedent for Phase γ. The Phase
   γ deliverable in this scoping doc (for `inversePolyTree`,
   14 trees + structural-induction default arm) is a direct
   generalisation, not a from-scratch design.

2. **Cycle 377's
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`
   already exists** as the 8-tree precedent for Phase β.1. The
   Phase β.1 deliverable (for `inversePolyTree`, 14-tree ladder)
   is mechanical: case-split + `_inv_<tree>` + `inversePolyTree_<tree>`
   + `ring` per branch. ~200–300 LOC realistic.

3. **The `mk (_::_::_::_::_)` quadchild arm is the primary
   net-new infrastructure Phase β.2 needs**: a proposition
   `elementaryWeightQ_phi (η_q⁻¹) (mk (c₁ :: c₂ :: c₃ :: c₄ :: cs))
   = 0`. The `inversePolyTree` recursion's default-`0` branch
   already commits to this on the RHS; the new content is proving
   the quotient-level LHS also evaluates to `0` for `k ≥ 4`-arity
   trees. Identified as Risk R6 (HIGH); recommended R6.B
   (in-line in Phase β.2) over R6.A (separate cycle).

4. **Phase δ.B's `dws`-mediated cross-product** (decomposing
   `η_q^(-(m+1)) * η_q⁻¹` via cycle 219's `_phi_mul`) is the place
   where the cycle 365 worker's original "heterogeneous Σ-type
   comparison" obstruction surfaces. The Phase γ closed-subtree
   agreement at the `dws` level (cycle 362) already exists and
   provides the per-row equality; the Phase δ.B challenge is
   threading the agreement through the `Nat.rec` on `m`.
   Identified as Risk R9 (HIGH).

5. **The doc's §11 framing — "strategic pivot from accumulate to
   consume" — is the right narrative arc**: cycles 386–494 spent
   109 cycles accumulating the 14-witness ladder; Phase β/γ
   consumes that ladder into the structural induction.
   Re-emphasising this in the supervisor-scoring §10 mitigates the
   markdown-only-cycle underweighting risk.

## Suggested next approach

**Cycle 496 should ship Phase β.1** (per-tree dispatch over the
14-tree ladder).

Concrete first task per §7 of the scoping doc:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (ht_ladder :
        t = RootedTree.vertex ∨ t = RootedTree.cherry
      ∨ t = RootedTree.broom₃ ∨ t = mk [RootedTree.cherry]
      ∨ t = RootedTree.bushy   ∨ t = mk [RootedTree.broom₃]
      ∨ t = mk [vertex, cherry] ∨ t = mk [mk [cherry]]
      ∨ t = mk [cherry, cherry] ∨ t = mk [broom₃, cherry]
      ∨ t = mk [vertex, vertex, cherry]
      ∨ t = mk [vertex, cherry, cherry]
      ∨ t = mk [vertex, vertex, mk [cherry]]
      ∨ t = mk [vertex, vertex, broom₃]) :
    elementaryWeightQ_phi (η_q⁻¹) t
      = inversePolyTree t (fun s => elementaryWeightQ_phi η_q s)
```

Proof: `rcases ht_ladder` + per-branch
`exact <_inv_<tree>_eq_inversePolyTree_<tree>>` (which is in turn
proved by `rw [_inv_<tree>, inversePolyTree_<tree>]; ring`).

LOC estimate: ~200–300 LOC.

**Cycle 496 should also**:
1. Verify before Phase β.1 ship that all 14 `_inv_<tree>` theorems
   and all 14 `inversePolyTree_<tree>` calibration witnesses are
   `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
2. Watch for the `ring`/`show` opacity bridge per memory
   `feedback_ring_def_opacity.md` (`f (mk [vertex])` vs `f cherry`
   canonicalisation).

**Cycles 497–501+**: Phase β.2 → γ → δ.B → ε per the scoping doc's
§5 phase decomposition. Expect Risk R6 (Phase β.2 quadchild-zero)
and Risk R9 (Phase δ.B heterogeneous Σ-comparison) to be the
substantive challenges; allow scope expansion if either escalates.

**Pre-cycle-495 streak**: 68 substantive + 4 doc.
**Post-cycle-495 streak**: 68 substantive + 5 doc (cycles 336–495).
**Projected post-cycle-~501**: 73–76 substantive + 5 doc, with the
cycle 365 sorry closed and `Section422.lean` fully sorry-free.
