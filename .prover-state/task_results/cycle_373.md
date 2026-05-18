# Cycle 373 Results

## Worked on

`.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` — a new
multi-cycle scoping doc distilling the closed-form pattern revealed
by cycles 367–372's witness ladder into a concrete phased plan for
closing the **Sub-lemma A body** of `def:422B` Phase D.3.b
(`powRep_sum_eq_of_strict_subtree_agreement`, sorry'd at
`OpenMath/Chapter4/Section422.lean:2279`).

Per the cycle 373 strategy §J, this cycle is markdown-only: no Lean
file edits, no new sorries, no axiom changes. The 38-consecutive-
cycle §422 axiom-clean streak (336–372) is preserved.

## Approach

Per the cycle 373 strategy §F task list:

1. Read `def_422B_phase_D_3_scoping.md` end-to-end to understand
   the current state and locate cycle 365's Sub-lemma A statement.
   Identified the per-cycle update blocks (357–372) as the
   authoritative trace of why prior approaches (cycle 366
   `Quotient.inductionOn₂` + `_inv_mk`; cycle 365 strong induction
   + cycle 362) failed.
2. Read `lem_310B_plan.md` (cycle 260 produced) to internalise the
   template structure for multi-phase scoping docs — 10 sections
   (status, blocker, textbook source, distilled content,
   project-hook inventory, gap inventory, phase decomposition, risk
   assessment, cycle 374 entry point, cross-references).
3. Re-read the seven cycle 341/367–372 closed-form witnesses to
   confirm the §C.1 pattern table (vertex through `mk [vertex,
   cherry]`).
4. Verified line numbers and namespaces by `Grep` against HEAD
   `b1bfe32` for every cited symbol:
   - `Section422.lean`: `linearResidualAt` (1885),
     `coeff_eta_t_in_eta_zpow_neg` (1900),
     `linearResidualAt_vertex_eq_zero` (1918),
     `linearResidualAt_one_mk_eq` (1939),
     `elementaryWeightQ_phi_zpow_natCast_mk` (2040),
     `elementaryWeightQ_phi_zpow_negSucc_mk` (2061),
     `linearResidualAt_succ_mk_eq` (2118),
     `powRep_sum_eq_of_strict_subtree_agreement` (2272, sorry at
     2279), `powRep_sum_eq_of_agreement_at_vertex` (2314),
     `elementaryWeightQ_phi_inv_cherry` (2376),
     `powRep_sum_eq_of_agreement_at_cherry_zero` (2477),
     `elementaryWeightQ_phi_inv_broom₃` (2538),
     `powRep_sum_eq_of_agreement_at_broom₃_zero` (2695),
     `elementaryWeightQ_phi_inv_mkCherry` (2772),
     `powRep_sum_eq_of_agreement_at_mkCherry_zero` (2941),
     `elementaryWeightQ_phi_inv_bushy` (3011),
     `powRep_sum_eq_of_agreement_at_bushy_zero` (3229),
     `linearResidualAt_depends_only_on_strict_subtrees` (3288,
     `[propext, sorryAx, Classical.choice, Quot.sound]` — auto-
     upgrades when Sub-lemma A body lands),
     `elementaryWeightQ_phi_inv_mkBroom₃` (3397),
     `powRep_sum_eq_of_agreement_at_mkBroom₃_zero` (3704),
     `elementaryWeightQ_phi_inv_mkVertexCherry` (3798),
     `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero` (4135),
     `elementaryWeightQ_phi_mul_mk` (536),
     `elementaryWeightQ_phi_inv_mk` (582),
     `elementaryWeightQ_phi_pow_succ_mk` (632),
     `elementaryWeightQ_phi_zpow_vertex` (433),
     `sum_i_alpha_ne_zero_of_stable_preconsistent` (953).
   - `Section381.lean`: `RKTableau.powRep` (4437),
     `RKTableau.powRep_quotient_eq` (4450),
     `RKTableau.derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
     (2830),
     `RKTableau.derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement`
     (2853), `elementaryWeightQ_phi_composeQ_phi_mk` (4867).
   - `Section301.lean`: `RootedTree.order_eq` (112),
     `RootedTree.order_pos` (159),
     `RootedTree.order_lt_of_mem_children` (167),
     `instance : WellFoundedRelation RootedTree := measure
     RootedTree.order` (177).
5. Wrote the 1018-line scoping doc following `lem_310B_plan.md`'s
   structure, covering all 10 strategy-mandated sections (§D.1
   line-number cross-checks; §D.2 conjecture content with formal
   statement; §7 phase decomposition with concrete cycle 374 entry
   point at Phase α; §I discovery slot covering coefficient
   patterns).

## Result

**SUCCESS — scoping doc shipped.**

- `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` — 1018
  lines markdown, slightly above the strategy's 500–800 target. The
  extra ~200 lines are concentrated in §5 (project-hook inventory
  table with 30+ symbols verified at HEAD), §7 (per-phase deliverable
  blocks with sub-tasks, exit criteria, and graceful-degradation
  fallbacks), and §10 (per-cycle task-result references for all 16
  prior cycles in the §422 chain). The strategy's §D template
  structure is followed verbatim.
- Zero Lean code changes — `Section422.lean`, `Section381.lean`, all
  other source files unchanged this cycle.
- Sorry count unchanged: 5 lines / 1 code sorry at
  `Section422.lean:2279` (the cycle 365 grandfathered Sub-lemma A
  body sorry).
- Axiom counts unchanged on all shipped theorems.
- `lean_status.json` unchanged; `plan.md` unchanged (per strategy
  §E).
- Streak preservation: §422 axiom-clean streak now **39 consecutive
  cycles (336–373)**.

The scoping doc's central deliverable is the **§4.4 conjecture**
(`inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ` defined by
well-founded recursion on `RootedTree.order`, with parts (a) and
(b) covering the equality-to-`Φ_{η_q⁻¹}` and the
subtree-agreement-monotonicity), plus the **§7 5-phase
decomposition** (α through ε):

- **Phase α** (cycle 374): define `inversePolynomial` with 7
  non-vacuity witnesses matching cycles 341/367–372.
- **Phase β** (cycle 375, possibly 376):
  `elementaryWeightQ_phi_inv_eq_inversePolynomial` via strong
  induction on `t.order`.
- **Phase γ** (cycle 376 or 377):
  `inversePolynomial_eq_of_subtree_agreement` via structural
  induction.
- **Phase δ** (cycle 377 or 378): lift to general `m` via cycle
  359's `powRep`.
- **Phase ε** (cycle 378 or 379): close Sub-lemma A body via
  3-line composition.

Total horizon: cycles 374–379 for Sub-lemma A close; cycles 380–382
for Phase D.3.d (`underlyingOneStepMethod_aux`); cycle 382 or 383 for
Phase E sealing of `def:422B`.

## Faithfulness check

**No new Lean definitions or theorems introduced this cycle —
faithfulness check N/A.** The cycle 373 task is markdown-only
scoping per the strategy. The faithfulness checks documented in
cycles 367–372 task results (each verifying the per-tree closed
form matches a paper-algebra derivation from cycle 358's `_inv_mk`)
carry over unchanged.

The scoping doc itself does **not** make any claims requiring
faithfulness validation against Butcher's textbook — the inductive
proof's content (the recursive shape of `Φ_{η_q⁻¹}`) is purely
internal to our Lean encoding (per the scoping doc §3, Butcher's
prose is silent on this structural argument).

## Dead ends

The scoping doc explicitly documents two approaches that were
investigated by prior cycles (366, 365) and found NOT to close
Sub-lemma A's body. These are cited in the doc's §8.3:

1. **Direct `Quotient.inductionOn₂` + cycle 358 `_inv_mk`
   expansion** on the two sides: after the inductionOn₂ on `η_q` and
   `η_q'`, cycle 358's `_inv_mk` formula expresses each side as a
   sum over representative-specific stage counts (`M.1` vs `M'.1`),
   which are generally different. There is no direct way to bridge
   the two heterogeneous sums via cycle 362's substitution lemma
   (which only substitutes the *source* tableau `M₁`, not the
   *inner* tableau `M₂`). — cycle 366 worker's finding.

2. **Strong induction on `t.order` using cycle 362 alone**: cycle
   362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
   bridges the `derivativeWeightWithSrc` sum's substitution behaviour
   but does not handle the *inner-tableau heterogeneity* between
   `M.powRep (m+1)` and `M'.powRep (m+1)`. — cycle 365 worker's
   finding, re-validated in cycle 366.

The §7 plan's `inversePolynomial`-based approach sidesteps **both**
obstructions by reducing both sides to the same `RootedTree → ℝ`
polynomial — the heterogeneous-stage-count issue vanishes because
`inversePolynomial t f` takes a tree and a real-valued function, no
stage counts involved. The Phase β equality
`Φ_{η_q⁻¹}(t) = inversePolynomial t (Φ_η)` is the load-bearing
bridge.

## Discovery

1. **Coefficient sign uniform in `r(t)`**: the seven cycle 341/367–372
   closed forms all have `−Φ_η(t)` with coefficient `−1`, constant in
   `r(t)`. This confirms the cycle 363 P2 audit's finding that
   Butcher's `(−1)^r(t)` factor is spurious under our Φ-quotient
   encoding. Documented in the scoping doc §4.5.

2. **No σ appearance in witness coefficients**: σ(t) — Butcher's
   tree symmetry coefficient — does NOT appear in any of the seven
   closed-form coefficients (verified by inspection: σ(`bushy`)=6,
   σ(`mk [broom₃]`)=2 do not show up; coefficients are all
   ±integer or ±rational with small denominators). This suggests
   the `inversePolynomial`'s combinatorial coefficient recipe is via
   the convolution structure (cycle 358 `_inv_mk` unrolling) rather
   than via tree-symmetry counting. Documented in the scoping doc
   §4.5.

3. **Broom-family closed form is binomial**: cycle 368/370's
   `(Aᵢ − v)^k` discovery generalises to the broom family
   `broom_k = mk [vertex, …, vertex]` (k child-vertices), with
   closed form
   `Σ_{j=0}^k (−1)^j · C(k,j) · v^{k−j} · w_j` where `w_j = Φ_η(broom_j)`.
   Verified at k=0 (vertex), k=1 (cherry), k=2 (broom₃), k=3 (bushy).
   Documented in the scoping doc §4.5. This may suggest a **combinatorial
   closed-form recipe** for `inversePolynomial` at non-broom trees too,
   though the seven witnesses include only one heterogeneous-children
   case (cycle 372 `mk [vertex, cherry]`) and so the full combinatorial
   pattern is not yet visible.

4. **Phase α's calibration data**: the 7 closed-form witnesses serve
   as **calibration data** for Phase α. The cycle 374 worker must
   define `inversePolynomial` such that the recursion evaluates
   correctly on these 7 trees by `rfl` or `unfold + ring`. If any
   witness fails, Phase α has the wrong shape and must be redesigned
   before Phase β can proceed.

5. **`linearResidualAt_depends_only_on_strict_subtrees`
   auto-upgrade**: per cycle 365's headline ship structure, once
   Sub-lemma A's body lands, the Sub-lemma B headline at
   `Section422.lean:3288` automatically upgrades from `[propext,
   sorryAx, Classical.choice, Quot.sound]` to `[propext,
   Classical.choice, Quot.sound]` with **no further changes needed
   to the headline statement or its proof**. This is a clean
   "ship Phase ε, two theorems become axiom-clean" outcome
   documented in the scoping doc §7 Phase ε exit criteria.

## Suggested next approach

**For cycle 374 (Phase α executor)**: ship `inversePolynomial`
definition + 7 non-vacuity witnesses, per the scoping doc §9 entry
point.

Worker preliminaries:

1. Read cycle 358's `_inv_mk` proof at
   `Section422.lean:582–630` carefully — the `inversePolynomial`
   recursive case must mirror this formula's structure.
2. Read cycle 343's `WellFoundedRelation` instance at
   `Section301.lean:177` and `order_lt_of_mem_children` at
   `Section301.lean:167` for the termination measure pattern.
3. Read the 7 closed-form witnesses in `Section422.lean` (lines
   433, 2376, 2538, 2772, 3011, 3397, 3798) for calibration data.
4. Read `feedback_rootedtree_nested_induction.md` (memory) for the
   `mutual`-block pattern that may be needed.

Cycle 374 deliverable budget: ~80–120 LOC (recursion definition + 7
non-vacuity examples). Risk: LOW. Aristotle: not needed. The α → β
boundary is the natural one-cycle split.

**For cycle 375+ (Phase β/γ/δ/ε)**: follow the scoping doc §7's
per-phase deliverable blocks, with per-phase exit criteria and
graceful-degradation fallbacks. Each phase ships axiom-clean or
ships nothing (per the cycle 200/201 / cycle 149/150 rollback
precedents).

**Phase E sealing of `def:422B`** projected for cycle **382 or 383**
under nominal phase durations (9–10 cycles from cycle 373). The
cycle 373 scoping doc is the load-bearing prep that makes this
horizon concrete and avoids re-scoping at each phase boundary.

## Verification

- `wc -l .prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
  → 1018 lines.
- `lake env lean OpenMath/Chapter4/Section422.lean` not re-run this
  cycle (no Lean changes).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` → 5 (unchanged
  from cycles 365–372: 4 documentation references + 1 actual sorry
  at line 2279).
- Git status: 1 new file (the scoping doc); modified
  `.prover-state/heartbeat.json`, `.prover-state/history.jsonl`,
  `.prover-state/strategy.md` per harness; no other source changes.
- §422 axiom-clean streak: **38 → 39** (336–373).
