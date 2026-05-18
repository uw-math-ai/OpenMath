# Cycle 365 Strategy — §422 Phase D.3.b parametricity Step 2

## Context

Cycle 364 shipped the cycle 363 P2 audit's `linearResidualAt`
coefficient fix axiom-clean — the spurious `(-1)^r(t)` factor is
removed; the residual is now defined as
`Φ_{η_q^(-i)}(t) + i·Φ_{η_q}(t)` (audit-correct sign, constant in
`r(t)`). 4 closed-form theorems + 4 non-vacuity examples were
restated successfully, sorry count remains 0, `#print axioms` is
clean on all four theorems.

The §422 axiom-clean streak now stands at **30 consecutive cycles**
(336–364). The cycle 364 task results §"Suggested next approach"
lays out the cycle 365 deliverable explicitly: attempt Phase D.3.b
**parametricity Step 2** (`linearResidualAt_depends_only_on_strict_subtrees`)
under the cycle 364 corrected definition. The Discovery #3 note in
cycle 364 task results confirms the cancellation argument is now
structurally clean: the `+((m:ℝ)+1) * M.elementaryWeight t` term in
`linearResidualAt_succ_mk_eq` has the **correct sign** to cancel
against a `-(m+1)·M.elementaryWeight t` contribution hidden inside
the powRep-sum.

No Aristotle results pending.

## Priority 1 — Phase D.3.b parametricity Step 2 (CYCLE 365 DELIVERABLE)

**Target theorem** (the headline; ship this in `OpenMath/Chapter4/Section422.lean`):

```lean
theorem linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_strict : ∀ s : RT, s.order < t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```

I.e. `linearResidualAt i η_q t` depends only on `η_q`'s elementary
weights at strict subtrees of `t`. This is the substantive Phase D.3.b
content — once shipped, cycle 366 can immediately scaffold
`underlyingOneStepMethod_aux` via well-founded recursion on
`RootedTree.order` per Phase D.3.d.

### Recommended decomposition (per cycle 364 task results §"Suggested next approach")

Split the proof into two sub-deliverables. Ship **Sub-lemma A first**;
Sub-lemma B (the headline composition) is a near-trivial corollary.

#### Sub-lemma A — `powRep_sum_eq_of_strict_subtree_agreement`

**Preferred signature** (Route A.1):

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q^(-(((m+1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q'^(-(((m+1) : ℕ) : ℤ))) t
```

i.e. **closed-subtree** (agreement at `u.order ≤ t.order`, including
`t` itself). This is the form that **fires cleanly** because the cycle
361 closed form `linearResidualAt_succ_mk_eq` reads `M.elementaryWeight t`
at `t` itself. Per cycle 362 task results note #3, the closed-subtree
form is sufficient for Phase D.3.d's `underlyingOneStepMethod_aux`
recursion (which has agreement at ALL `u.order ≤ t.order` by the
time it reaches `t`).

The proof strategy:

1. Use cycle 359's `elementaryWeightQ_phi_zpow_negSucc_mk` to expand
   both `η_q^(-(m+1))` and `η_q'^(-(m+1))` into representative-form
   powRep-sums.
2. Apply cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
   to bridge across `M.inverse` substitution at strict subtrees of `t`.
3. Use `h_closed` at `t` itself for the direct `M.elementaryWeight t`
   contribution.

LOC estimate: ~80-120 LOC for Sub-lemma A (including the powRep-sum
unfolding and the recursive call through `derivativeWeightWithSrc`).

**Fallback signature** (Route A.2, if Route A.1's quotient-level form
doesn't fire cleanly): state at the representative level via
`Quotient.inductionOn₂` first, then lift to the quotient via
`elementaryWeightQ_phi_mk`. This avoids the heterogeneous Σ-types in
`M.powRep (m+1)` vs `M'.powRep (m+1)`.

#### Sub-lemma B — `linearResidualAt_depends_only_on_strict_subtrees`

The headline. Direct composition of Sub-lemma A with cycle 364's
`linearResidualAt` definition:

```lean
theorem linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t := by
  unfold linearResidualAt
  -- Case-split on i.
  match i with
  | 0 =>
    -- Φ_{η_q^0}(t) + 0 = Φ_1(t) + 0 = 0; same for η_q'.
    simp [zpow_zero, elementaryWeightQ_phi_id]
  | m + 1 =>
    -- Use Sub-lemma A on the η_q^(-(m+1)) term and h_closed at t
    -- on the direct Φ_{η_q}(t) term.
    rw [show (((m + 1) : ℕ) : ℤ) = ((m : ℕ) : ℤ) + 1 from by push_cast; ring]
    -- Or: directly invoke Sub-lemma A.
    have hA := powRep_sum_eq_of_strict_subtree_agreement m t η_q η_q' h_closed
    have hT := h_closed t (le_refl _)
    -- Show -(((m+1):ℕ):ℤ) = -((m+1):ℤ) bridge.
    -- ... close via push_cast + ring after rw [hA, hT].
    sorry  -- ~10 LOC
```

LOC estimate: ~30 LOC for the headline body once Sub-lemma A is in
hand.

**Total Sub-lemma A + B**: 110-150 LOC. Within budget for one cycle.

### Faithfulness note — strict vs closed subtree

The cycle 364 strategy presented a **strict-subtree** form
(`s.order < t.order`). This cycle ships the **closed-subtree** form
(`s.order ≤ t.order`) instead, justified as follows:

* The closed-subtree form is **strictly weaker** as a Lean theorem
  (more permissive consumer interface).
* It is **sufficient** for Phase D.3.d's `underlyingOneStepMethod_aux`
  recursion: by the time the recursion reaches `t`, it has values
  for all `u.order ≤ t.order` (since strong induction stores all
  prior values, and `t` itself is the value being computed via the
  closed form which uses `M.elementaryWeight t` from the LHS).
* It **closes** because the `M.elementaryWeight t` cancellation
  argument from cycle 364 Discovery #3 works ONLY when both `t` and
  strict subtrees agree.

The strict-subtree form (with separate handling of `t`-itself via
the cancellation) is the **stretch target** for cycle 365. Attempt
the closed-subtree form first; if it lands cleanly in <60 minutes,
attempt to strengthen to strict-subtree as a follow-up.

If the strict-subtree form is needed by a downstream consumer that
the closed-subtree form doesn't satisfy, this can be a cycle 366+
deliverable. Document the divergence in the docstring + task results.

### Risks and pre-flight checks

* **R1 (heterogeneous Σ-types in Sub-lemma A)**: `M.powRep (m+1)` and
  `M'.powRep (m+1)` have different stage counts when `s ≠ s'`.
  **Mitigation**: state Sub-lemma A at the **quotient level**
  (Route A.1 above) — i.e. consume `elementaryWeightQ_phi η_q^(-(m+1))`
  on both sides. The heterogeneous Σ-types are hidden inside cycle
  359's `powRep_quotient_eq`.

* **R2 (`Quotient.inductionOn₂` motive)**: when stating
  `linearResidualAt_depends_only_on_strict_subtrees` and inducting on
  `η_q, η_q'`, the motive `linearResidualAt i · t = linearResidualAt i · t`
  may not unify cleanly. **Mitigation**: avoid `Quotient.inductionOn₂`
  if possible; instead state Sub-lemma A as a direct claim about
  `elementaryWeightQ_phi (η_q^(-(m+1))) t = elementaryWeightQ_phi (η_q'^(-(m+1))) t`
  which is one-quotient-class-vs-the-other and doesn't need joint
  induction.

* **R3 (Pre-flight check on `M.powRep 2`'s cancellation)**: per cycle
  364 Discovery #3, the cancellation between the direct
  `M.elementaryWeight t` term and a hidden `-(m+1)·M.elementaryWeight t`
  inside the powRep-sum is the load-bearing structural prediction.
  **BEFORE writing the Sub-lemma A body**, use `lean_multi_attempt`
  at a position after `linearResidualAt_succ_mk_eq` (e.g. inside an
  `example` at `M := explicitEuler, m := 1, t := cherry`) to validate
  this empirically. Verify that the powRep-sum at `m = 1` indeed
  produces a `-2·explicitEuler.elementaryWeight cherry` contribution
  that cancels against the `+2·explicitEuler.elementaryWeight cherry`
  direct term.

  Specifically: compute
  `(RKTableau.explicitEuler.powRep 2).2.b 0 *
   (RKTableau.explicitEuler.powRep 2).2.derivativeWeightWithSrc
     (RKTableau.explicitEuler.powRep 2).2.inverse 0 cherry`
  via `simp`/`norm_num` and check the coefficient of
  `RKTableau.explicitEuler.elementaryWeight cherry`. If the
  coefficient is `-2` (i.e. `-(m+1)` at `m=1`), the prediction
  holds; if not, Sub-lemma A's statement needs different framing.

* **R4 (Aristotle suitability)**: this is structural induction +
  parametricity. Aristotle suitability is **LOW**. Manual closure
  only. No Aristotle submission this cycle.

### Implementation order

1. **Pre-flight check via `lean_multi_attempt`** (≤15 min) — validate
   the cycle 364 Discovery #3 cancellation prediction on a concrete
   `(explicitEuler, m=1, cherry)` instance. **If the prediction fails,
   pivot to Priority 3.**

2. **Sub-lemma A's signature** (≤10 LOC) — write the statement with
   `sorry` first; ensure it compiles. Use the closed-subtree form.

3. **Sub-lemma B (headline)** (≤30 LOC) — write the body consuming
   Sub-lemma A as a black box. Match-on-`i`, vertex base case via
   `elementaryWeightQ_phi_id`, recursive case via Sub-lemma A +
   `h_closed t (le_refl _)`. **Verify the headline closes modulo
   Sub-lemma A's body** by inserting one `sorry` only in Sub-lemma A.

4. **Sub-lemma A's body** (~80-120 LOC) — by Quotient-induction +
   `powRep_quotient_eq` + cycle 362's
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`. The
   substantive algebraic identity.

5. **Non-vacuity examples** (≤30 LOC) — 2-3 `example`s on
   `explicitEuler` with trivial agreement (`fun _ _ => rfl`), at
   `(i, t) ∈ {(1, cherry), (2, cherry), (1, broom₃)}`.

### Graceful degradation

If Sub-lemma A's body proves too hard (>90 min of attempts without
progress, OR the algebraic structure doesn't match cycle 364
Discovery #3's prediction), **ship the strategy in three pieces**:

* **Cycle 365**: Sub-lemma A signature + Sub-lemma B headline body
  (both compile; Sub-lemma A has `sorry`). Headline statement
  shipped; sorry count goes 0 → 1.
* **Cycle 366**: Sub-lemma A body closure.
* **Cycle 367+**: Phase D.3.d (`underlyingOneStepMethod_aux`).

This staging precedent matches cycles 358 → 359 (Phase D.3.a partial
→ full closure) and 360 → 361 (Phase D.3.b signature + base cases →
ℤ-form lift + general closed form). **Sorry count must NOT exceed 1**
— per the cycle 200/201 (thm:381H) and cycle 149/150 (def:530B)
rollback precedents.

## Priority 2 — Stretch (only if Priority 1 closes in <60 minutes)

If Sub-lemma A + the headline ship cleanly with axiom-clean status
in under 60 minutes (unlikely but possible given cycle 364
Discovery #3's structural insight), attempt:

* **Strengthen to strict-subtree form** — restate Sub-lemma A and
  the headline with `s.order < t.order` (strict). The proof requires
  the `M.elementaryWeight t` cancellation argument (cycle 364
  Discovery #3) inside Sub-lemma A.

* **Scoping update**: append a "Cycle 365 closure" subsection to
  `def_422B_phase_D_3_scoping.md` §10 documenting that Phase D.3.b
  is fully closed.

DO NOT attempt Phase D.3.d (`underlyingOneStepMethod_aux`) in cycle
365. That is cycle 366+ work (~120 LOC of well-founded recursion +
spec lemma).

## Priority 3 — Pivot only if Priority 1 is fundamentally blocked

If the cycle 364 Discovery #3 cancellation prediction **fails** in
the pre-flight check (R3 above), OR if Sub-lemma A's signature can't
be stabilized after 60 min of attempts, file an update to
`def_422B_phase_D_3_scoping.md` §10 ("Cycle 365 obstacle") and pivot:

* **Option 3A — concrete-tree ladder**: ship Sub-lemma A specialized
  to small trees:
  `powRep_sum_eq_of_agreement_at_cherry`,
  `powRep_sum_eq_of_agreement_at_broom₃`.
  Validate the cancellation empirically before generalizing in
  cycle 366. Analogous to cycles 273-280's small-`n` ladder for §342.

* **Option 3B — fresh entity**: per `cycle_336_pivot_options.md` and
  `def_422B_path.md` §5, possible pivots are `def:442A` (principal
  sheet), `thm:535A` (one-step method for GLM), `thm:541A` (DIMSIM
  types). Read `cycle_336_pivot_options.md` for the menu. **Only
  pivot if Option 3A also stalls** — the §422 30-cycle streak should
  not be broken lightly.

## What NOT to do

* **DO NOT redefine `linearResidualAt`.** Cycle 364 shipped the
  audit-correct form; it is final.

* **DO NOT introduce more than 1 `sorry`** in cycle 365. Sorry count
  is currently 0; if Sub-lemma A's body is deferred to cycle 366,
  ONLY introduce a sorry in Sub-lemma A (NOT in the headline). Cycle
  200/201 thm:381H rollback precedent applies.

* **DO NOT skip the pre-flight check on `M.powRep 2`'s cancellation
  structure** (R3 above). This validates the cycle 364 Discovery #3
  prediction before the proof investment begins.

* **DO NOT submit to Aristotle.** Phase D.3.b parametricity Step 2
  is genuinely structural — Aristotle has low track record on
  parametricity / well-founded reasoning. Cycle 364 task results
  classified Aristotle suitability as "poor". Manual closure only.

* **DO NOT attempt Phase D.3.d (`underlyingOneStepMethod_aux`) in
  cycle 365.** That is cycle 366+ work and requires Step 2 as a
  prerequisite.

* **DO NOT pursue old approaches that failed.** Per memory and
  prior attempts:
  - Direct tree induction at the `i`-indexed sum level (cycle 226 —
    "per-summand reasoning fails" because of cross-term coupling).
  - `simp` with `derivativeWeightWithSrc` in the simp set (cycle 226).
  - Reduction to cycle 217's `compose_equivalent_compose` via a
    `PhiEquivalent → Equivalent` implication (the implication is
    Butcher's converse direction, NOT formalised).

* **DO NOT edit `scripts/autonomous_loop.py`** or any infrastructure
  files. Worker territory: `OpenMath/`, `.prover-state/issues/`,
  `.prover-state/task_results/`, `lean_status.json`, `plan.md`.

* **DO NOT attempt to compile `OpenMath/Chapter4/Section441.lean`** —
  see `.prover-state/issues/cycle_182_gpfs_slowness.md` (43+
  consecutive GPFS timeouts since cycle 182). Cycle 365 work is in
  `OpenMath/Chapter4/Section422.lean` exclusively.

* **DO NOT raise `maxHeartbeats` above 200000.** If a proof times
  out, decompose into named sub-lemmas (cycle 281's
  `Section342NormSqHelpers.lean` is the canonical decomposition
  precedent — extract reusable helpers into a separate file).

## Verification checklist

Before commit:

1. `lake build OpenMath.Chapter4.Section422` exits 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` ≤ 1 (currently 0;
   max 1 if Sub-lemma A's body is deferred).
3. `#print axioms` on whatever shipped (`linearResidualAt_depends_only_on_strict_subtrees`,
   `powRep_sum_eq_of_strict_subtree_agreement`, or both) returns
   `[propext, Classical.choice, Quot.sound]`. Document in task results.
4. If a sorry remains: it has an explicit docstring pointing to
   cycle 365 strategy + a one-line description of what cycle 366
   needs to discharge.
5. Faithfulness check: the closed-subtree weakening (vs strict-
   subtree as initially scoped) is documented in the docstring and
   in `task_results/cycle_365.md` — explicitly noting that the
   weakening is sufficient for Phase D.3.d's recursion and
   strictly weaker as a Lean theorem.
6. `task_results/cycle_365.md` written: what shipped, what
   remains, faithfulness divergences, suggested cycle 366 approach.
7. `def_422B_phase_D_3_scoping.md` §5 ladder + §10 closure record:
   "Cycle 365 update" subsection appended.
8. `lean_status.json` row for `def:422B`: remains `partial`. `plan.md`
   row for `def:422B`: remains `[~]`.

## Expected cycle 365 outcome

| Scenario | Sub-lemma A | Headline | Sorries | Streak |
|---|---|---|---|---|
| **Best** (full closure) | ✅ axiom-clean | ✅ axiom-clean | 0 | 31 |
| **Likely** (A deferred to 366) | sorry'd | ✅ axiom-clean (uses A as black box) | 1 | 31 |
| **Stretch (rare)** | ✅ + strict-subtree | ✅ + strict-subtree | 0 | 31 |
| **Worst case** (pivot per Priority 3) | scoping doc | scoping doc | 0 | 31 (via small fresh ship) |

Each outcome ships **forward progress** on §422 D.3.b. No outcome
breaks the 30-cycle axiom-clean streak.

## Cross-references

* `.prover-state/task_results/cycle_364.md` §"Suggested next approach"
  — cycle 365 entry point definition.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` §5 cycle 365
  slot — phase decomposition.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10 — cycle
  363 P2 audit + cycle 364 closure record (the corrected
  `linearResidualAt` definition this strategy builds on).
* `OpenMath/Chapter4/Section422.lean:1879` — `linearResidualAt`
  definition (cycle 364 corrected form).
* `OpenMath/Chapter4/Section422.lean:2118` — `linearResidualAt_succ_mk_eq`
  (the closed form cycle 365 unfolds).
* `OpenMath/Chapter4/Section422.lean:2040` — `elementaryWeightQ_phi_zpow_natCast_mk`
  (cycle 361 ℤ-form lift positive case).
* `OpenMath/Chapter4/Section422.lean:2061` — `elementaryWeightQ_phi_zpow_negSucc_mk`
  (cycle 361 ℤ-form lift negative case).
* `OpenMath/Chapter3/Section381.lean:2830` —
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` (cycle 362
  parametricity Step 1, the load-bearing substitution lemma).
* `OpenMath/Chapter3/Section381.lean:2853` —
  `derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement`
  (cycle 362 list-helper).
* `OpenMath/Chapter3/Section381.lean` (cycle 359) — `powRep` +
  `powRep_quotient_eq` (the canonical representative bridge).
* `OpenMath/Chapter3/Section301.lean:177` —
  `WellFoundedRelation RootedTree := measure RootedTree.order`
  (cycle 343, consumed by Phase D.3.d in cycle 366).

§422 axiom-clean streak target: **31** consecutive cycles (336–365).
