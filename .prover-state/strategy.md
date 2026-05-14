# Cycle 230 Strategy

## Status snapshot

- Sorry count: **0** (43rd consecutive clean cycle since cycle 201
  rollback). Do not regress this.
- Branch tip: `3d4b71b` (cycle 229 — right-identity laws for the
  one-sided §383 partial action).
- Aristotle right-action job
  `176aa964-db7b-40f8-a01c-05247c186ec5`: IN_PROGRESS at **17 %**
  as of cycle 229 single-poll. Growth rate ≈ 2–3 % per cycle
  (9 % → 11 % → 17 % across cycles 227–229). Several-day ETA at
  this rate.
- §441 Phase C.2: GPFS-blocked since cycle 182. **44th
  consecutive cycle of being skipped** — do not attempt.
- §383 group-homomorphism path Phase 3 ledger:
  - Cycle 224 — top-block `derivativeWeight_compose_castAdd` (mutual)
  - Cycle 225 — bottom-block `derivativeWeight_compose_natAdd` +
    `derivativeWeightWithSrc` / `derivativeWeightWithSrcProd` defs
  - Cycle 226 — `derivativeWeightWithSrc_subst_M₁` (M₁-substitution)
    + `compose_elementaryWeight_decomp` +
    `compose_phiEquivalent_compose_left` (left-action only)
  - Cycle 227 — `composeQ_phi_left_act` (one-sided `Quotient.lift`)
  - Cycle 228 — left-identity laws (`id_elementaryWeight`,
    `id_compose_phiEquivalent`, `composeQ_phi_left_act_id_left`)
  - Cycle 229 — right-identity laws (`compose_id_phiEquivalent`,
    `composeQ_phi_left_act_id_right`)
  - **Open**: right-action (`compose_phiEquivalent_compose_right` /
    full binary `compose_phiEquivalent_compose`) — gated on the
    M₂-side sum equality. Issue:
    `.prover-state/issues/cycle_226_compose_phi_right_action.md`.

## §A — §441 Phase C.2

**SKIP.** 44th consecutive cycle. Do not run any local Section441
smoke test. Do not try to apply the cycle 182 draft. The pathology
is well-documented and the cluster has not recovered. Cycle 229's
warm rebuild was 6.2 s on Section381, confirming the GPFS issue is
specific to Section441's transitive Mathlib.Analysis.* load.

## §B — Priority 0: single Aristotle poll (mandatory, do this first)

Run **exactly one** poll on project
`176aa964-db7b-40f8-a01c-05247c186ec5`. Use the
`mcp__aristotle__get_status` tool. Per CLAUDE.md, do NOT re-poll
in the same cycle; the single-poll discipline is enforced across
cycles 227 / 228 / 229.

Three possible outcomes:

1. **`COMPLETE`** (proof returned) → branch to §C (path A: ship full
   binary `composeQ_phi`).
2. **`COMPLETE_WITH_ERRORS`** → extract the relevant diff, apply it
   locally, then attempt §C. If errors look superficial (namespace
   resolution, missing import) and the proof body is otherwise
   sound, this still routes to path A. If the proof is unsalvageable
   ⇒ branch to §D (path B).
3. **`IN_PROGRESS` / `FAILED` / `CANCELLED`** → branch to §D (path
   B: ship one half of `derivativeWeightWithSrc_compose` mutual
   pair as infrastructure for cycle 231's
   `compose_assoc_phiEquivalent`).

## §C — Path A: Aristotle returned (full binary right-action)

If Aristotle gives a clean (or near-clean) proof of the M₂-side sum
equality, the cycle's deliverables are:

### C.1 Ship `compose_phiEquivalent_compose_right`

The M₂-side mirror of cycle 226's left-action. Statement:

```lean
theorem compose_phiEquivalent_compose_right {s₁ s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁.compose M₂')
```

Body: incorporate the Aristotle proof. The shape will route through
`compose_elementaryWeight_decomp` (cycle 225) on both sides, then
discharge the M₂-side bottom-block sum equality
`∑ i, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t =
 ∑ i', M₂'.b i' * M₂'.derivativeWeightWithSrc M₁ i' t` via whatever
mechanism Aristotle produced.

Place it immediately after cycle 226's
`compose_phiEquivalent_compose_left` (currently at
`OpenMath/Chapter3/Section381.lean:2860`).

### C.2 Ship the full binary `compose_phiEquivalent_compose`

```lean
theorem compose_phiEquivalent_compose
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₁ : PhiEquivalent M₁ M₁') (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂') :=
  (compose_phiEquivalent_compose_left M₂ hPhi₁).trans
    (compose_phiEquivalent_compose_right M₁' hPhi₂)
```

(Uses `PhiEquivalent.trans` to compose left and right legs through
the middle `M₁'.compose M₂`.)

### C.3 Promote `composeQ_phi_left_act` to full binary `composeQ_phi`

Replace cycle 227's one-sided `Quotient.lift` with a `Quotient.lift₂`.
Mirror cycle 218's `composeQ` template (search Section381.lean for
`composeQ_eq_of_equivalent` and the `composeQ` def just above it):

```lean
noncomputable def composeQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma :=
  Quotient.lift₂
    (fun p q => Quotient.mk PhiEquivalent.setoidSigma
                  ⟨p.1 + q.1, p.2.compose q.2⟩)
    (by
      rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩ ⟨s₂', M₂'⟩ hPhi₁ hPhi₂
      apply Quotient.sound
      show @PhiEquivalent (s₁ + s₂) (s₁' + s₂') _ _
      exact compose_phiEquivalent_compose hPhi₁ hPhi₂)
```

Cycle 227's one-sided `composeQ_phi_left_act` may be retained as
a corollary (or retired; the planner of cycle 231 can decide).

### C.4 Ship the bracketed (formal §383 textbook) corollary

```lean
theorem composeQ_phi_eq_of_phiEquivalent
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₁ : PhiEquivalent M₁ M₁') (hPhi₂ : PhiEquivalent M₂ M₂') :
    composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
                 (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩)
      = composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁', M₁'⟩)
                     (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂', M₂'⟩) :=
  Quotient.sound (compose_phiEquivalent_compose hPhi₁ hPhi₂)
```

This is the §383 analog of cycle 218's `composeQ_eq_of_equivalent`
and closes the "[m₁·m₂] = [m̂₁·m̂₂] on PhiEquivalent classes"
half of `thm:384A`'s underlying identification.

### C.5 Promote cycles 228 / 229's identity laws

Cycles 228 / 229 shipped `composeQ_phi_left_act_id_left` and
`composeQ_phi_left_act_id_right` on the **one-sided** action.
With the full binary `composeQ_phi` now available, ship the
two-sided versions:

```lean
theorem composeQ_phi_id_left (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩) q = q
theorem composeQ_phi_id_right (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi q (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩) = q
```

Bodies: `Quotient.inductionOn q` + `Quotient.sound` consuming
`id_compose_phiEquivalent` (cycle 228) / `compose_id_phiEquivalent`
(cycle 229). Both are one-liner reskins of cycles 228 / 229.

### C.6 Non-vacuity (P2)

Two `example`s in `namespace OpenMath.Chapter3.Section381` at the
file's end:
- `composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
   (Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
   = Quotient.mk PhiEquivalent.setoidSigma ⟨4, paddedEuler.compose paddedEuler⟩`
  by `rfl` through `Quotient.lift₂_mk`.
- Heterogeneous-stage witness using `pReduced_phiEquivalent` on both
  sides via cycle 187's
  `paddedEuler_isPReducibleVia_pairPartition` — exercises both
  arguments through PhiEquivalent simultaneously.

Use explicit `Quotient.mk PhiEquivalent.setoidSigma` syntax (NOT
`⟦...⟧`) per the cycle 227 discovery D2 about ambiguous Σ-typed
`⟦...⟧` notation (both `Equivalent.setoidSigma` and
`PhiEquivalent.setoidSigma` are registered).

### C.7 Bookkeeping
- Update `lean_status.json`: `thm:384A` row from `partial` to
  `formalized` IF the §383 group structure can be assembled in this
  cycle; otherwise leave `partial` and bump the cycle reference.
  (Likely leave as `partial` — the homomorphism Φ itself is a
  cycle 231+ deliverable that consumes `composeQ_phi`.)
- Update `plan.md`'s `thm:384A` row with the cycle 230 outcome.
- Resolve / close
  `.prover-state/issues/cycle_226_compose_phi_right_action.md`
  by appending a cycle 230 resolution note.

### C.8 Stretch (only if §C.1–C.6 finish with budget remaining)
Begin the §383 `Group` instance on
`Quotient PhiEquivalent.setoidSigma` by porting cycle 221's
`composeQ_assoc` recipe: ship `compose_assoc_phiEquivalent` at the
`PhiEquivalent` level. This will likely need cycle 230 path-B
infrastructure (top-block + bottom-block
`derivativeWeightWithSrc_compose_*` lemmas) — if path B has not yet
been shipped, defer this stretch.

## §D — Path B: Aristotle still running (build cycle 231 infrastructure)

If the Aristotle job has not returned, do NOT attempt the right-
action via direct tree induction (per cycle 226 dead end record:
direct tree induction does NOT close because the inner `A`-recursion
couples outer `b`-weighting in a non-factorable cross-term). The
issue
`.prover-state/issues/cycle_226_compose_phi_right_action.md`
documents three other ruled-out routes (decomposition re-application,
reduction to cycle 217's operational `compose_equivalent_compose`,
and PhiEquivalent → Equivalent without B-series machinery).

Instead, ship the **top-block half** of the
`derivativeWeightWithSrc_compose` unfolding. This is concrete,
self-contained, axiom-clean expected, and unblocks cycle 231 +
cycle 232's `compose_assoc_phiEquivalent` (Phase 3 follow-up
building toward the §383 `Group` instance).

### D.1 Ship `derivativeWeightWithSrc_compose_castAdd` mutual block

Add a new mutual block to `OpenMath/Chapter3/Section381.lean`,
placed **after** cycle 226's `compose_phiEquivalent_compose_left`
(currently at line ~2860) and **before** cycle 227's
`composeQ_phi_left_act` (which is the natural source-order home for
all `derivativeWeightWithSrc_compose_*` lemmas). The block defines
TWO private mutual theorems:

```lean
section
open OpenMath.Chapter3.Section310

mutual
  /-- *Top-block derivative-weight-with-source reduction.* For a
  stage `castAdd s₃ j` in the top block of `M₂.compose M₃`, the
  composite derivative-weight-with-source on `M₁` equals
  `M₂`'s derivative-weight-with-source on `M₁` at stage `j`. The
  bottom block of `M₂.compose M₃` does not contribute (because
  `compose_A_topRight = 0`). Companion to
  `derivativeWeightWithSrcProd_compose_castAdd`. -/
  private theorem derivativeWeightWithSrc_compose_castAdd
      {s₁ s₂ s₃ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
      ∀ (t : RootedTree) (j : Fin s₂),
        (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.castAdd s₃ j) t
          = M₂.derivativeWeightWithSrc M₁ j t
    | RootedTree.mk children, j => by
        show (M₂.compose M₃).derivativeWeightWithSrcProd M₁
                (Fin.castAdd s₃ j) children
            = M₂.derivativeWeightWithSrcProd M₁ j children
        exact derivativeWeightWithSrcProd_compose_castAdd
                M₁ M₂ M₃ children j

  /-- List-helper companion to
  `derivativeWeightWithSrc_compose_castAdd`. -/
  private theorem derivativeWeightWithSrcProd_compose_castAdd
      {s₁ s₂ s₃ : ℕ}
      (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
      ∀ (children : List RootedTree) (j : Fin s₂),
        (M₂.compose M₃).derivativeWeightWithSrcProd M₁
            (Fin.castAdd s₃ j) children
          = M₂.derivativeWeightWithSrcProd M₁ j children
    | [], _ => rfl
    | t :: ts, j => by
        show ((M₁.elementaryWeight t
                + ∑ k : Fin (s₂ + s₃),
                    (M₂.compose M₃).A (Fin.castAdd s₃ j) k
                      * (M₂.compose M₃).derivativeWeightWithSrc M₁ k t)
              * (M₂.compose M₃).derivativeWeightWithSrcProd M₁
                  (Fin.castAdd s₃ j) ts)
            = (M₁.elementaryWeight t
                + ∑ j' : Fin s₂,
                    M₂.A j j' * M₂.derivativeWeightWithSrc M₁ j' t)
              * M₂.derivativeWeightWithSrcProd M₁ j ts
        rw [derivativeWeightWithSrcProd_compose_castAdd M₁ M₂ M₃ ts j]
        congr 1
        rw [Fin.sum_univ_add]
        simp only [compose_A_topLeft, compose_A_topRight,
                   zero_mul, Finset.sum_const_zero, add_zero]
        congr 1
        exact Finset.sum_congr rfl (fun j' _ => by
          rw [derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j'])
end

end
```

**Proof recipe summary**. At each cons cell `t :: ts`:
1. Use IH on the tail to reduce the recursive-on-`ts` factor.
2. `Fin.sum_univ_add` splits the `Fin (s₂ + s₃)` sum into top
   (`castAdd s₃ j'`) and bottom (`natAdd s₂ k`) blocks.
3. `simp only [compose_A_topLeft, compose_A_topRight, zero_mul,
   Finset.sum_const_zero, add_zero]` collapses the bottom-block
   summands to `0 * _` via `compose_A_topRight = 0`, which then
   `zero_mul` / `Finset.sum_const_zero` / `add_zero` eliminate.
4. The top-block `compose_A_topLeft` rewrites
   `(M₂.compose M₃).A (castAdd s₃ j) (castAdd s₃ j') = M₂.A j j'`.
5. `Finset.sum_congr` + the per-summand IH on `t` (i.e.
   `derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j'`) closes
   the inner sum.

This is structurally **identical** to cycle 224's
`derivativeWeight_compose_castAdd` proof, only with
`derivativeWeightWithSrc M₁` substituted for `derivativeWeight`.
See cycle 224's body at `OpenMath/Chapter3/Section381.lean:~2604–2654`
for the verbatim template (search for
`derivativeWeightProd_compose_castAdd` in the source). Do not invent
new tactics.

If Lean's structural-recursion checker complains, add
`decreasing_by exact?` annotations with the same shape as cycles
224 / 225 — but cycles 224 / 225 / 226 / 228 all elaborated without
explicit `decreasing_by`, so expect this is unnecessary.

### D.2 Non-vacuity witness on `paddedEuler`

In `namespace OpenMath.Chapter3.Section381` near the file's end
(after cycle 225's `paddedEuler_derivativeWeight_compose_natAdd`
example at ~line 3870), add:

```lean
example (t : RootedTree) (j : Fin 2) :
    (paddedEuler.compose paddedEuler).derivativeWeightWithSrc
        paddedEuler (Fin.castAdd 2 j) t
      = paddedEuler.derivativeWeightWithSrc paddedEuler j t :=
  derivativeWeightWithSrc_compose_castAdd
    paddedEuler paddedEuler paddedEuler t j
```

(Three-factor compose witness at `s₁ = s₂ = s₃ = 2`, mirroring
cycle 225's two-factor non-vacuity but exercising the new
three-method dependency on `M₁`, `M₂`, `M₃`.)

### D.3 Bookkeeping (path B)
- `lean_status.json`: no `thm:384A` change this cycle (right-action
  still gated; partial status preserved).
- `plan.md`: append a cycle 230 line on `thm:384A`'s row noting the
  top-block `derivativeWeightWithSrc_compose_castAdd` infrastructure.
- Issue
  `.prover-state/issues/cycle_226_compose_phi_right_action.md`:
  append a cycle 230 update noting that path B was taken and
  documenting the cycle 231 outlook (ship bottom-block partner via
  cycle 225's algebraic recipe + cycle 230 top-block + cycle 225
  `compose_elementaryWeight_decomp`; then cycle 232 assembles
  `compose_assoc_phiEquivalent`).

### D.4 Cycle 231 outlook (preview, for the next planner)

The bottom-block partner

```lean
private theorem derivativeWeightWithSrc_compose_natAdd
    {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    ∀ (t : RootedTree) (k : Fin s₃),
      (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
        = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t
```

will close via the cycle 230 top-block lemma + cycle 225's
`compose_elementaryWeight_decomp` (applied to push
`(M₁.compose M₂).elementaryWeight` inside the RHS) + the standard
`Fin.sum_univ_add` block split on
`compose_A_botLeft = M₂.b j` / `compose_A_botRight = M₃.A k k'`.
The cross-term `∑ j, M₂.b j * (M₂.compose M₃).derivativeWeightWithSrc
M₁ (castAdd s₃ j) c` then collapses via cycle 230's lemma to
`∑ j, M₂.b j * M₂.derivativeWeightWithSrc M₁ j c`, which is exactly
the second term of `compose_elementaryWeight_decomp M₁ M₂ c`. Once
both halves land, cycle 232 ships `compose_assoc_phiEquivalent`
(three-factor associativity at the PhiEquivalent level), mirroring
cycle 221's `compose_equivalent_compose_assoc` at the §382 level.

## §E — What NOT to try

Cycle 226 explicitly ruled out the following routes for the
M₂-side right-action. Do **not** repeat:

1. **Direct tree induction on `t`** for the right-action M₂-side sum
   equality. The `t :: ts` expansion produces a cross-term
   `∑ i,j, M₂.b i * M₂.A i j * M₂.derivativeWeightWithSrc M₁ j c
   * M₂.derivativeWeightWithSrcProd M₁ i ts` that does not factor
   into a sum the IH can consume; per-summand reasoning fails.
2. **Re-applying `compose_elementaryWeight_decomp`** to the M₂-side
   sum equality. This restates the same claim and is circular.
3. **Reducing to cycle 217's operational `compose_equivalent_compose`**
   via a hypothetical `PhiEquivalent → Equivalent` implication. That
   implication is Butcher's converse direction (§380) — multi-cycle
   B-series / Taylor expansion infrastructure, not yet formalised.

Cycle 226's task results §"Dead ends" enumerates these explicitly.

Additionally:
- Do **not** modify `scripts/autonomous_loop.py` (loop-maintainer
  territory).
- Do **not** raise `maxHeartbeats` above 200 000.
- Do **not** introduce `axiom` declarations.
- Do **not** attempt a Section441.lean smoke test (45th consecutive
  skip — GPFS pathology unresolved).
- Do **not** re-poll the Aristotle right-action job within the same
  cycle.
- Do **not** use `⟦...⟧` notation on `Σ s, RKTableau s` — both
  setoid instances (`Equivalent.setoidSigma` and
  `PhiEquivalent.setoidSigma`) are registered and the notation is
  ambiguous. Use explicit `Quotient.mk PhiEquivalent.setoidSigma`
  per cycle 227 discovery D2.

## §F — Pre-flight risk register

- **R1 (path B `decreasing_by` annotations)**: cycles 224 / 225's
  mutual blocks worked WITHOUT explicit `decreasing_by` clauses
  because Lean's structural-recursion checker handled `RootedTree`
  + `List RootedTree` mutuals automatically. Cycle 230 path B uses
  the identical structural pattern — expect no `decreasing_by`
  needed. If Lean complains, add `decreasing_by` with the same
  measure as `derivativeWeight_pReduced` (cycle 187 template at
  `Section312.lean:91–106`).
- **R2 (namespace scoping for `RootedTree`)**: the mutual block
  must live inside a `section ... open OpenMath.Chapter3.Section310
  ... end` wrapper, identical to cycles 224 / 225 / 226 at lines
  ~2670, 2750, 2762. Unqualified `RootedTree` inside the
  `RKTableau` namespace would resolve to the wrong type.
- **R3 (warm rebuild time)**: cycle 229 was 6.2 s warm. Expect
  cycle 230 path B at ~12–20 s (one new mutual block) or path A at
  ~10–15 s (one new theorem + one Quotient.lift₂ def + three
  corollaries + two examples). If a single compile takes more than
  **60 s** warm (red flag — §F.5 threshold from prior cycles is
  30 s), investigate before continuing.
- **R4 (path A respect-obligation universe annotations)**: cycle
  218's `composeQ_eq_of_equivalent` required an explicit
  `show @Equivalent.{u} ...` to stabilise the goal before the
  final `exact`. Path A's analogous `composeQ_phi_eq_of_phiEquivalent`
  will likely need
  `show @PhiEquivalent (s₁ + s₂) (s₁' + s₂') _ _` similarly. Do
  not skip this.
- **R5 (path A `Quotient.lift₂_mk` reduction)**: cycle 218's
  homogeneous non-vacuity example closed by plain `rfl` through
  `Quotient.lift₂_mk` definitional reduction. Expect the same for
  §C.6 path A non-vacuity examples — no `rw [...]` or `simp`
  needed for the homogeneous case.
- **R6 (path B `compose_A_topLeft` / `topRight` shape)**: cycle 224's
  proof used `simp only [compose_A_topLeft, compose_A_topRight,
  zero_mul, Finset.sum_const_zero, add_zero]` for the bottom-block
  collapse. Path B's `derivativeWeightWithSrcProd_compose_castAdd`
  uses the identical simp set — verify by reading cycle 224 verbatim
  at `Section381.lean:~2645` before authoring.

## §G — Faithfulness checklist (mandatory before commit)

Run through the CLAUDE.md Pre-Commit Faithfulness Checklist for
every new `theorem` / `def`:

- **Tautology check**: does any new theorem's conclusion appear
  verbatim as one of its hypotheses? (Should be NO for everything
  in §C and §D.)
- **Identity check**: any new theorem proved by `exact h`? Only
  the `compose_phiEquivalent_compose` definition in §C.2 is a
  one-line definition via `.trans`, which is genuine composition
  (not identity).
- **Hypothesis strength**: any hypothesis stronger than needed?
  For path A, the new `compose_phiEquivalent_compose` takes only
  the two `hPhi₁, hPhi₂` — minimal. For path B, the new mutual
  block takes only the three tableaux — minimal.
- **Definition smuggling**: not applicable (no new `def`s in
  path B; path A's `composeQ_phi` is a `Quotient.lift₂` of a
  ground-level composition, faithful to the textbook §383 "..as
  a group" construction).

Verify axiom-cleanliness via `lean_verify` on every new public
theorem; expected axiom set is `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`, no new well-founded recursion axioms).

## §H — Decision tree

```
Step 1: mcp__aristotle__get_status on 176aa964-... (SINGLE poll)
        |
        +-- COMPLETE / COMPLETE_WITH_ERRORS (salvageable)
        |   --> Path A (§C):
        |       1. Incorporate proof of compose_phiEquivalent_compose_right
        |       2. Ship compose_phiEquivalent_compose (trans of left+right)
        |       3. Promote composeQ_phi_left_act to composeQ_phi (Quotient.lift₂)
        |       4. Ship composeQ_phi_eq_of_phiEquivalent + identity laws
        |       5. Non-vacuity examples (homog + heterog)
        |       6. Update lean_status.json + plan.md + close issue
        |       7. (Stretch) begin compose_assoc_phiEquivalent if budget
        |
        +-- IN_PROGRESS / FAILED / CANCELLED / unsalvageable errors
            --> Path B (§D):
                1. Ship derivativeWeightWithSrc_compose_castAdd mutual block
                2. Non-vacuity example on paddedEuler (s = 2,2,2 three-factor)
                3. Update plan.md + append cycle 230 update to issue
                4. Cycle 231 outlook: bottom-block partner +
                   compose_assoc_phiEquivalent assembly
```

## §I — Commit message templates

For path A:
```
Cycle 230 — §383 group-hom path Phase 3 follow-up: right-action SHIPPED
via Aristotle proof; full binary composeQ_phi + bracketed thm:384A
identification + two-sided identity laws all axiom-clean.
```

For path B:
```
Cycle 230 — §383 group-hom path Phase 3 follow-up:
derivativeWeightWithSrc_compose_castAdd (top-block mutual partner)
SHIPPED axiom-clean. Aristotle right-action job still IN_PROGRESS at <X>%.
Cycle 231 ships bottom-block partner; cycle 232 assembles
compose_assoc_phiEquivalent.
```

Either way, include the cycle's full task-results summary in
`.prover-state/task_results/cycle_230.md` per CLAUDE.md format.
