# Cycle 222 Results

## Worked on

§382 `Group` instance on `Quotient Equivalent.setoidSigma` — the fourth
and final piece of the §382 group structure (after cycle 219's
identity, cycle 220's inverse-element absorption laws, and cycle 221's
associativity). Linear P1 → P2 → P3 → P4 execution per cycle 222
strategy §B / §I.

## Approach

Five new symbols at `OpenMath/Chapter3/Section381.lean`, ~150 LOC total:

1. **P1 — `inverse_equivalent_inverse.{u}`** (~50 LOC). The
   load-bearing well-definedness lemma allowing `RKTableau.inverse` to
   lift to the heterogeneous Σ-typed quotient
   `Quotient Equivalent.setoidSigma`. Heterogeneous-stage signature
   `{s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'} (hEq : Equivalent
   M M') : Equivalent M.inverse M'.inverse`.

   The proof uses a five-step recipe (not the cycle 220 step-inversion-
   only recipe sketched in the cycle 222 strategy §B.P1 — the
   straightforward "apply hEq at y_final after inverting both witnesses"
   approach hit a starting-point mismatch because the two inverted
   M-/M'-steps start at *different* `y_final` and `y_final'`):

   - **Step 1**: invert `h_M_inv_step : M.inverse.IsRKOneStep f y₀ h
     y_final` via cycle 220's `isRKOneStep_of_inverse_isRKOneStep` to
     obtain `M.IsRKOneStep f y_final h y₀`.
   - **Step 2**: invoke cycle 205's `IsRKOneStep_exists` on `M'` at
     `y_final` (small-`h` Banach existence) to obtain `y_alt` with
     `M'.IsRKOneStep f y_final h y_alt`. Requires the Banach smallness
     condition `|h| · L · C_M' < 1`, which we derive from `h ≤ h₀_M'
     := 1 / (2 · (L · C_M' + 1))` — recipe mirroring cycle 206's
     `Equivalent.trans`.
   - **Step 3**: apply `hEq` at `y_final` to force `y₀ = y_alt`.
   - **Step 4**: re-invert via cycle 220's
     `inverse_isRKOneStep_of_isRKOneStep` (M'-version) to obtain
     `M'.inverse.IsRKOneStep f y₀ h y_final`.
   - **Step 5**: discharge by uniqueness from `M'.inverse.equivalent_self`
     paired with the original `M'.inverse.IsRKOneStep f y₀ h y_final'`.

   Threshold: `min h₀_eq (min h₀_M'_inv h₀_M')`. The proof is
   structurally a near-identical port of `Equivalent.trans` (cycle 206)
   with the M'-existence step inserted between Banach uniqueness on
   M and the direction-reversed M'.inverse re-construction.

2. **P2 — `inverseQ.{u}`** (~12 LOC). `noncomputable def` via
   `Quotient.lift` (matching the cycle 218 `composeQ` style; the
   strategy §B.P2's `Quotient.map` form would have worked too but
   `Quotient.lift` is the more general primitive already in use).
   Respect obligation discharged by `inverse_equivalent_inverse`.

3. **P2 supporting** — `inverseQ_mk.{u}` (~5 LOC, `@[simp]` `rfl`).
   Definitional unfold for `inverseQ ⟦⟨s, M⟩⟧ = ⟦⟨s, M.inverse⟩⟧`,
   used by the `Group.ofLeftAxioms`-derived `mul_inv_cancel` and
   `inv_mul_cancel` non-vacuity examples.

4. **P2 supporting** — `composeQ_inverseQ_left.{u}` (~7 LOC). The
   pointwise lift of cycle 220's `composeQ_inverse_left M` to all
   quotient classes via `Quotient.inductionOn`. Used as the
   `inv_mul_cancel` field of `Group.ofLeftAxioms`.

5. **P3 — `Group` instance** (~25 LOC). `Mul`, `Inv`, `One` typeclass
   instances bound to `composeQ`, `inverseQ`,
   `⟦⟨0, RKTableau.id⟩⟧`, then `Group` instance via Mathlib's
   `Group.ofLeftAxioms` (the cleaner minimal-axiom abbrev needing only
   `mul_assoc` + `one_mul` + `inv_mul_cancel`; right-side axioms
   auto-derived). Required adding
   `import Mathlib.Algebra.Group.MinimalAxioms` to Section381.lean.

6. **P4 non-vacuity** — five examples covering:
   (a) homogeneous `inverse_equivalent_inverse` on `paddedEuler`;
   (b) heterogeneous `inverse_equivalent_inverse` `paddedEuler` ↔
       `paddedEuler.pReduced pairPartition` (genuinely-distinct stage
       counts 2 vs 1, the relevant test) via cycle 208's
       `paddedEuler_equivalent_pReduced`;
   (c) `inverseQ_mk` by `rfl`;
   (d) `mul_inv_cancel` via the typeclass on `⟦⟨2, paddedEuler⟩⟧`;
   (e) `inv_mul_cancel` (the defining `Group.ofLeftAxioms` axiom)
       via the typeclass on `⟦⟨2, paddedEuler⟩⟧`.

## Result

SUCCESS — all four priorities P1, P2, P3, P4 shipped axiom-clean on
first compile. `lake env lean OpenMath/Chapter3/Section381.lean`
finishes in 9.657s warm rebuild (34 consecutive cycles of stable §381
health since cycle 184 GPFS recovery). Sorry count remains 0.

§A GPFS smoke test on Section441: 39th consecutive timeout (EXIT=124
after 300s, near-zero CPU). Logged at 2026-05-14 11:18 UTC in
`.prover-state/issues/cycle_182_gpfs_slowness.md`. Skipping Phase C.2
per the established pattern.

## Faithfulness check

The four-axiom `Group` instance is supplementary infrastructure for
the future §383 group-homomorphism work (`PhiEquivalent.toGroupHom`,
`lem:383A` *The Runge–Kutta group*); it is not itself a direct
textbook entity in Butcher's numbering. But it expresses Butcher
§382's "the equivalence classes of Runge–Kutta methods form a group
under composition" conclusion in machine-readable form, completing
the four-axiom story started in cycles 219/220/221.

For each new `def` or `theorem` introduced this cycle:

### `inverse_equivalent_inverse`
- Entity ID: not a direct textbook entity. Implements the
  well-definedness obligation for the §382 group's `Inv` operation
  on `Quotient Equivalent.setoidSigma`.
- Textbook statement: Butcher §382 p. 307 only states the group
  *exists* — well-definedness of operations is implicit.
- Lean statement captures: same content as the implicit obligation.
  Heterogeneous-stage signature matches the cycle 216 uniform-
  threshold refactor convention.
- Tautology check: NO. The conclusion involves `M.inverse`/`M'.inverse`
  (different terms from the hypothesis's `M`/`M'`).
- Identity check: NO. The proof routes through `IsRKOneStep_exists`,
  `equivalent_self`, and cycle 220's step-inversion lemmas — real
  mathematical work.
- Hypothesis strength: matches the cycle 216 `Equivalent` definition
  exactly. No extra hypotheses.

### `inverseQ`, `inverseQ_mk`
- Implements §382's inverse operation at the quotient level. The
  definition is forced by the textbook's "inverse method" construction
  (cycle 220's `RKTableau.inverse`) lifted through the quotient.
- `inverseQ_mk` is the definitional unfold (by `rfl`), making the
  `Quotient.lift` reduction visible to `simp`. Not a smuggled
  theorem — it's a documented `rfl`.

### `composeQ_inverseQ_left`
- Direct pointwise lift of cycle 220's `composeQ_inverse_left` from
  the specific representative `⟦⟨s, M⟩⟧` to all quotient classes via
  `Quotient.inductionOn`. The `composeQ_inverse_right` analogue
  isn't lifted here because Mathlib's `Group.ofLeftAxioms` only needs
  the left form; `mul_inv_cancel` derives automatically.

### `Group` instance
- Implements the typeclass form of Butcher §382's group conclusion.
  `Group.ofLeftAxioms` is a Mathlib `abbrev`; the three input axioms
  (`composeQ_assoc`, `composeQ_id_left`, `composeQ_inverseQ_left`)
  are direct citations of cycles 221, 219, 222 (this cycle) results.
  The right-side axioms `mul_one` and `mul_inv_cancel` are
  *derived* by Mathlib from the three left axioms (see
  `Group.ofLeftAxioms`'s body: it provides a `Group` instance by
  proving `mul_one` from the left axioms via a five-line `calc`
  chain).
  No definition smuggling: the four-axiom Group is what Butcher's
  §382 actually proves; we cite exactly those theorems we have.

## Dead ends

**Initial attempted approach to P1** — the strategy §B.P1 sketch
suggested "apply hEq_app to force the two M/M' witnesses (at whichever
y-arguments they emerge after step-inversion) to agree." This does
*not* directly work because after `isRKOneStep_of_inverse_isRKOneStep`,
the M-step starts at `y_final` and the M'-step starts at `y_final'`
— different starting points, so hEq can't be applied with a single
common starting `y₀`. Recovered by inserting the cycle 205
`IsRKOneStep_exists` Banach-existence call on M' at `y_final` to
provide a M'-witness with the same starting point as the M-witness,
mirroring cycle 206's `Equivalent.trans` recipe (which uses
`IsRKOneStep_exists` on M' for the middle witness).

**Missing import** — first compile failed with `unknown constant
'Group.ofLeftAxioms'`. Fix: add `import
Mathlib.Algebra.Group.MinimalAxioms` to the Section381.lean preamble.
Recompile clean on second attempt.

No other dead ends. All eight pre-flagged risks R1–R8 from strategy
§B / §I (step-inversion signature drift, sign of `H`, heterogeneous
stages, `.{u}` annotations, `Quotient.map` API, Σ-projection naming,
`Group` field naming, cycle 220 symbol naming) did NOT fire — every
inferred signature, every type, every dot-syntax call worked on first
attempt after the missing-import fix.

## Discovery

1. **`Group.ofLeftAxioms`** (Mathlib's `Mathlib.Algebra.Group.MinimalAxioms`)
   is the right primitive for assembling a `Group` instance on a
   quotient type from three left axioms. It takes `Mul`/`Inv`/`One`
   instances + `mul_assoc` + `one_mul` + `inv_mul_cancel` as
   parameters, and auto-derives `mul_one` + `mul_inv_cancel` via a
   five-line `calc` chain on the left axioms. Much cleaner than
   binding the full `Group` record's six+ fields (some of which
   would need awkward npow/zpow/div defaults).

2. **`IsRKOneStep_exists` is the natural injection point** for
   adapting `Equivalent.trans`'s recipe to other binary-relations-on-
   `Equivalent` infrastructure. Whenever a proof needs to compare
   `M.IsRKOneStep` (from `y_A`) and `M'.IsRKOneStep` (from `y_B`)
   with `y_A ≠ y_B` provided, the trick is to use Banach existence
   on M' at `y_A` to manufacture a M'-witness with starting point
   `y_A`, then apply `hEq` at `y_A`. The cost is one `min` extension
   of the threshold to include `h₀_M' := 1 / (2 · (L · C_M' + 1))`.

3. **`Quotient.lift` vs `Quotient.map`** for single-argument quotient
   functions: both work. The strategy §B.P2 suggested `Quotient.map`,
   but `Quotient.lift` with explicit `Quotient.mk` in the body
   (matching the cycle 218 `composeQ` style) is equally clean and
   keeps the codebase visually consistent.

4. **Five non-vacuity examples is the right granularity** for a
   four-axiom typeclass instance. Two `Equivalent`-level examples
   (homogeneous + heterogeneous) exercise the load-bearing lemma; one
   `rfl` example confirms the quotient lift unfolds definitionally;
   two typeclass-level examples (`mul_inv_cancel` and `inv_mul_cancel`)
   confirm the `Group.ofLeftAxioms` field bindings are correct.

## Suggested next approach

**Cycle 223 — §383 group homomorphism path.** With the §382 `Group`
instance in hand, the immediate next pivot is the §383 path:

1. **`lem:383A` — *The Runge–Kutta group* (§383)** is already
   `[x]` formalized in `plan.md` (it's a pre-§382 cycle line). Check
   whether the cycle-222 `Group` instance now allows tightening
   `lem:383A`'s statement (e.g. expressing it directly as the new
   `instGroup`).

2. **`PhiEquivalent.toGroupHom`** — the structural bridge from
   cycle 187/193's `PReducesTo.toPhiEquivalent` to a `GroupHom` on
   the §382 group. This is the cycle 223 P1 candidate per
   `.prover-state/issues/thm_382A_path.md`'s cycle 217+ outlook.

3. **Alternative pivot** — `thm:381G` (Irreducible RK Stage
   Distinguishability) or `thm:381H` (RK Equivalence Conditions),
   the two remaining `[ ]` Ch.3 §380 textbook entities, would benefit
   from the §382 group structure being available downstream (per
   `.prover-state/issues/thm_381H_deferred.md`).

**§441 Phase C.2 GPFS-blocked (39 consecutive timeouts).** Skip per
established pattern; revisit only when smoke test passes cleanly.
