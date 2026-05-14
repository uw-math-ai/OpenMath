# Cycle 215 Results

## Worked on

`thm:382A` (382g) form: `RKTableau.compose_equivalent_compose` in
`OpenMath/Chapter3/Section381.lean`.

Target signature (fixed-stage, per cycle 215 strategy §B):

```lean
theorem compose_equivalent_compose.{u}
    {s₁ s₂ : ℕ}
    (M₁ M₁' : RKTableau s₁) (M₂ M₂' : RKTableau s₂)
    (_hEq₁ : @Equivalent.{u} s₁ s₁ M₁ M₁')
    (_hEq₂ : @Equivalent.{u} s₂ s₂ M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁ + s₂) (M₁.compose M₂) (M₁'.compose M₂')
```

(The strategy's `M̂` notation rejected by Lean — combining circumflex
`̂` is not a valid identifier character; renamed to `M₁'`/`M₂'` per
the `Equivalent.symm`/`Equivalent.trans` convention.)

## Approach

1. Read `extraction/formalization_data/entities/thm_382A.json` for
   the (382f) textbook statement and the (382g) reformulation noted
   in Butcher's proof.
2. Read `Equivalent` definition (line 980) and `Equivalent.trans`
   (cycle 206) to confirm shapes and the `.{u}` annotation
   discipline.
3. Implemented cycle 215 strategy's route B.1 verbatim (~20 LOC
   body): destructure both equivalence hypotheses at outer `y₀`,
   take `min H₁ H₂` as the composite threshold, introduce H, apply
   cycle 214's `compose_isRKOneStep_iff.mp` to both composite
   step hypotheses to extract `y_mid` and `y_mid'`, apply hEq₁ to
   get `y_mid = y_mid'`, rewrite, then apply hEq₂.
4. **Encountered fundamental type mismatch.** The Lean error at
   line 2722 column 52:

   ```
   error: Application type mismatch: The argument
     h_M₂_step
   has type
     M₂.IsRKOneStep f y_mid' H y_final
   but is expected to have type
     M₂.IsRKOneStep f y₀ H y_final
   ```

5. Analyzed the cause: `Equivalent` is `∀ y₀, ∃ h₀, ...` —
   non-uniform. `hEq₂ f L hL y₀` produces an output-uniqueness
   statement at *that specific* y₀, requiring M₂ and M₂' to step
   from y₀. But the M₂ step in the composite (via cycle 214's
   `.mp`) fires from `y_mid'` — fundamentally a different input.
6. Tried four alternative routings (see issue file §"What was tried"):
   destructure `hEq₂` at `y_mid'` (circular threshold dependence),
   global infimum over y_mid' (potentially 0 without continuity),
   `IsRKOneStep_exists` insertion (same circularity), continuity
   argument on extracted threshold (no continuity guarantee from
   the abstract type). All four ruled out.
7. **Concluded the gap is fundamental** to the current `Equivalent`
   definition: Butcher's proof implicitly assumes uniform smallness
   (`∃ h₀, ∀ y₀, ...`), which the current type does not express.
8. Per cycle 215 strategy §H abort threshold, shipped the
   theorem as a sorry-scaffolded signature plus a comprehensive
   issue file documenting the gap and proposing the cycle 216
   resolution (refactor `Equivalent` to uniform form).
9. Added P2 paddedEuler reflexive non-vacuity `example` exercising
   the scaffolded signature.
10. Updated `lean_status.json` (thm:382A: `unformalized` →
    `partial`, cycle 215 note + lean_file/lean_symbol set),
    `plan.md` (`[ ]` → `[~]`), and `.prover-state/issues/thm_382A_path.md`
    (cycle 215 update section with proposed cycle 216 entry point
    + draft proof body that should close after the refactor).

## Result

**PARTIAL — sorry-scaffold shipped per cycle 215 §H abort threshold.**

What landed:
- `RKTableau.compose_equivalent_compose` signature in
  `OpenMath/Chapter3/Section381.lean` (immediately after cycle
  214's `compose_isRKOneStep_iff`), with `:= sorry` body.
- Docstring documents the quantifier-order gap and points to
  `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`.
- P2 paddedEuler reflexive `example` exercising the signature
  (compiles cleanly — the `sorry` doesn't block downstream
  elaboration).
- Comprehensive issue file documenting the gap (Blocker, Context,
  What was tried with four ruled-out approaches, Why Butcher's
  proof works, Three possible solutions with Option A
  recommended).
- `lean_status.json` thm:382A row updated to `partial`.
- `plan.md` thm:382A row updated to `[~]` with cycle 215 line.
- `.prover-state/issues/thm_382A_path.md` extended with the
  cycle 215 update section + cycle 216 entry point + draft
  proof body for use after the `Equivalent` refactor.

What did NOT land:
- The body of `compose_equivalent_compose` (sorry instead).
- Sorry count: 0 → 1 across the repo.

Axiom-cleanliness check:
- `compose_equivalent_compose`: axioms include `sorryAx` (expected
  — scaffolded). Axiom set: `[propext, sorryAx, Classical.choice,
  Quot.sound]`.
- `compose_isRKOneStep_iff` (cycle 214): axiom-clean
  `[propext, Classical.choice, Quot.sound]` — no regression.
- `compose_of_isRKOneStep` (cycle 213): axiom-clean
  `[propext, Classical.choice, Quot.sound]` — no regression.

Build status: `lake env lean OpenMath/Chapter3/Section381.lean`
exits clean with one `sorry` warning (compose_equivalent_compose
at line 2725:8). Warm rebuild ~6.2s (no elaboration regression).

§441 Phase C.2: GPFS-blocked (33rd consecutive smoke-test
timeout since cycle 182, ~11+ days). Skipped per strategy §A.

## Faithfulness check

For `RKTableau.compose_equivalent_compose` (new this cycle):

- **Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/thm_382A.json`)**:
  > Let m1, m2, m̂1, m̂2 denote Runge–Kutta methods, such that
  > m̂1 ≡ m1 and m̂2 ≡ m2. Then [m1·m2] = [m̂1·m̂2].
  > Equivalent form (382g): m1·m2 ≡ m̂1·m̂2.

- **Lean statement captures**: weaker (sorry-scaffolded — the
  signature is the (382g) form at fixed stage counts, but the body
  is deferred).
- **Justification for divergence**:
  - **Fixed-stage**: the textbook allows `m₁`/`m̂₁` (resp.
    `m₂`/`m̂₂`) to have different stage counts; our signature uses
    fixed `s₁`/`s₂` throughout. The heterogeneous-stage form is
    a natural cycle 217+ extension (per `thm_382A_path.md`); the
    fixed-stage form is the substantive mathematical content
    (the body's reasoning works at the abstract space N, not at
    the stage count).
  - **(382g) not (382f)**: the bracketed `[m₁·m₂] = [m̂₁·m̂₂]`
    form requires the `composeQ` lift on cycle 212's
    `Equivalent.setoidSigma` via `Quotient.lift₂` (Gap B per
    `thm_382A_path.md`); the (382g) form is Butcher's own
    reformulation in the §382A proof, so this is faithful to
    Butcher's intermediate claim.
  - **Sorry body**: blocked on a `Equivalent`-definition gap
    (non-uniform threshold), not a deficiency in the theorem
    signature. See
    `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`
    for the cycle 216 resolution path.

- **Tautology / identity / hypothesis-strength checks**: ✓
  - Conclusion `(M₁.compose M₂).Equivalent (M₁'.compose M₂')` is
    NOT a hypothesis; signature is non-tautological.
  - Proof body is `:= sorry`, not `:= h_something` (no identity
    smuggling, just a deferred body).
  - Hypotheses `_hEq₁ : M₁.Equivalent M₁'` and `_hEq₂ :
    M₂.Equivalent M₂'` are textbook-faithful (`(382f)` exactly);
    no extra strength. The `[CompleteSpace N]` typeclass binder
    is inherited via `Equivalent`'s definition (cycle 206) and
    is a no-op at every concrete call site.
  - The `_` prefix on `_hEq₁`/`_hEq₂` (Lean linter satisfies
    unused-variable warning for the sorry-scaffolded body) is
    cosmetic — the hypotheses are genuine and will be consumed
    once the body lands in cycle 216+.

For the P2 `example` exercising `compose_equivalent_compose`
on `paddedEuler`: trivial type-plumbing exercise, not a new
mathematical definition; no separate faithfulness obligation.

## Dead ends

1. **Strategy's recipe verbatim**: failed at the final `exact`
   with the type mismatch documented above.
2. **`hEq₂` destructured at `y_mid'`**: produces threshold
   `H₂(y_mid')` depending on `y_mid'`, which depends on `H` —
   circular dependency. Cannot pick the composite threshold
   ahead of `H`.
3. **Global infimum**: `inf_{y_mid'} H₂(y_mid')` can be 0
   without continuity / boundedness guarantees on the extracted
   threshold function.
4. **`IsRKOneStep_exists` insertion**: constructs a canonical
   `y_mid'(H)` but the threshold dependence on `y_mid'(H)` is
   still circular in `H`.
5. **Continuity argument**: would need continuity of the
   extracted `H₂` function, which the abstract `Equivalent` type
   does not provide.
6. **Identifier `M̂` (`M` + combining circumflex `̂`)**: Lean
   rejects combining marks in identifiers (`error: expected
   token` at the first parameter); had to rename to `M₁'`/`M₂'`
   following the existing `Equivalent.symm`/`Equivalent.trans`
   prime convention.

## Discovery

1. **`Equivalent`'s quantifier order is structurally weaker than
   Butcher's textbook treatment.** Butcher's "h sufficiently
   small" in §382A implicitly assumes uniform smallness in y₀
   (`∃ h₀, ∀ y₀, ...`), but our Lean type is `∀ y₀, ∃ h₀, ...`.
   Every concrete instance in our codebase (equivalent_self,
   symm, trans, PReducesTo.toEquivalent) produces a uniform
   threshold in practice, but the type does not expose this.
   This is the load-bearing gap blocking cycle 215's deliverable.

2. **The refactor is small and mechanical.** Changing
   `Equivalent` to uniform form moves a single `∀ y₀` binder
   inside the existential. Existing proofs port verbatim
   (~30 LOC churn): `equivalent_self`'s threshold
   `1/(2*(L*C+1))` is already y₀-independent, `symm` re-uses
   input threshold, `trans` takes min of y₀-independent
   thresholds.

3. **Combining marks are NOT valid Lean 4 identifiers.** The
   strategy used `M̂₁` (`M` + U+0302) which fails at parse time;
   identifiers must use precomposed Unicode characters or ASCII
   plus subscripts. Use prime notation (`M'`) to match the
   convention from `Equivalent.symm` and `Equivalent.trans`.

4. **Sorry-scaffold + comprehensive issue is a viable cycle
   strategy when the proof reveals a definitional gap.** Cycle
   215 lands the signature locked in, the P2 non-vacuity check
   exercised, the gap analysis written up, the cycle 216 entry
   point drafted — all without the body. This unblocks the next
   cycle with a precise, named target.

## Suggested next approach

**Cycle 216**: refactor `Equivalent` to uniform form
`∃ h₀, ∀ y₀, ...`. Specific steps documented in
`.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`
(Option A) and `.prover-state/issues/thm_382A_path.md` (Cycle 215
update → Cycle 216 entry point).

The refactor is mechanical:
1. Edit `Equivalent` definition at line ~980 of
   `OpenMath/Chapter3/Section381.lean` to move the `(y₀ : N)`
   binder inside the existential.
2. Update `equivalent_self` proof (cycle 203) — move `intro y₀`
   after `refine ⟨..., ?_⟩`.
3. Update `Equivalent.symm` proof (cycle 204) — move the `y₀`
   binder similarly.
4. Update `Equivalent.trans` proof (cycle 206) — same.
5. Update `PReducesTo.toEquivalent` and downstream consumers
   (`paddedEuler_equivalent_*`, the setoid instances at cycles
   211/212) for the new binder order.
6. Re-verify axiom-cleanliness on all updated proofs.
7. Close the cycle 215 sorry in `compose_equivalent_compose`
   using the draft body in
   `.prover-state/issues/thm_382A_path.md` (Cycle 215 update,
   Cycle 216 entry point section).
8. Update `lean_status.json` (`partial` → `formalized`),
   `plan.md` (`[~]` → `[x]`), and close the issue file.

Estimated cycle 216 LOC: ~30 LOC refactor + ~20 LOC compose body
+ ~5 LOC P2 update = ~55 LOC total. Should fit comfortably in
one cycle.

**Cycle 217+**: heterogeneous-stage form, then `composeQ` lift,
then §382 group structure — per the cycles 217/218/219 outlook
in `thm_382A_path.md`.

**§441 Phase C.2**: GPFS-blocked (33rd consecutive timeout); skip
per strategy §A. Loop-maintainer escalation pending in
`.prover-state/issues/cycle_182_gpfs_slowness.md`.
