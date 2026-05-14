# Strategy — Cycle 221

## §A — Filesystem health pre-check (Priority 0)

Smoke-test §441 first to record the GPFS state. **Do NOT spend more
than 5 minutes here.**

```bash
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

- **If it completes in <120s** (GPFS recovered after 37+ cycles of
  outage): pivot to Phase C.2 per `lem_441A_phase_C_scoping.md`. Use
  the preserved draft at
  `.prover-state/cycle_182_draft_section441.lean` plus the cycle 184
  namespace fix on line 1529
  (`M.αPoly_complex_root_norm_ge_one_of_stable` →
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M`).
  Skip §B–§F below; that branch has its own plan in the issue file.
- **If it times out at 300s** (38th consecutive — most likely): the
  GPFS pathology persists. Execute §B–§F below (§382 group
  associativity). Document the 38th timeout in
  `cycle_182_gpfs_slowness.md` and continue.

## §B — Substantive deliverable: §382 associativity at the Equivalent level

**Target**: `RKTableau.compose_equivalent_compose_assoc` —
heterogeneous-stage associativity for `compose` at the `Equivalent`
level. This is the third of the four §382 group axioms (after
identity in cycle 219 and inverse in cycle 220) and is the
**finesse for cycle 210's deferred `compose_assoc` HEq blocker** per
`.prover-state/issues/compose_assoc_HEq_plumbing.md`:

> Cycle 219 update: the on-the-nose `compose_assoc` HEq plumbing
> blocker is **finessable** through `Quotient.sound` once an
> `Equivalent`-level associativity is in hand — the stage-count
> Σ-projection lives inside the representative, not in the output type.

Target signature (P1):

```lean
theorem compose_equivalent_compose_assoc.{u} {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @Equivalent.{u} ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))
```

Place in `OpenMath/Chapter3/Section381.lean` inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, immediately after
`composeQ_inverse_left` (line ~3056), in a new `/-! ### §382 group
associativity -/` subsection comment.

## §C — Proof recipe for `compose_equivalent_compose_assoc`

The proof works at the abstract `IsRKOneStep` level — never inspects
stage counts, never invokes HEq. Pattern mirrors cycles 217 / 219 /
220.

**Strategy**: pick `H₀ := min (min H₁ H₂) H₃` where each `Hᵢ` is the
threshold from `equivalent_self Mᵢ`. Use cycle 214's
`compose_isRKOneStep_iff` to factor each side into three sequential
single-`Mᵢ`-steps, then chain three uniqueness applications to force
all three intermediates to agree.

```lean
theorem compose_equivalent_compose_assoc.{u} {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @Equivalent.{u} ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃)) := by
  intro N _ _ _ f L hL
  obtain ⟨H₁, hH₁_pos, hM₁_uniq⟩ := M₁.equivalent_self f L hL
  obtain ⟨H₂, hH₂_pos, hM₂_uniq⟩ := M₂.equivalent_self f L hL
  obtain ⟨H₃, hH₃_pos, hM₃_uniq⟩ := M₃.equivalent_self f L hL
  refine ⟨min (min H₁ H₂) H₃,
    lt_min (lt_min hH₁_pos hH₂_pos) hH₃_pos, ?_⟩
  intro y₀ H hH_pos hH_le y_final y_final' h_LHS h_RHS
  have hH_le_H₁ : H ≤ H₁ :=
    le_trans hH_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hH_le_H₂ : H ≤ H₂ :=
    le_trans hH_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hH_le_H₃ : H ≤ H₃ := le_trans hH_le (min_le_right _ _)
  -- Decompose LHS via outer (M₁.compose M₂) ∘ M₃, then inner M₁ ∘ M₂.
  obtain ⟨y_LHS_mid23, h_LHS_compose12, h_LHS_step3⟩ :=
    (compose_isRKOneStep_iff (M₁.compose M₂) M₃ f y₀ H y_final).mp h_LHS
  obtain ⟨y_LHS_mid12, h_LHS_step1, h_LHS_step2⟩ :=
    (compose_isRKOneStep_iff M₁ M₂ f y₀ H y_LHS_mid23).mp h_LHS_compose12
  -- Decompose RHS via outer M₁ ∘ (M₂.compose M₃), then inner M₂ ∘ M₃.
  obtain ⟨y_RHS_mid1, h_RHS_step1, h_RHS_compose23⟩ :=
    (compose_isRKOneStep_iff M₁ (M₂.compose M₃) f y₀ H y_final').mp h_RHS
  obtain ⟨y_RHS_mid12, h_RHS_step2, h_RHS_step3⟩ :=
    (compose_isRKOneStep_iff M₂ M₃ f y_RHS_mid1 H y_final').mp h_RHS_compose23
  -- Three uniqueness chains: M₁ from y₀, M₂ from common-mid1, M₃ from
  -- common-mid12.
  have hmid1 : y_LHS_mid12 = y_RHS_mid1 :=
    hM₁_uniq y₀ H hH_pos hH_le_H₁ y_LHS_mid12 y_RHS_mid1
      h_LHS_step1 h_RHS_step1
  rw [hmid1] at h_LHS_step2
  have hmid12 : y_LHS_mid23 = y_RHS_mid12 :=
    hM₂_uniq y_RHS_mid1 H hH_pos hH_le_H₂ y_LHS_mid23 y_RHS_mid12
      h_LHS_step2 h_RHS_step2
  rw [hmid12] at h_LHS_step3
  exact hM₃_uniq y_RHS_mid12 H hH_pos hH_le_H₃ y_final y_final'
    h_LHS_step3 h_RHS_step3
```

Estimated ~35 LOC body + ~12 LOC docstring. Naming choice uses
distinct prefixes `y_LHS_*` / `y_RHS_*` to avoid shadowing collisions
flagged in R4 below.

### Naming care

The destructured `obtain ⟨y_LHS_mid23, h_LHS_compose12, h_LHS_step3⟩`
introduces hypothesis names. If Lean complains about shadowing or
wrong introductions, rename live; the structure is non-negotiable
but the specific identifiers can be adjusted within the 10-min
abort window for R4.

## §D — P2: quotient-level corollary

Lift to `composeQ` via `Quotient.inductionOn₃` + `Quotient.sound`.
`Quotient.inductionOn₃` is in Lean core (verified — used by
`Mathlib.Data.Quot:644`). Identical syntactic shape to cycle 219's
`composeQ_id_left`/`composeQ_id_right` and cycle 220's
`composeQ_inverse_right`/`composeQ_inverse_left`.

```lean
theorem composeQ_assoc.{u}
    (p q r : Quotient Equivalent.setoidSigma.{u}) :
    composeQ (composeQ p q) r = composeQ p (composeQ q r) := by
  refine Quotient.inductionOn₃ p q r ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₃, M₃⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_equivalent_compose_assoc M₁ M₂ M₃)
```

Place immediately after `compose_equivalent_compose_assoc`.
Estimated ~10 LOC body + ~6 LOC docstring.

**Risk**: `composeQ (composeQ p q) r` LHS-unfold may require an extra
`show Quotient.mk _ _ = Quotient.mk _ _` line OR may need the
`composeQ` `lift₂` reduction to fire — try plain `Quotient.sound`
first; if Lean complains about type mismatches between
`Quotient.mk ⟨(s₁+s₂)+s₃, _⟩` and `Quotient.mk ⟨s₁+(s₂+s₃), _⟩`,
use the explicit `show Quotient.mk _ _ = Quotient.mk _ _` reframing
(cycle 219/220 precedent).

## §E — P3: Non-vacuity examples (paddedEuler)

Place in `namespace OpenMath.Chapter3.Section381` at the end of
the file (after the cycle 220 P6 examples, around line 3260). Two
examples following the cycle 219/220 P6 template:

```lean
/-- *Non-vacuity for `compose_equivalent_compose_assoc` (cycle 221 P3).*
Triple composition of `paddedEuler` is equivalent under either
associativity grouping. Concrete instance at `s₁ = s₂ = s₃ = 2`:
the stage count `(2+2)+2` matches `2+(2+2)` definitionally on
concrete numerals (both reduce to `6`), so this is a
homogeneous-stage `@Equivalent 6 6` claim despite the
heterogeneous-stage signature of the general theorem. -/
example :
    @RKTableau.Equivalent ((2 + 2) + 2) (2 + (2 + 2))
      ((paddedEuler.compose paddedEuler).compose paddedEuler)
      (paddedEuler.compose (paddedEuler.compose paddedEuler)) :=
  RKTableau.compose_equivalent_compose_assoc
    paddedEuler paddedEuler paddedEuler

/-- *Non-vacuity for `composeQ_assoc` (cycle 221 P3).* Quotient-
level associativity exercised on three copies of `⟨2, paddedEuler⟩`.
Routes through the cycle 030 non-vacuity backbone. -/
example :
    RKTableau.composeQ
        (RKTableau.composeQ
          (Quotient.mk RKTableau.Equivalent.setoidSigma
            ⟨2, paddedEuler⟩)
          (Quotient.mk RKTableau.Equivalent.setoidSigma
            ⟨2, paddedEuler⟩))
        (Quotient.mk RKTableau.Equivalent.setoidSigma
          ⟨2, paddedEuler⟩)
      = RKTableau.composeQ
          (Quotient.mk RKTableau.Equivalent.setoidSigma
            ⟨2, paddedEuler⟩)
          (RKTableau.composeQ
            (Quotient.mk RKTableau.Equivalent.setoidSigma
              ⟨2, paddedEuler⟩)
            (Quotient.mk RKTableau.Equivalent.setoidSigma
              ⟨2, paddedEuler⟩)) :=
  RKTableau.composeQ_assoc _ _ _
```

Estimated ~20 LOC.

## §F — Pre-flagged risks

- **R1 (three-way `min_le_*` chains)**: `H ≤ min (min H₁ H₂) H₃`
  unfolds as `min_le_left/right` composed; the specific composition
  for each `Hᵢ` is given in the recipe above. If `le_trans` chains
  bog down, factor out `min_le_iff` or use `omega` after extracting
  individual `H ≤ Hᵢ` facts. **Likelihood: low** — the cycle 219 /
  cycle 220 two-way analog worked first try.
- **R2 (`Quotient.inductionOn₃` name)**: confirmed present in Lean
  core (used by Mathlib's `Quot.lean:644`). Should fire on first
  compile.
- **R3 (`composeQ` lift₂ reduction in P2)**: the LHS `composeQ
  (composeQ ⟦⟨s₁,M₁⟩⟧ ⟦⟨s₂,M₂⟩⟧) ⟦⟨s₃,M₃⟩⟧` reduces via
  `Quotient.lift₂_mk` (definitional) twice to
  `Quotient.mk ⟨(s₁+s₂)+s₃, (M₁.compose M₂).compose M₃⟩`. Similarly
  the RHS reduces to `Quotient.mk ⟨s₁+(s₂+s₃), M₁.compose (M₂.compose
  M₃)⟩`. If `show Quotient.mk _ _ = Quotient.mk _ _` doesn't fire,
  unfold `composeQ` first with `simp only [composeQ]` or supply the
  explicit metavariables. **Likelihood: low** — cycle 219/220 lifts
  worked uniformly.
- **R4 (variable shadowing in `obtain ⟨...⟩`)**:
  the inner `obtain` introduces names that collide with the outer
  ones. The recipe in §C uses distinct `_LHS_` / `_RHS_` prefixes
  to mitigate. If Lean still complains, rename live; do NOT spend
  more than 10 minutes here.
- **R5 (`@Equivalent.{u}` annotation on heterogeneous types)**:
  the explicit `.{u}` annotation has worked uniformly in cycles
  204+. Pattern from cycle 220 `compose_inverse_equivalent.{u}`.
- **R6 (spurious `.{u}` on `RKTableau`)**: the cycle 218 dead end
  applies — `RKTableau` is NOT universe-polymorphic. Use `.{u}`
  only on `Equivalent.{u}` and `Equivalent.setoidSigma.{u}`.
  Annotate cycles' theorem heads with `.{u}` to match cycle 217 /
  cycle 220 conventions; never annotate `RKTableau s` references.
- **R7 (dot-notation universe trap)**: per cycle 220 discovery,
  `X.f.{u}` parses as `X.{u}.f`. Use `f.{u} X` form or fully
  qualified `OpenMath.Chapter3.Section312.RKTableau.f.{u} X`. Avoid
  dot-notation on universe-annotated calls.
- **R8 (`equivalent_self.{u}`)**: per cycle 220 discovery,
  `equivalent_self` is universe-monomorphic. Do NOT annotate with
  `.{u}` at call sites. Use plain `M₁.equivalent_self f L hL`.

## §G — Stretch goal (only if time permits, ≤30 min remaining)

If P1/P2/P3 land by min 70 of the cycle, **stop** and ship. Avoid
opening Pandora's box. If genuinely confident:

**Stretch S1**: `inverse_equivalent_inverse` — "M ≡ M' implies
M.inverse ≡ M'.inverse" — needed for cycle 222's `Group` instance
to lift `RKTableau.inverse` to `Quotient` via `Quotient.map`.
LOC estimate: ~50 (involves step-inversion + uniqueness chain similar
to `compose_equivalent_compose`).

**Strong default**: NO stretch. Ship P1+P2+P3 axiom-clean and
stop. Cycle 222 takes care of the Group instance with a fresh
analysis.

## §H — What NOT to try

1. **Do NOT** attempt the on-the-nose `compose_assoc` (cycle 210's
   deferred `HEq` claim). It's blocked on `Fin.append_assoc`'s
   `Fin.cast` composition; see
   `.prover-state/issues/compose_assoc_HEq_plumbing.md` for the
   full dead-end analysis. The `Equivalent`-level form sidesteps
   all of it.
2. **Do NOT** route through `Quotient.hrecOn₃` or any heterogeneous
   recursor. Plain `Quotient.inductionOn₃` suffices because
   `composeQ`'s output type does not depend on the inputs.
3. **Do NOT** invoke `Nat.add_assoc` directly — the proof works at
   the abstract `IsRKOneStep` level, where stage counts are
   irrelevant. The heterogeneous-stage signature is naturally
   discharged by the `compose_isRKOneStep_iff` factorisation which
   never inspects them.
4. **Do NOT** use `M.equivalent_self.{u}` with explicit `.{u}` —
   per cycle 220's discovery (R8), `equivalent_self` is
   universe-monomorphic.
5. **Do NOT** use `M.compose_equivalent_compose_assoc.{u}` dot-notation
   per R7 above. Use function-application form
   `compose_equivalent_compose_assoc.{u} M₁ M₂ M₃` if `.{u}`
   annotation is needed in a call site.
6. **Do NOT** restate any §441 work this cycle. §441 Phase C.2 stays
   GPFS-blocked per §A; only the smoke test runs against it.
7. **Do NOT** raise `maxHeartbeats`. Per CLAUDE.md.
8. **Do NOT** introduce axioms or constants.
9. **Do NOT** attempt the `Group` instance this cycle. Cycle 222
   territory.

## §I — Verification plan

After landing P1+P2+P3, verify with:

```bash
time lake env lean OpenMath/Chapter3/Section381.lean
```

Expected: clean exit, no errors, no new warnings.
Expected rebuild time: 4–8 seconds (warm cache). If >30s with
zero progress, something is wrong — investigate before committing.

Run `lean_verify` on the two main symbols:
- `OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose_assoc`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_assoc`

Both should return `[propext, Classical.choice, Quot.sound]` only
— no `sorryAx`.

Regression check — re-verify cycle 218/219/220 landmarks remain
axiom-clean:
- `composeQ_eq_of_equivalent`
- `composeQ_id_left`, `composeQ_id_right`
- `composeQ_inverse_right`, `composeQ_inverse_left`

Sorry count: must remain 0.

## §J — Recommended invocation sequence

Linear execution (~75 min budget):

1. **§A** (5 min): GPFS smoke test. If healthy, switch to Phase C.2
   per `lem_441A_phase_C_scoping.md`; else continue.
2. **P1** (25 min): write `compose_equivalent_compose_assoc` —
   ~35 LOC body + docstring. Compile + axiom-check.
3. **P2** (15 min): write `composeQ_assoc` — ~10 LOC body +
   docstring. Compile + axiom-check.
4. **P3** (15 min): write two `paddedEuler` non-vacuity examples
   (§E above) — ~20 LOC total. Compile.
5. **Housekeeping** (15 min): update `plan.md` def:381A row with
   cycle 221 note; update
   `.prover-state/issues/compose_assoc_HEq_plumbing.md` to record
   that the Equivalent-level associativity is now shipped (the
   on-the-nose `compose_assoc` HEq blocker remains unresolved but
   no longer load-bearing for §382 group structure); write
   `cycle_221.md` task results; final `lake env lean`; commit.

**Abort threshold (§F-style)**: If P1's body fails to compile in 3
sequential attempts (≤45 min total from start), **stop P1**, ship
P1 as a sorry-scaffold (one sorry, signature locked in), and
proceed to P3 examples (cycle 215 precedent). Document the failure
mode in cycle 221 task results and pre-position cycle 222 for
closure. The strategy's stretch goal is optional and should NOT
be touched in this contingency.

**Strict default**: ship P1+P2+P3, ~65 LOC total LOC delta. Stable
warm rebuild ~5s of §381.

## §K — Housekeeping notes

- `plan.md` def:381A row: extend with cycle 221 entry noting the
  Equivalent-level associativity + quotient-level corollary, with
  cross-references to `compose_assoc_HEq_plumbing.md`'s cycle 219
  update (the HEq finesse rationale).
- `lean_status.json`: no entity status transition required. def:381A
  remains formalized; thm:382A remains formalized; thm:382B remains
  formalized (cycle 220). The cycle 221 deliverable is supplementary
  infrastructure for the future `Group` instance, not a textbook
  theorem in its own right.
- `.prover-state/issues/compose_assoc_HEq_plumbing.md`: extend the
  cycle 219 update with a cycle 221 note recording that the
  Equivalent-level associativity is now shipped and the on-the-nose
  HEq claim is permanently superseded by the quotient route.
- `.prover-state/issues/thm_382A_path.md`: extend cycle 220 outlook
  section with cycle 221's associativity completion and an updated
  cycle 222 outlook (Group instance: needs `inverse_equivalent_inverse`
  for the `inv` lift, then composition of cycles 219/220/221's
  absorption laws).
- §441 Phase C.2: 38th consecutive GPFS-blocked timeout expected.
  Append one-line cycle 221 entry to `cycle_182_gpfs_slowness.md`
  per the established 37-cycle pattern.
