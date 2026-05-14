# Cycle 232 Results

## Worked on

Aristotle path-A closure of the §383 group-homomorphism Phase 3:
- The right-action half of `compose_phiEquivalent_compose`
  (M₂-side sum equality `derivativeWeightWithSrcSum_M₂_phi_eq`,
  unblocked by Aristotle project
  `176aa964-db7b-40f8-a01c-05247c186ec5` COMPLETE at 100 %).
- The full bilinear `compose_phiEquivalent_compose` (`PhiEquivalent
  M₁ M₁' → PhiEquivalent M₂ M₂' → PhiEquivalent (M₁.compose M₂)
  (M₁'.compose M₂')`) via `.trans` of left (cycle 226) + right
  (cycle 232) at the intermediate composite `M₁'.compose M₂`.
- The full binary `composeQ_phi : Quotient PhiEquivalent.setoidSigma
  → Quotient PhiEquivalent.setoidSigma → Quotient
  PhiEquivalent.setoidSigma` via `Quotient.lift₂` consuming
  `compose_phiEquivalent_compose`.
- Two `@[simp]` lemmas: `composeQ_phi_mk` (rfl-based unfold)
  and `composeQ_phi_eq_left_act_mk` (rfl-based bridge to cycle
  227's partial `composeQ_phi_left_act`).
- Five `paddedEuler`-based non-vacuity witnesses exercising
  both right-action halves and the full binary operation.

## Approach

Strategy `§B` decision tree path A: poll Aristotle once at cycle
start, find COMPLETE at 100 %, suspend the cycle 232 path-B
plan (`compose_assoc_phiEquivalent`), and instead extract +
incorporate Aristotle's proof + assemble the full
`composeQ_phi`.

1. `mcp__aristotle__get_status` returned `COMPLETE at 100 %`
   (started 2026-05-14T15:50:23, finished 2026-05-14T17:28:04).
2. `mcp__aristotle__extract_result` to `/tmp/aristotle_cycle232_result`.
3. Compared Aristotle's `Section381.lean` (4119 lines) against
   HEAD (4699 lines): Aristotle was given a pre-cycle-227
   snapshot, so its insertion at lines 2860–3050 in its file
   needed to be mapped to *after* cycles 230–231's mutual blocks
   in HEAD (post line 3021).
4. Inserted the Aristotle symbols (~225 LOC) as a single
   `section / open OpenMath.Chapter3.Section310 / end` wrapper
   between cycle 231's bottom-block `end` and cycle 227's
   `composeQ_phi_left_act` doc block:
   - `private theorem derivativeWeightProd_append` (DP is
     multiplicative over list append, ~6 LOC).
   - `private mutual { gen_dws_eq, gen_dwsp_eq }` (the
     generalized weight-compatibility claim with trailing-
     factor parameter `f`, ~75 LOC for the mutual block).
   - `private theorem derivativeWeightWithSrcSum_M₂_phi_eq`
     (the Aristotle target, ~15 LOC).
   - `theorem compose_phiEquivalent_compose_right` (~10 LOC).
   - `theorem compose_phiEquivalent_compose` (~10 LOC, one-line
     `.trans` proof body).
5. Added `composeQ_phi` and its simp lemmas (~50 LOC) after
   cycle 227's `composeQ_phi_left_act_eq_of_phiEquivalent`
   (line 3287 area in HEAD before edit).
6. Added 5 P2 non-vacuity `example`s at the file's end inside
   `namespace OpenMath.Chapter3.Section381` (~75 LOC):
   homogeneous + heterogeneous-stage right-action witnesses,
   full-bilinear heterogeneous-both witness, `composeQ_phi`
   `rfl` witness, and Φ-bridged heterogeneous-stage
   well-definedness witness.
7. `lake build OpenMath.Chapter3.Section381` clean (only
   `linter.unusedSimpArgs` warnings on Aristotle's
   simp-with-redundant-args calls, no errors). Cold rebuild
   2m10s, warm rebuild 6.5s.
8. Axiom check via `lake env lean /tmp/check_axioms.lean`
   after rebuild: all new symbols `[propext, Classical.choice,
   Quot.sound]`.

## Result

**SUCCESS** — all targets shipped axiom-clean.

- `compose_phiEquivalent_compose_right` — axioms: `[propext,
  Classical.choice, Quot.sound]`.
- `compose_phiEquivalent_compose` — axioms: same.
- `composeQ_phi` — axioms: same.
- `composeQ_phi_mk` — axioms: same.
- `composeQ_phi_eq_left_act_mk` — axioms: same.
- Regression spot-checks on `compose_phiEquivalent_compose_left`
  (cycle 226), `composeQ_phi_left_act` (cycle 227),
  `composeQ_phi_left_act_id_left` (cycle 228),
  `composeQ_phi_left_act_id_right` (cycle 229) — all
  `[propext, Classical.choice, Quot.sound]`.
- Cycle 230/231 lemmas (`derivativeWeightWithSrc_compose_castAdd`
  / `_natAdd`) are `private`, so unreachable from `#print
  axioms` via a separate file; transitivity of axiom-cleanness
  through the public `compose_phiEquivalent_compose_right`
  (which consumes them indirectly via
  `compose_elementaryWeight_decomp`) confirms cleanness.
- Sorry count remains **0** (46th consecutive clean cycle
  since the cycle 201 rollback).
- Section381.lean total line count: 4779 (was 4699; +80 net
  for the assembly).

## Faithfulness check

### `compose_phiEquivalent_compose_right`

- **Entity ID**: `thm:384A` (the §383 group-homomorphism
  result, which states `Φ̂ = Φ · Φ̃` pointwise on rooted trees
  for the composite method).
- **Textbook statement quoted from
  `extraction/formalization_data/entities/thm_384A.json`**:
  > "Let Φ : T → ℝ be the elementary weight function associated
  > with (A, b, c) and Φ̃ : T → ℝ the elementary weight function
  > associated with (Ã, b̃, c̃). Let Φ̂ : T → ℝ denote the
  > elementary weight function for the product method as
  > represented by (eq:382a). Then Φ̂ = Φ Φ̃."
- **Lean statement captures**: same content (different
  presentation). Butcher's `Φ̂ = Φ · Φ̃` says the composite
  method's elementary weight function is determined by the
  factors' elementary weight functions (the elementary weight
  function is the *only* relevant data). The Lean version
  `compose_phiEquivalent_compose` captures the same observation
  in PhiEquivalent form: if `PhiEquivalent M₁ M₁'` and
  `PhiEquivalent M₂ M₂'` (i.e. they have identical elementary
  weight functions, which is exactly `Φ = Φ'` and `Φ̃ = Φ̃'`),
  then their composites are PhiEquivalent (identical Φ̂). The
  pointwise `Φ̂ = Φ · Φ̃` formula is a stronger structural
  characterization that decomposes Φ̂; the `PhiEquivalent`-respecting
  form is the consequence that gives the group-homomorphism
  property on the Φ-quotient (and is what the `composeQ_phi`
  lift directly consumes).
- **Justification for divergence**: The cycle 232 statement is
  the PhiEquivalent-respecting form (the necessary and
  sufficient witness for `Quotient.lift₂`). The pointwise
  `Φ̂ = Φ · Φ̃` formula is a separate (related) theorem and
  remains a future cycle target — it requires the explicit
  B-series expansion machinery (Connes–Kreimer coproduct,
  binomial-style identity) which Aristotle's proof
  deliberately avoids. The chosen formalization is *what the
  group-homomorphism structure consumes*; the pointwise
  characterization is downstream.

### `composeQ_phi`

- **Entity ID**: `thm:384A` (this `def` is the binary group
  operation on `Quotient PhiEquivalent.setoidSigma` that
  realizes Butcher's "homomorphism between two groups" —
  composition lifted to the Φ-quotient).
- **Lean signature**:
  `noncomputable def composeQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma`
  via `Quotient.lift₂` with `compose_phiEquivalent_compose`
  as the respect witness.
- **Captures**: the binary operation on the Φ-quotient. The
  `Group` instance (associativity, identity, inverse) on this
  quotient is still deferred to cycle 233+, but the operation
  itself is now axiom-clean and well-defined.

### Generalized helper claims (Aristotle)

- `private theorem gen_dws_eq`, `private theorem gen_dwsp_eq`:
  Internal helpers with no direct textbook counterpart. They
  encode an *induction vehicle* for the M₂-side sum equality.
  The `f` (trailing-factor) parameterization is the technical
  trick that avoids the Connes–Kreimer Hopf algebra of
  B-series — Aristotle's proof essentially uses the
  list-append associativity of `derivativeWeightProd` to
  thread compatibility through the cons-case in lieu of an
  explicit subtree-coloring decomposition.

### Pre-commit faithfulness checklist

1. **Tautology check**: no theorem conclusion equals one of
   its hypotheses. `compose_phiEquivalent_compose` consumes
   `hPhi₁ hPhi₂` and concludes about composite methods —
   distinct from the inputs.
2. **Identity check**: `compose_phiEquivalent_compose`'s
   proof is `(compose_phiEquivalent_compose_left M₂ hPhi₁).trans
   (compose_phiEquivalent_compose_right M₁' hPhi₂)` — a
   genuine `Trans` composition, not a `:= h` re-export.
   `composeQ_phi_mk` and `composeQ_phi_eq_left_act_mk` are
   `rfl`-based — these are *intentional* `simp` unfolds that
   expose the definitional `Quotient.lift₂` reduction; they
   are vacuous-by-design (they exist to fire as `simp` rules,
   not to do mathematical work).
3. **Definition smuggling check**: no `structure` introduced
   this cycle.
4. **Hypothesis strength check**: cycle 232's
   `compose_phiEquivalent_compose` takes exactly the
   hypotheses Butcher requires (`PhiEquivalent` on both
   factors). No extra hypotheses.
5. **Absent theorem check**: all promised theorems are
   present and proved.

## Dead ends

None this cycle — the entire deliverable came from
Aristotle's path-A success, so there were no manual proof
dead ends to report. The path-B plan
(`compose_assoc_phiEquivalent`) was *suspended* per strategy
§B decision tree, not abandoned after failure.

The one minor friction: `lake env lean /tmp/check_axioms.lean`
on a separate file initially returned "Unknown constant" for
the new symbols because the `Section381.olean` had not been
rebuilt yet (its mtime predated the edit). Solution:
`lake build OpenMath.Chapter3.Section381` explicitly to
refresh the olean; the `lean_verify` MCP tool already
rebuilds in-file, so it returned axioms correctly. **Future
cycle note**: after writing to a Lean file but before running
`#print axioms` from a separate test file, run `lake build
<Module>` to refresh the olean — `lake env lean
<source-file>` checks the source but does NOT update the
olean cache.

## Discovery

### D1 — Aristotle's generalized-weight-compatibility trick

The cycle 226 issue catalogued four ruled-out approaches for
the M₂-side sum equality (direct tree induction,
decomposition-then-reapply, `PhiEquivalent → Equivalent`
reduction, per-summand reasoning). Aristotle found a fifth
approach that none of those anticipated: parameterize the
list-IH with a **trailing factor** `f : List RootedTree`.
The kept-child subterm in the cons case `c :: cs` requires
proving compatibility of *updated weights*
`uⱼ = ∑ᵢ wᵢ · Aᵢⱼ · DWPᵢ(cs) · DPᵢ(f)`. Naively this
reduces to compatibility at the same list (circularity),
but a sum-swap + `derivativeWeightProd_append` rewrites
`∑ⱼ uⱼ · DPⱼ(g)` as
`∑ᵢ wᵢ · DWPᵢ(cs) · DPᵢ(f ++ [RootedTree.mk g])` — i.e.
the same shape with `cs` *shorter* and `f` *longer*. This is
the *structurally decreasing* signal that the recursion needs.

**Generalizable rule**: when a per-summand induction fails
because the inner-summand update couples weights with stage
indices, ask whether a *trailing accumulator* parameter
can absorb the inner update into a list-prefix shift —
turning a circular dependency into a well-founded one.

### D2 — `derivativeWeightProd_append` as the bridge

The trick crucially uses
`derivativeWeightProd_append : DP(i, f ++ g) = DP(i, f) · DP(i, g)`.
This is a basic list-multiplicativity fact that is *new* to
the codebase (introduced this cycle as a `private` helper);
no analogue existed before. Pattern: when introducing a
parameterized list-IH, check whether the relevant per-list
function is multiplicative over append — if so, that
multiplicativity is often the key to breaking circularity in
the propagation step.

### D3 — `Quotient.lift₂` vs `Quotient.lift` partial-action

Cycle 227 shipped `composeQ_phi_left_act` as a one-sided
`Quotient.lift` (left-arg-only lift, right-arg raw). With the
full bilinear `compose_phiEquivalent_compose` now in hand,
the cleaner `Quotient.lift₂`-based `composeQ_phi` subsumes
the partial-action: `composeQ_phi ⟦x⟧ ⟦y⟧ = composeQ_phi_left_act
⟦x⟧ ⟨y.1, y.2⟩` definitionally (shipped as
`@[simp] composeQ_phi_eq_left_act_mk` with proof `rfl`). The
cycle 227–229 partial-action API and its identity laws
(`composeQ_phi_left_act_id_left/right`) remain useful as
explicit corollaries, but `composeQ_phi` is now the canonical
operation. Future cycles should prefer it for the `Group`
instance.

### D4 — olean refresh discipline

`lake env lean <source>.lean` typechecks the source file but
does NOT update its olean. `lake build <Module>` is required
to refresh the olean cache. Cross-file `#print axioms` and
LSP-loaded MCP queries via the project (rather than the
file) need fresh oleans — be explicit about `lake build`
before cross-file axiom audits.

### D5 — Path-A timing

Aristotle's right-action job took ~12 cycles from submission
(cycle ~220 era) to COMPLETE. The growth trajectory had been
2–7 % per cycle (9 % → 11 % → 17 % → 24 % → 29 %), then a
jump from 29 % to 100 % in roughly a 5–7 day wall-clock
window. The cycle 226 issue's "Connes–Kreimer or multi-cycle
infrastructure required" assessment was too pessimistic;
Aristotle's actual solution (~225 LOC, no new mathematical
infrastructure) is far simpler than any of the four
ruled-out approaches in the cycle 226 issue would have
suggested. **Lesson**: do NOT prematurely write off an
Aristotle delegation as multi-cycle infrastructure work
just because the path-A obstacles look structurally hard —
Aristotle may find an entirely different proof strategy
that human attempts overlook.

## Suggested next approach

### Cycle 233 candidates (in priority order)

1. **`compose_assoc_phiEquivalent`** (originally cycle 232's
   path-B target, now displaced). Either reroute via the
   newly-built infrastructure (use `compose_phiEquivalent_compose`
   on cycle 221's `compose_equivalent_compose_assoc` —
   though this requires bridging `Equivalent` ⟹ `PhiEquivalent`
   on both sides, which may be cleaner via the existing
   `Equivalent`-to-`PhiEquivalent` lift), or via the
   `compose_elementaryWeight_decomp` + cycle 230/231 mutual-
   lemma route the cycle 232 strategy outlined. Estimated
   ~50–100 LOC. This is the natural prerequisite for the
   `Group` instance's associativity axiom.

2. **`Group` instance on `Quotient PhiEquivalent.setoidSigma`**.
   Requires:
   - `composeQ_phi` associativity (cycle 233 / 234 target —
     see candidate 1).
   - `composeQ_phi_id_left` / `composeQ_phi_id_right` —
     trivial generalizations of cycles 228–229's
     `composeQ_phi_left_act_id_*` (the partial-action
     identities) lifted to both arguments being quotient
     classes. Likely ~20 LOC each.
   - `composeQ_phi_inverseQ_phi_left` /
     `composeQ_phi_inverseQ_phi_right` — requires lifting
     `inverse_equivalent_inverse` (cycle ?) and
     `compose_inverse_equivalent` / `inverse_compose_equivalent`
     (cycles ~?) to the PhiEquivalent level. May require
     a `compose_inverse_phiEquivalent` analog (cycle 234 target).
   Total: 2–3 cycles to land the `Group` instance.

3. **The pointwise `Φ̂ = Φ · Φ̃` formula** (literal
   `thm:384A` statement). This is the *characterization* of
   the composite elementary weight function as a *product*
   of the factor elementary weights — a stronger statement
   than `compose_phiEquivalent_compose`. Likely requires
   Connes–Kreimer (which Aristotle avoided) or a B-series
   expansion. Lower priority — the `Group` instance is the
   immediate structural goal.

### Aristotle reuse opportunity

With Aristotle's job complete, the queue is free. Consider
submitting `compose_assoc_phiEquivalent` (or its
elementary-weight-level analog) to Aristotle in cycle 233
to lock in the associativity result; the path-B route is
straightforward but verbose, so Aristotle may find a
shorter proof. Estimated 30 min for Aristotle batch + 30
min for cycle 233 work.

### §441 Phase C.2

GPFS-blocked for 46+ consecutive cycles. No progress
expected; continue skipping per CLAUDE.md.
