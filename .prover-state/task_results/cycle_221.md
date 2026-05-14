# Cycle 221 Results

## Worked on

§382 group **associativity** at both the `Equivalent` level and the
quotient level — the third of the four §382 group axioms (after
cycles 219/220's identity and inverse). Strategy §B–§F linear
execution path.

Two new symbols shipped at
`OpenMath/Chapter3/Section381.lean` inside
`namespace OpenMath.Chapter3.Section312.RKTableau`:

1. **`RKTableau.compose_equivalent_compose_assoc.{u}`** (P1,
   ~35 LOC body + ~22 LOC docstring) — heterogeneous-stage
   `@Equivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
     ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))`
   for `M₁ : RKTableau s₁`, `M₂ : RKTableau s₂`, `M₃ : RKTableau s₃`.
   Placed at line ~3060, immediately after `composeQ_inverse_left`
   (cycle 220), in a new `/-! ### §382 group associativity -/`
   subsection comment.

2. **`RKTableau.composeQ_assoc`** (P2, ~10 LOC body + ~7 LOC
   docstring) — for `p q r : Quotient Equivalent.setoidSigma.{u}`,
   `composeQ (composeQ p q) r = composeQ p (composeQ q r)`. Placed
   immediately after deliverable 1.

P3 non-vacuity (~25 LOC total at end of file):

- Triple `paddedEuler` Equivalent witness at `((2+2)+2, 2+(2+2))`.
- Quotient-level associativity on three copies of
  `⟦⟨2, paddedEuler⟩⟧`.

## Approach

Strategy's linear execution per §J was followed exactly:

1. **§A (5 min)** — GPFS smoke test on §441. As expected, 38th
   consecutive timeout (EXIT=143 after 300s, near-zero CPU). Logged
   in `cycle_182_gpfs_slowness.md`. Continued with §B–§F.

2. **P1 (~25 min)** — wrote `compose_equivalent_compose_assoc`
   verbatim from strategy §C's recipe. Proof structure:
   - Threshold `min (min H₁ H₂) H₃` from three `Mᵢ.equivalent_self
     f L hL` applications (no `.{u}` on `equivalent_self` per
     cycle 220 R8 discovery).
   - Three `H ≤ Hᵢ` facts extracted via two `min_le_*` chains.
   - LHS factored twice via cycle 214's `compose_isRKOneStep_iff`:
     outer `(M₁·M₂)·M₃` yields `y_LHS_mid23` and
     `h_LHS_compose12`; inner `M₁·M₂` further yields `y_LHS_mid12`
     and the two single-stage witnesses `h_LHS_step1` /
     `h_LHS_step2`.
   - RHS factored twice analogously: outer `M₁·(M₂·M₃)` yields
     `y_RHS_mid1` and `h_RHS_compose23`; inner `M₂·M₃` further
     yields `y_RHS_mid12` and the two single-stage witnesses.
   - Three uniqueness chains: `M₁` from `y₀` forces
     `y_LHS_mid12 = y_RHS_mid1`; `M₂` from common `mid1` forces
     `y_LHS_mid23 = y_RHS_mid12` (after `rw [hmid1]`); `M₃` from
     common `mid12` closes `y_final = y_final'` (after
     `rw [hmid12]`).
   - The proof never inspects stage counts; the heterogeneous-
     stage signature is discharged by abstract-`N`-level reasoning.

3. **P2 (~10 min)** — wrote `composeQ_assoc` via
   `Quotient.inductionOn₃` + `rintro` destructure + `show
   Quotient.mk _ _ = Quotient.mk _ _` reframe + `Quotient.sound
   (compose_equivalent_compose_assoc M₁ M₂ M₃)`. Identical
   syntactic shape to cycles 219/220's quotient-level lifts.

4. **P3 (~10 min)** — wrote two non-vacuity examples on
   `paddedEuler` following the cycle 219/220 P6 template.

5. **Verification (~15 min)** — cold build of Section381.lean took
   1m33s, warm rebuild 7.6s (well within strategy §I's 4-8s
   expectation). Both new symbols verified `[propext,
   Classical.choice, Quot.sound]` axiom-clean via `lean_verify`.
   Regression checks on `composeQ_eq_of_equivalent`,
   `composeQ_id_left`, `composeQ_id_right`,
   `composeQ_inverse_right`, `composeQ_inverse_left` — all
   axiom-clean, no regressions. Sorry count remains 0.

6. **Housekeeping** — updated `plan.md` def:381A row with cycle
   221 entry; appended cycle 221 update sections to
   `compose_assoc_HEq_plumbing.md` and `thm_382A_path.md`; logged
   the 38th GPFS timeout in `cycle_182_gpfs_slowness.md`.

## Result

**SUCCESS** — all three priorities (P1 / P2 / P3) shipped on first
compile, no rework required. Sorry count remains 0. Section381.lean
builds clean. Both new symbols axiom-clean (`[propext,
Classical.choice, Quot.sound]`). All pre-flagged R1–R8 risks did
NOT fire — the cycle 217/219/220 abstract-`IsRKOneStep`-level
recipe generalised cleanly to three factors.

§441 Phase C.2 remains GPFS-blocked (38th consecutive timeout) per
strategy §A.

## Faithfulness check

`compose_equivalent_compose_assoc.{u}` and `composeQ_assoc` are
**supplementary infrastructure** for the future `Group` instance on
`Quotient Equivalent.setoidSigma` (cycle 222+). They are NOT direct
textbook formalizations in their own right — they implement Butcher
§382's implicit group-axiom step in machine-readable form.

The textbook anchor for cycle 221's deliverables is **the §382 group
construction** (Butcher pp. 305–307). Butcher's text states without
proof that "the operation `·` is associative", relying on the
reader's intuition that composition of methods (interleaved
sequential application) is associative. Cycle 221 formalizes this
intuition explicitly.

- **Entity ID**: `thm:382A` (the umbrella "group of RK methods"
  theorem, already marked `formalized` in `lean_status.json` after
  cycle 218). No status transition required.
- **Textbook statement** (Butcher §382, p. 305): "The operation `·`
  is associative, with the trivial method as identity and
  `M^{-1}` as inverse [...] hence the equivalence classes
  `[m]` form a group."
- **Lean statement captures**: same content — the associativity
  axiom of the §382 group, faithfully stated at both the
  `Equivalent` level (the natural setting where `compose`'s
  heterogeneous stage counts are accommodated) and the quotient
  level (the literal "group operation on `[m]`" form).
- **No divergence**: heterogeneous-stage signature is the natural
  Lean shape for `compose`'s stage-count behavior; the textbook
  form `[m₁ · (m₂ · m₃)] = [(m₁ · m₂) · m₃]` is exactly
  `composeQ_assoc` with the standard quotient bracket notation.

### Tautology / identity / smuggling checks (all pass)

- **Tautology**: neither `compose_equivalent_compose_assoc` nor
  `composeQ_assoc` has a conclusion that appears verbatim as a
  hypothesis. The hypothesis is the three RKTableau inputs; the
  conclusion is an Equivalent (resp. quotient-equality) between
  two different parenthesizations of their composite.
- **Identity**: proofs are not `exact h` — they are genuine
  ~35-LOC and ~5-LOC proof bodies invoking `compose_isRKOneStep_iff`
  factorisations, `equivalent_self` uniqueness chains, and
  `Quotient.inductionOn₃` / `Quotient.sound` lift machinery.
- **Definition smuggling**: no new `def` or `structure` introduced
  — only two `theorem`s.
- **Hypothesis strength**: signatures use no hypotheses beyond the
  three `RKTableau sᵢ` inputs; cannot be weakened further. Stage-
  count parameters are implicit. No `[CompleteSpace N]` or
  Lipschitz constants leak into the user-facing signature (they
  are extracted from `equivalent_self`'s threshold).

## Dead ends

**None.** Strategy §C's proof recipe compiled on the first
attempt. All eight pre-flagged risks (§F R1–R8) did NOT fire:

- **R1 (three-way `min_le_*` chains)**: did NOT fire. The two
  `le_trans` chains `min_le_left _ _` ∘ `min_le_left _ _` (for
  H₁), `min_le_left _ _` ∘ `min_le_right _ _` (for H₂), and
  `min_le_right _ _` (for H₃) compiled cleanly.
- **R2 (`Quotient.inductionOn₃` name)**: did NOT fire. Lean
  recognized the name on first compile.
- **R3 (`composeQ` lift₂ reduction in P2)**: did NOT fire. The
  `show Quotient.mk _ _ = Quotient.mk _ _` reframe + plain
  `Quotient.sound` discharged P2 directly without needing to
  unfold `composeQ` via `simp only`.
- **R4 (variable shadowing in `obtain ⟨...⟩`)**: did NOT fire.
  The distinct `_LHS_` / `_RHS_` prefixes prevented any name
  collisions.
- **R5 (`@Equivalent.{u}` annotation on heterogeneous types)**:
  did NOT fire. Explicit `.{u}` on `compose_equivalent_compose_assoc`
  worked on first compile.
- **R6 (spurious `.{u}` on `RKTableau`)**: did NOT fire. Universe
  annotation applied only to `Equivalent.{u}` and
  `Equivalent.setoidSigma.{u}`; `RKTableau s` references kept
  bare (mindful of cycle 218's dead end).
- **R7 (dot-notation universe trap)**: did NOT fire. No `.{u}`
  dot-notation calls in the recipe.
- **R8 (`equivalent_self.{u}`)**: did NOT fire. Used
  `Mᵢ.equivalent_self f L hL` (no `.{u}` annotation) per cycle
  220 discovery; Lean inferred universe levels without complaint.

## Discovery

1. **Three-factor abstract-`IsRKOneStep` recipe generalises
   smoothly**: cycle 221 confirms that cycles 217/219/220's
   abstract-`IsRKOneStep`-level technique (threshold from
   `equivalent_self`, factor via `compose_isRKOneStep_iff`,
   chain uniqueness applications) generalises from two factors
   (`compose_equivalent_compose`, cycle 217) and one-vs-zero
   (`compose_id_equivalent` / `id_compose_equivalent`, cycle
   219) and one-vs-one (`compose_inverse_equivalent` /
   `inverse_compose_equivalent`, cycle 220) to three factors,
   with no qualitative change in proof shape. The technique's
   key strength: it never inspects stage counts, so
   heterogeneous-stage signatures (`(s₁+s₂)+s₃` vs `s₁+(s₂+s₃)`,
   `s+s` vs `0`, etc.) are discharged automatically by abstract-
   `N`-level reasoning. Conjecture: any "compose multiple methods
   in different parenthesizations or orderings" equivalence
   follows the same template.

2. **`Quotient.inductionOn₃` is the natural recursor for ternary
   group axioms**: strategy §D's choice of `Quotient.inductionOn₃`
   (not `Quotient.ind` thrice or `Quotient.hrecOn₃`) is the
   cleanest path. The output type does not depend on the inputs
   (it's `Quotient Equivalent.setoidSigma`, fixed), so plain
   induction suffices — no heterogeneous recursor needed.
   Confirmed in Lean core; works on first compile.

3. **The on-the-nose `compose_assoc` HEq blocker is permanently
   superseded**: with cycle 221's `compose_equivalent_compose_assoc`
   in hand and `Quotient.sound` discharging the heterogeneous-
   stage mismatch, the cycle 210 on-the-nose `compose_assoc`
   blocker is no longer load-bearing for any §382 group
   construction. The blocker remains technically unresolved at
   the `RKTableau`-level (no on-the-nose
   `M₁.compose (M₂.compose M₃) = (M₁.compose M₂).compose M₃` is
   provable without HEq plumbing), but every downstream consumer
   routes through `composeQ` and `composeQ_assoc` instead.

4. **Stage-count Σ-projection-inside-representative pattern is
   load-bearing for the §382 group**: the design choice in cycle
   212 to put the stage count `s` inside the Σ-typed setoid
   element (`Σ s : ℕ, RKTableau s`) rather than as a parameter
   of the setoid pays off here. With `Quotient
   Equivalent.setoidSigma : Type`, the output type of `composeQ`
   does not vary with the stage-count sum, so all group-axiom
   lifts are mechanical `Quotient.inductionOnₙ` + `Quotient.sound`
   one-liners over the corresponding `Equivalent`-level facts.
   This is the architectural reason the cycle 219/220/221
   quotient-level proofs are uniformly ~10 LOC each.

## Suggested next approach

**Cycle 222 — `Group` instance on `Quotient Equivalent.setoidSigma`**.
With three of the four `Group` axioms (identity / inverse /
associativity) now closed at the quotient level, the entry point
for cycle 222 is the lift of `RKTableau.inverse` to the quotient,
needed for the `inv` operation:

1. **P1 (~50 LOC) — `inverse_equivalent_inverse.{u}`**: the
   "function respects equivalence" lemma for `RKTableau.inverse`.
   Signature `@Equivalent s s' M M' → @Equivalent s s' M.inverse
   M'.inverse`. Proof recipe (analogous to
   `compose_equivalent_compose`): threshold from
   `equivalent_self M.inverse`; factor two parallel
   `M.inverse.IsRKOneStep` / `M'.inverse.IsRKOneStep` witnesses
   via cycle 220's `isRKOneStep_of_inverse_isRKOneStep` into
   `M.IsRKOneStep` / `M'.IsRKOneStep` witnesses on the reversed
   `(y_mid, y₀)` direction; leverage the `M ≡ M'` hypothesis to
   force the underlying values to agree; transport back through
   `inverse_isRKOneStep_of_isRKOneStep`.

2. **P2 (~10 LOC) — `inverseQ`**: lift `RKTableau.inverse` to
   `Quotient Equivalent.setoidSigma` via `Quotient.map` with
   `inverse_equivalent_inverse` as the respect proof.

3. **P3 (~20 LOC) — `instance : Group (Quotient
   Equivalent.setoidSigma)`**: bundle cycle 219's `composeQ_id_*`,
   cycle 220's `composeQ_inverse_*`, cycle 221's `composeQ_assoc`,
   and the new `inverseQ` into Mathlib's `Group` typeclass. The
   `mul = composeQ`, `one = ⟦⟨0, RKTableau.id⟩⟧`, `inv = inverseQ`.
   May need explicit `mul_assoc` / `one_mul` / `mul_one` /
   `mul_left_inv` field bindings — the names might differ
   slightly from cycle 219/220/221's symbol names.

4. **P4 non-vacuity**: instantiate the `Group` instance and
   compute `⟦⟨2, paddedEuler⟩⟧ * ⟦⟨2, paddedEuler.inverse⟩⟧ =
   1` directly using the `Group` typeclass syntax (no longer
   `composeQ_inverse_right`-shaped).

**Stretch (cycle 222+ if time permits)**: investigate the §383
"group homomorphism via Φ" path. With the `Group` instance in
hand on `Quotient Equivalent.setoidSigma`, the next textbook
deliverable is `thm:383A` (the Φ map respects group operations);
this would be cycle 223+ but should be scoped earlier if
opportune.

§441 Phase C.2 path: continues to be blocked by GPFS pathology
(38 consecutive cycles). Strategy continues to skip it per the
established pattern. If GPFS recovers in a future cycle, the
preserved draft at `.prover-state/cycle_182_draft_section441.lean`
plus the cycle 184 namespace fix on line 1529 are ready for
immediate resumption.
