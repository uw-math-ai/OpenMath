# Cycle 234 Results

## Worked on

§383 group-homomorphism path Phase 4.2 — identity axioms for the
`Group` instance on `Quotient PhiEquivalent.setoidSigma`:

- **P1.1** `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_id_left`
  (`composeQ_phi ⟦⟨0, RKTableau.id⟩⟧ q = q`)
- **P1.2** `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_id_right`
  (`composeQ_phi q ⟦⟨0, RKTableau.id⟩⟧ = q`)
- **P2.1 / P2.2** Two `paddedEuler` non-vacuity examples in
  `namespace OpenMath.Chapter3.Section381`.

## Approach

Verbatim port of cycle 219's `composeQ_id_{left,right}` template
(at the §382 `Equivalent`-quotient level) to the §383 PhiEquivalent
level, now routed through the cycle-232 full binary `composeQ_phi`
rather than the cycle-228/229 partial-action `composeQ_phi_left_act`:

```lean
theorem composeQ_phi_id_left
    (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma
        ⟨0, RKTableau.id⟩) q = q := by
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (id_compose_phiEquivalent M)
```

(P1.2 is the mirror with `compose_id_phiEquivalent M` and the
`⟨0, id⟩` argument moved to the right.) The cycle 232 binary
`composeQ_phi` is keyed on `composeQ_phi_left_act` via `Quotient.lift₂`,
so the `show Quotient.mk _ _ = Quotient.mk _ _` reframing performs the
unfolding by definitional reduction (no explicit `Quotient.lift₂_mk` /
`composeQ_phi_mk` simp lemma needed — per cycle 219 / cycle 233
templates).

## Result

**SUCCESS** — both theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`), both non-vacuity examples
type-check. Section381.lean warm rebuild 6.4s, matching the cycle
230–233 baseline (well under the §F.3 60s red-flag threshold).

Regression spot-checks via `lean_verify` all axiom-clean: cycle 232
`composeQ_phi`, cycle 233 `compose_assoc_phiEquivalent`, cycle 233
`composeQ_phi_assoc`.

Sorry count remains 0 (48th consecutive clean cycle since cycle 201
rollback).

## Strategy correction

The cycle 234 strategy template (§C.1, §C.2) said to insert the new
theorems "immediately after cycle 233's `composeQ_phi_assoc`" at
line 3454. That placement **fails to compile**:

```
OpenMath/Chapter3/Section381.lean:3467:60: error(lean.unknownIdentifier):
  Unknown constant `OpenMath.Chapter3.Section312.RKTableau.id`
OpenMath/Chapter3/Section381.lean:3472:24: error(lean.unknownIdentifier):
  Unknown identifier `id_compose_phiEquivalent`
OpenMath/Chapter3/Section381.lean:3486:62: error(lean.unknownIdentifier):
  Unknown constant `OpenMath.Chapter3.Section312.RKTableau.id`
OpenMath/Chapter3/Section381.lean:3491:24: error(lean.unknownIdentifier):
  Unknown identifier `compose_id_phiEquivalent`
```

Root cause: forward references. The cycle 234 ingredient lemmas live
later in the file than cycle 233's `composeQ_phi_assoc`:

| Symbol                            | Line in `Section381.lean` |
| --------------------------------- | ------------------------- |
| `composeQ_phi` (cycle 232)        | 3393                      |
| `composeQ_phi_mk` (cycle 232)     | 3410                      |
| `composeQ_phi_assoc` (cycle 233)  | 3447 (strategy template)  |
| `def RKTableau.id`                | 3747                      |
| `id_compose_phiEquivalent` (228)  | 3934                      |
| `compose_id_phiEquivalent` (229)  | 3980                      |
| `composeQ_phi_left_act_id_right`  | 4002                      |

Lean enforces a strict top-down declaration order — a theorem at
line 3470 cannot reference a `def` at line 3747 or a `theorem` at
line 3934.

**Fix**: I inserted the two new theorems immediately after cycle 229's
`composeQ_phi_left_act_id_right` at line 4008 (still inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, which closes at
line 4354). At that location all ingredients are in scope and the
file compiles axiom-clean.

This is **not** a deviation from the cycle 234 mathematical objective
(which is unchanged: ship the two identity axioms via the cycle 219
template). It is a placement correction. The lesson for cycle 235+
strategy authoring: when the proof of theorem T at line N depends on
symbol S, check whether S is declared at line < N before stating
"insert T immediately after `<sibling-theorem>` at line K". A line
number K < line_of(S) makes the strategy template uncompilable.

## Faithfulness check

For each new theorem introduced this cycle:

### `composeQ_phi_id_left` / `composeQ_phi_id_right`

- **Entity ID**: `thm:384A` (Butcher §384, p. 311 — "A homomorphism
  between two groups"). The cycle 234 deliverables ship piece (b) of
  the three-axiom `Group` package on the codomain
  `Quotient PhiEquivalent.setoidSigma`; the full `thm:384A` is the
  homomorphism Φ as a `MonoidHom`, which requires all three group
  axioms (associativity ✓ cycle 233, identity ✓ cycle 234, inverse
  cycle 235+) plus a `Multiplicative.ofAdd`-style packaging.

- **Textbook statement (quoted from `formalization_data/entities/thm_384A.json`)**:
  > "Let $\Phi : T \to \mathbb{R}$ be the elementary weight function
  > associated with $(A, b, c)$ and $\widetilde{\Phi} : T \to \mathbb{R}$
  > the elementary weight function associated with
  > $(\widetilde{A}, \widetilde{b}, \widetilde{c})$. Let
  > $\widehat{\Phi} : T \to \mathbb{R}$ denote the elementary weight
  > function for the product method as represented by (382a). Then
  > $\widehat{\Phi} = \Phi \widetilde{\Phi}.$"

- **Lean statement captures**: weaker — same shape as cycle 233
  (associativity-axiom-only). Cycle 234 ships only the **identity
  axiom** of the codomain `Group`, not the full homomorphism Φ
  itself. The status in `lean_status.json` remains `partial`.

- **Justification for divergence**: per cycle 234 strategy §H, the
  `Group` instance is a multi-cycle deliverable. Cycle 233 shipped
  associativity, cycle 234 ships identity, cycle 235+ ships inverse,
  cycle 237+ packages the `Group` instance via `Group.ofLeftAxioms`,
  and cycle 238+ ships Φ as a `MonoidHom` proper. Splitting matches
  cycle 218–222's §382 group-construction sequence (cycle 219
  identity → cycle 220 inverse → cycle 221 associativity →
  cycle 222 `instance Group`).

- **Tautology check**: ✓ pass. P1.1 / P1.2 hypotheses are bare
  `q : Quotient PhiEquivalent.setoidSigma`; conclusions are equalities
  involving `⟦⟨0, RKTableau.id⟩⟧` and `composeQ_phi`. No conclusion
  appears verbatim as a hypothesis.

- **Identity-only proof check**: ✓ pass. Bodies are
  `Quotient.inductionOn` + `Quotient.sound` (id_compose_phiEquivalent M)
  / (compose_id_phiEquivalent M). These do real definitional work:
  extracting a representative, applying the underlying PhiEquivalent
  lemma at that representative, lifting back via `Quotient.sound`.
  Not a single `exact h` re-export of a hypothesis.

- **Hypothesis strength check**: ✓ pass. Minimal — just a bare
  quotient class. No Lipschitz, smallness, normedness, or other
  auxiliary constraints.

- **Definition smuggling check**: ✓ pass. No new `class` or
  `structure` introduced this cycle.

- **Absent theorem check**: ✓ pass. Both theorems are real, not
  promises in comments.

## Dead ends

**Insertion at line 3454** (strategy template default): failed at
compile with four `unknownIdentifier` errors (see "Strategy correction"
above). Fixed by relocating to line 4009.

## Discovery

1. **Strategy ⨯ Lean declaration order is fragile.** The cycle 234
   strategy template said "insert after cycle 233's `composeQ_phi_assoc`",
   which would have been correct if `RKTableau.id` and the cycle
   228/229 lemmas lived earlier in the file. They don't. The strategy
   author likely assumed the cycle 234 theorems would live in the
   same "quotient-level axioms" cluster as cycle 233's
   `composeQ_phi_assoc`, but cycle 228/229 placed the underlying
   PhiEquivalent lemmas after `RKTableau.id` (which is itself at
   line 3747). Future strategies that prescribe an exact insertion
   line should verify it via a forward-reference scan.

2. **`show Quotient.mk _ _ = Quotient.mk _ _` reframing handles
   `composeQ_phi`'s `Quotient.lift₂` definitional unfolding cleanly**
   — no `composeQ_phi_mk` / `Quotient.lift₂_mk` simp lemma needs to
   be invoked manually. This matches cycle 219's `composeQ_id_left`
   template (which used `composeQ` defined via `Quotient.lift₂` at
   the §382 Equivalent level) and cycle 233's `composeQ_phi_assoc`
   (which lifted through the cycle 232 `composeQ_phi`). The cycle
   234 strategy §E.6 was correct to forbid `Quotient.lift₂_mk` in
   the proof body.

3. **The cycle 232 simp lemma `composeQ_phi_eq_left_act_mk` did not
   need to fire** — `show Quotient.mk _ _ = Quotient.mk _ _` reduces
   both sides far enough that `Quotient.sound` against the
   PhiEquivalent witness closes the goal directly.

4. **Warm rebuild stable across the entire cycle 230–234 window**:
   ~6.2–6.5s per cycle, well under the §F.3 60s red-flag threshold.
   The §381 file is now ~4960 lines with two cycle-232 mutual
   inductions (`gen_dws_eq` / `gen_dwsp_eq`), three mutual blocks
   from cycles 224/225/226/228/229/230/231 (`derivativeWeight*` and
   `derivativeWeightWithSrc*`), and ~10 quotient-level theorems.
   Elaboration time has held steady because the new theorems are
   shallow `Quotient.inductionOn` + `Quotient.sound` lifts whose
   per-symbol cost is dominated by the underlying `PhiEquivalent`
   lemma elaboration (already paid at the underlying-lemma site).

## Suggested next approach

**Cycle 235 (per strategy §J.235)**: ship `inverse_phiEquivalent_inverse`
— `PhiEquivalent M M' → PhiEquivalent M.inverse M'.inverse`. Likely
requires showing equality of `M.inverse.elementaryWeight t` and
`M'.inverse.elementaryWeight t` for all trees `t`, given equality of
`M.elementaryWeight t` and `M'.elementaryWeight t`. Strong Aristotle
candidate — submit early in the cycle with a sorry-first scaffold,
then sleep 30 minutes per the Aristotle-first protocol.

**Cycle 236**: inverse absorption laws on `composeQ_phi` (analog of
cycle 220's `composeQ_inverse_{left,right}`). Requires cycle 235 +
either (a) a closed-form for `M.inverse`'s `derivativeWeightWithSrc`
or (b) a `MonoidHom`-style argument via Φ on its codomain. The §382
analog at cycle 220 used path (a) via direct stage-tuple inversion;
the §383 analog may be smoother via path (b) once Φ is defined.

**Cycle 237+**: `instance : Group (Quotient PhiEquivalent.setoidSigma)`
via `Group.ofLeftAxioms` (analog of cycle 222's §382 group instance),
consuming associativity (✓ cycle 233), identity
(✓ cycle 234), and inverse (cycle 235–236).

**Cycle 238+**: Φ as a `MonoidHom`, closing `thm:384A` proper.

**Strategy authoring note for cycle 235**: please verify the
declaration order of ingredient symbols (in particular, where
`inverse` is defined and where the inverse-related PhiEquivalent
lemmas live) **before** prescribing an exact insertion line. The
cycle 234 strategy template's line-3454 placement would have failed;
cycle 235 should not repeat this miss.
