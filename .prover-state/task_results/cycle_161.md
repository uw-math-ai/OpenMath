# Cycle 161 Results

## Worked on
`def:530B`/`def:530C` Path A r = 4 mechanical lift (Backup A from
cycle 161 strategy). Lifted cycle 159's r = 3 non-vacuity grid for
`HasOrderRelativeTo_explicit` and `HasOrder_explicit` to r = 4 by
mirroring the cycle 159 deliverables verbatim.

## Approach
Mechanical port of cycle 159's r = 3 templates to r = 4:

1. **Step 2 — Section520**: added `padded4DEulerGLM`
   `(s, r) = (1, 4)` immediately after `padded3DEulerGLM`. V matrix
   `!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]` with row 0
   active and rows 1, 2, 3 zero. Same row-padding scheme as cycles
   133/159.

2. **Step 3 — Section530 infrastructure**: added five new
   declarations after the cycle 159 r = 3 templates:
   - `pad4CompatMethod : Fin 4 → GeneralizedRungeKuttaMethod 1`
     (index 0 → trivialGeneralizedRK, indices 1, 2, 3 →
     zeroGeneralizedRK).
   - `pad4CompatStartingMethod : StartingMethod 4`.
   - `pad4CompatStartingMethod_isNonDegenerate` via index 0
     (b₀ = 1 ≠ 0).
   - `pad4CompatStartingMethod_constituents_isExplicit` via
     `fin_cases i` + four arms (one trivial, three
     zeroGeneralizedRK).
   - `padded4DEulerGLM_isExplicit` (1×1 zero `A`-block, vacuous).
   - `pad4CompatStartingMethod_applyExplicit` (closed form
     `![y₀ + h·f y₀, 0, 0, 0]`, four `fin_cases` arms reusing
     existing `trivialGeneralizedRK_explicitApply` and
     `zeroGeneralizedRK_explicitApply`).

3. **Step 4a — p = 0 witness**:
   `padded4DEulerGLM_hasOrderZero_pad4CompatStarting`. Four
   `fin_cases` arms:
   - i = 0: SM[0] and ES[0] closed forms reduce to the cycle-160
     helper input shape via `simp [padded4DEulerGLM, Matrix.mulVec,
     dotProduct, Fin.sum_univ_four]`. One-line invocation of
     `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO` after
     `h^(0+1) = h` collapse.
   - i ∈ {1, 2, 3}: SM[i] = 0 and ES[i] = 0; difference identically
     zero; closed by `Asymptotics.isBigO_zero`.

4. **Step 4b — p = 1 witness**:
   `padded4DEulerGLM_hasOrderOne_pad4CompatStarting`. Four arms:
   - i = 0: same SM[0]/ES[0] closed forms; one-line invocation of
     `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` (cycle
     158 helper) after `h^(1+1) = h^2` collapse.
   - i ∈ {1, 2, 3}: zero-collapse with exponent `h^(1+1)`.

5. **Step 5 — def:530C wrappers**:
   `padded4DEulerGLM_hasOrderZero` and `padded4DEulerGLM_hasOrderOne`
   exhibit `pad4CompatStartingMethod` as the existential witness via
   `refine ⟨..., ?_⟩` + the cycle-161 HasOrderRelativeTo witnesses.

The only material change between the r = 3 templates and the r = 4
versions is `Fin.sum_univ_three` → `Fin.sum_univ_four` and adding
one extra `fin_cases` arm with the same closure body.

## Result
SUCCESS — all nine new declarations compiled and verified
axiom-clean on the first attempt. No closure-shape adjustments
needed beyond the mechanical `Fin.sum_univ_three` →
`Fin.sum_univ_four` swap.

* `lake env lean OpenMath/Chapter5/Section520.lean` exit 0.
* `lake env lean OpenMath/Chapter5/Section530.lean` exit 0.
* `lake env lean OpenMath/Chapter5.lean` exit 0.
* `grep -c sorry OpenMath/Chapter5/Section{520,530}.lean` → 0.
* All nine new declarations report
  `[propext, Classical.choice, Quot.sound]` via `lean_verify`:
  - `padded4DEulerGLM` (Section520.lean — definition)
  - `pad4CompatStartingMethod_isNonDegenerate`
  - `pad4CompatStartingMethod_constituents_isExplicit`
  - `padded4DEulerGLM_isExplicit`
  - `pad4CompatStartingMethod_applyExplicit`
  - `padded4DEulerGLM_hasOrderZero_pad4CompatStarting`
  - `padded4DEulerGLM_hasOrderOne_pad4CompatStarting`
  - `padded4DEulerGLM_hasOrderZero`
  - `padded4DEulerGLM_hasOrderOne`
* Tautology-scanner regex clean on both files.

Path A non-vacuity grid now saturates r ∈ {1, 2, 3, 4} × p ∈ {0, 1}.

## Faithfulness check
The r = 4 lift introduces zero new mathematical content: it is a
parametric extension of cycles 156/159's non-vacuity grid for the
existing entities `def:530B` and `def:530C`. No new textbook-named
concepts; no new `class`/`structure` declarations.

For the new `def`s and theorems:

- **`padded4DEulerGLM`** (def): not a textbook-named concept.
  It is a generic instance of `GeneralLinearMethod 1 4` used
  purely as a non-vacuity witness for `def:530B`/`def:530C`.
  Faithfulness check: vacuous (no textbook divergence to check).

- **`pad4CompatMethod`, `pad4CompatStartingMethod`** (defs): same as
  `pad{2,3}CompatStartingMethod` from cycles 156/159 — generic
  starting-method witnesses, no textbook-named concept introduced.

- **`pad4CompatStartingMethod_isNonDegenerate`,
  `pad4CompatStartingMethod_constituents_isExplicit`,
  `padded4DEulerGLM_isExplicit`,
  `pad4CompatStartingMethod_applyExplicit`** (theorems): all
  closed-form / non-vacuity statements about the new defs above.
  No textbook divergence (no textbook entity these correspond to).

- **`padded4DEulerGLM_hasOrderZero_pad4CompatStarting`,
  `padded4DEulerGLM_hasOrderOne_pad4CompatStarting`,
  `padded4DEulerGLM_hasOrderZero`,
  `padded4DEulerGLM_hasOrderOne`** (theorems): non-vacuity
  witnesses for `def:530B` (the first two) and `def:530C` (the
  wrappers). The witnessed predicates were defined in cycles 153
  and 155, and their faithfulness to Butcher §530, p. 432 was
  established at definition time. These theorems exhibit specific
  inputs (a particular GLM, starting method, and IVP hypothesis
  pack) and assert the predicate holds on them. They do not modify
  the predicate; they witness existence. No faithfulness drift.

  Hypothesis-strength check: the witness signatures match cycle
  159's r = 3 witnesses verbatim:
  - p = 0 witness: `LipschitzWith L f` + `yex x₀ = y₀` +
    `HasDerivAt yex (f y₀) x₀` (matches cycle 159).
  - p = 1 witness: `LipschitzWith L f` + `yex x₀ = y₀` +
    `ContDiff ℝ 2 yex` + `∀ x, HasDerivAt yex (f (yex x)) x`
    (matches cycle 159).

  No hypothesis added or strengthened compared to cycle 159; no
  deviation requires justification.

  Tautology check: no theorem conclusion appears verbatim as a
  hypothesis. Identity check: no proof is `exact h_...` or `:= id`.

## Dead ends
None. The mechanical port worked on the first attempt — the only
non-trivial decision was selecting `Fin.sum_univ_four` to expand
the size-4 V * y_input dot products inside the SM[i] closed-form
rewrites. Verified existence in Mathlib via `grep` before writing.

After the initial Section520 edit, an intermediate Section530 build
failed with "Unknown identifier `padded4DEulerGLM.IsExplicit`"
because the Section520 .olean was stale. A `lake build
OpenMath.Chapter5.Section520` refresh fixed it. Not a real dead
end — just a stale-cache artifact of editing across files.

## Discovery
The r = 4 lift confirms the mechanical-port pattern that cycles
156/159 established: for any new r, adding the (s, r) = (1, r)
padded GLM and matching starting method costs ≈300 LOC of
duplication, but the closure bodies are uniform across r once the
cycle 158 + 160 helpers are in place. Specifically:
- The i = 0 channel is one-line dispatch via the helpers (zero
  per-r work after closed-form rewrites).
- The i ≥ 1 channels are all syntactically identical
  zero-collapses parameterised only by the Fin index.
- The closed-form SM[i] rewrites uniformly use
  `simp [paddedRDEulerGLM, Matrix.mulVec, dotProduct,
  Fin.sum_univ_<r>]`.

This four-data-point baseline (r ∈ {1, 2, 3, 4}) is now sufficient
evidence to commit to the r-parametric refactor. The structural
choice is whether to reformulate the GLM as
`Matrix.of (fun i j => if i = 0 ∧ j = 0 then 1 else 0)` (purely
parametric) or to retain the literal `!![...]` matrices and prove
type-equalities (less pure but reuses existing infrastructure).

## Suggested next approach
Two reasonable options for cycle 162:

1. **r-parametric refactor (option 1 from cycle 161 strategy)**.
   Now that the four-data-point baseline is in place, refactor
   cycles 156/159/161's three pairs of `padded{2,3,4}DEulerGLM` +
   `pad{2,3,4}Compat...` into a single
   `paddedRDEulerGLM (r : ℕ) (hr : 0 < r)` family, with a single
   inductive pair of HasOrderRelativeTo theorems. Phase A
   (definitions + IsExplicit) is ~150 LOC; phase B (witnesses by
   induction on r) is the larger investment. Cycle 138/149 rollback
   precedent argues against sorry-first scaffolding; do this in
   phases, landing each phase axiom-clean.

2. **Pivot to a fresh entity**. The Path A non-vacuity grid is now
   saturated through r = 4 with both p ∈ {0, 1} witnesses. Diminishing
   returns on r = 5 (option 2 again) — each subsequent r adds the
   same ≈300 LOC of duplication with no new mathematical content.
   Better to either:
   - Pivot to a fresh entity (cycle 160 strategy listed
     `def:451A`, `def:422B`, `thm:381G`, `thm:521B` as candidates;
     cycle 161 strategy noted these are multi-cycle but worth
     scouting).
   - Start Path B (implicit method via `ContractingWith`) — also
     multi-cycle but with a clear endpoint per
     `.prover-state/issues/def_530B_scaffold_strategy.md`.

The r-parametric refactor (option 1) consolidates all three padded
GLM pairs and is the highest-leverage cleanup; it is the planner's
recommended next step. If the planner prefers fresh-entity
progress, scout one of the cycle-160 candidates first to confirm
tractability.
