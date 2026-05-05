# Cycle 125 Results

## Worked on

- **Priority 1**: `thm:520B` — Stability Matrix for Linear Differential
  Equation (Butcher §520B, p. 397). Stated and proved
  `GeneralLinearMethod.stabilityMatrix_linearTest_step` plus a
  non-vacuity witness `…_step_at_zero` in
  `OpenMath/Chapter5/Section520.lean`.
- **Priority 2**: hygiene rename `hβ_nn → _hβ_nn` in
  `aux_515D_discrete_gronwall_raw` (Section515.lean:1713) to silence
  the unused-variable warning. The parameter is intentionally kept in
  the signature for API symmetry with the wrapper
  `aux_515D_gronwall_bound`.

## Approach

1. **Aristotle Job A** (project `53f55009-…`) submitted at cycle start
   with the inlined-matrix scaffold of `thm:520B`. Completed in
   ~5 min with a working alternative proof (kept for reference under
   `.prover-state/aristotle_results/cycle_125/`).
2. **Manual proof** authored in parallel using
   - `Matrix.sub_mulVec`, `Matrix.one_mulVec`, `Matrix.smul_mulVec`,
     `nth_rewrite + abel` for Step 1 (`(I − z·A)·Y = U·yPrev`).
   - `Matrix.isUnit_iff_isUnit_det`, `Matrix.nonsing_inv_mul`,
     and `congrArg` for Step 2 (recover `Y = (I − z·A)⁻¹·U·yPrev`).
   - `Matrix.mulVec_mulVec`, `← Matrix.smul_mulVec`, `← Matrix.add_mulVec`,
     `add_comm`, `congr 2`, `Matrix.smul_mul`, and `Matrix.mul_assoc`
     for Step 3 (collapse to `M(z) · yPrev`).
3. The `…_at_zero` non-vacuity witness uses the pre-existing
   `stabilityMatrix_at_zero` (`M(0) = V`) lemma in one rewrite.

## Result

- **SUCCESS** — `OpenMath/Chapter5/Section520.lean` compiles cleanly
  (`lake env lean Section520.lean` returns no diagnostics).
- `#print axioms
  GeneralLinearMethod.stabilityMatrix_linearTest_step` returns
  `[propext, Classical.choice, Quot.sound]` — axiom-clean.
- `#print axioms
  GeneralLinearMethod.stabilityMatrix_linearTest_step_at_zero` likewise
  axiom-clean.
- **Section515.lean** also recompiles cleanly; the `hβ_nn` warning is
  gone. No other code changed.
- `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/` returns
  only the pre-existing Section514.lean:601 line (unchanged this
  cycle). No new tautological identities introduced.

## Faithfulness check

### `thm:520B` (`GeneralLinearMethod.stabilityMatrix_linearTest_step`)

- Entity ID: `thm:520B`. Textbook statement (quoted from
  `entities/thm_520B.json`):
  > "Let M(z) denote the stability matrix for a general linear
  > method. Then, for a linear differential equation (520a), (520b)
  > holds with z = hq."
- Lean statement captures: **same content**. The textbook proof
  begins with the substitution `f(y) = qy ⇒ F = qY` and `z = hq`,
  reducing the GLM step to `Y = z·A·Y + U·yPrev`,
  `y^[n] = z·B·Y + V·yPrev`. Our Lean form pre-applies that
  substitution: `hY_stage` *is* the post-substitution stage equation,
  and the conclusion is the post-substitution output identity
  `z·B·Y + V·yPrev = M(z)·yPrev`. Faithfulness preserved.
- **Divergence (documented)**: hypothesis
  `IsUnit (1 - z • complexify M.A)` is added. Justification: our
  `stabilityMatrix` definition (cycle 086) uses `Matrix.inv`, which
  returns the junk-zero on singular matrices. Without invertibility,
  the conclusion is genuinely false (RHS would collapse to `V·yPrev`
  via the junk-inverse). The textbook implicitly restricts attention
  to invertible `(I − zA)`, as flagged in `def:520A`'s docstring
  (Section520.lean:83-88). The hypothesis surfaces this faithfully.
- **Tautology check**: conclusion
  `z • B *ᵥ Y + V *ᵥ yPrev = M.stabilityMatrix z *ᵥ yPrev`
  is NOT verbatim in the hypotheses. `hY_stage` is the stage
  equation, not the output identity. Real work — passes.
- **Hypothesis strength check**: `IsUnit` is the minimal
  invertibility condition; weakening it (e.g., to a non-zero
  determinant predicate) wouldn't add value since `Matrix.inv` is
  defined via determinant invertibility internally.
- **Identity check**: proof is multi-step (15+ tactics), not a
  trivial `exact`. Real work.

### `…_step_at_zero` (non-vacuity witness)

- This is the `z = 0` specialisation: at `z = 0`, the linear-test
  step says `y^[n] = V·y^[n−1]`, and the witness collapses via the
  pre-existing `stabilityMatrix_at_zero` (`M(0) = V`).
- Not an entity in `formalization_data/`; an internal non-vacuity
  check confirming the main theorem reduces correctly at the
  identity case.

### Section515.lean rename (`hβ_nn → _hβ_nn`)

- Pure binder rename. Signature shape preserved (the parameter
  remains in the proof signature for API symmetry). No semantic
  change; the wrapper `aux_515D_gronwall_bound` still passes its own
  `hβ_nn` to the renamed inner argument by position.

## Dead ends

- Initial first attempt at Step 1 used `linear_combination` after
  `Matrix.smul_mulVec_assoc` (a non-existent lemma name; Mathlib has
  `Matrix.smul_mulVec`). Adjusted to the correct lemma name plus
  `nth_rewrite + abel`.
- Initial Step 3 ended with `smul_mul_assoc` and `mul_assoc` (the
  generic algebraic forms). These don't apply because `B`, `(1−z·A)⁻¹`,
  `U` are heterogeneous matrices (different `Fin` index types), so
  the `Mul β` typeclass on a single carrier doesn't fire. Replaced
  with `Matrix.smul_mul` and `Matrix.mul_assoc` — the
  rectangular-matrix-aware variants. Both forward-direction rewrites
  worked once the right lemma names were used.
- `congr 1` after `add_comm` left `(z • B * (M⁻¹ * U)) = (z • B * M⁻¹ * U)`;
  needed `congr 2` to peel the smul-by-`z` and reach the inner matrix
  equality.

## Discovery

- For heterogeneous matrix products (`B : Matrix (Fin r) (Fin s) ℂ`,
  `M⁻¹ : Matrix (Fin s) (Fin s) ℂ`, `U : Matrix (Fin s) (Fin r) ℂ`),
  the generic `mul_assoc` / `smul_mul_assoc` algebraic lemmas don't
  apply — `Mul β` is a homogeneous typeclass. Use Mathlib's
  rectangular-aware `Matrix.mul_assoc` and `Matrix.smul_mul` instead.
  `Matrix.Mul.lean:482` (`protected theorem mul_assoc (L : Matrix l m α)
  (M : Matrix m n α) (N : Matrix n o α) : L * M * N = L * (M * N)`).
- `Matrix.smul_mulVec : (b • M) *ᵥ v = b • M *ᵥ v` (rather than the
  `_assoc` variant which doesn't exist in Mathlib for `mulVec`).
- The `congrArg (fun w => M⁻¹ *ᵥ w) h_stage_solved` pattern is the
  cleanest way to apply `M⁻¹` on the left of an equality of
  matrix-vector products without re-deriving the action via
  `mulVec_mul`.

## Suggested next approach

Per cycle 125 strategy's Priority 3 plan:

1. **`thm:520D`** (Instability Region Boundary Characterization) is
   the last open §520 theorem. Requires a power-bounded ↔ spectral
   radius < 1 bridge for matrices. Mathlib has the spectral-form
   version in `Mathlib.Analysis.NormedSpace.Spectrum` for general
   Banach algebra elements; `Matrix.linfty_op_spectralRadius` or a
   Gelfand-formula application is the bridge. **Recommend**: file
   an issue documenting the Mathlib gap before attempting. Likely
   2–3 cycles.
2. **`thm:550A`** (Doubly companion matrices, §550): requires the
   doubly-companion-matrix data structure plus polynomial-coefficient
   extraction (550b). Multi-cycle infrastructure investment.
3. **`thm:521B`** (Maximum stability order for given complexity
   sequence ν): requires re-encoding `stabilityFunction` as
   `Polynomial (Polynomial ℂ)` and the `complexity sequence`
   apparatus from §521A. Multi-cycle.
4. **Bonus hygiene**: 5+ unused-simp-arg / unused-tactic warnings
   remain in Section515.lean (lines 2218, 2640, 2677, 2845). One
   surgical cycle could clean these for a "0 warnings"
   regression baseline.
5. **Forward**: §523, §530, §540 stability theorems — start whichever
   has the cleanest dependency chain into existing definitions.
