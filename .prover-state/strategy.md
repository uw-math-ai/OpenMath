# Cycle 242 strategy — ship `thm:523B` (inequality form of §523)

## Summary

Cycle 241 shipped the algebraic-stability **identity**
`GeneralLinearMethod.algebraicStability_identity` axiom-clean in
`OpenMath/Chapter5/Section523.lean`. The natural one-cycle follow-up
is `thm:523B`, the **inequality** corollary:

> If `M = algebraicStabilityMatrix D G` is positive semi-definite,
> and the step is dissipative (`⟨hF, Y⟩_D ≤ 0`), then
> `‖y_next‖²_G ≤ ‖y_prev‖²_G`.

This closes a textbook landmark in 1 cycle, axiom-clean, sorry-clean,
≈40 LOC. **Score-2 candidate.**

## Priority 0 — GPFS smoke test (skip)

The §441 GPFS path has timed out 44 consecutive times since cycle 182.
Per `.prover-state/issues/cycle_182_gpfs_slowness.md` this is
loop-maintainer territory; the worker MUST NOT attempt the
`OpenMath/Chapter4/Section441.lean` smoke test this cycle. Skip
directly to Priority 1.

## Priority 1 — ship `thm:523B` inequality form

### Target

Add a new public theorem
`GeneralLinearMethod.algebraicStability_inequality` to
`OpenMath/Chapter5/Section523.lean`, placed immediately after
cycle 241's `algebraicStability_identity` (before the non-vacuity
`example` block).

### Proposed signature

```lean
/-- **Theorem 523B** (Butcher §523, p. 428) — *Non-linear stability
of a general linear method.*

If the algebraic-stability block matrix `M(D, G)` is positive
semi-definite, `D` is symmetric, and the step is dissipative
(`⟨hF, Y⟩_D ≤ 0`), then `‖y_next‖²_G ≤ ‖y_prev‖²_G`.

**Faithfulness note**: Butcher's textbook statement says "if M is
PSD, then ‖y_next‖²_G ≤ ‖y_prev‖²_G". The dissipativity hypothesis
`⟨hF, Y⟩_D ≤ 0` is implicit in Butcher's §357/§523 framing (the
underlying ODE must be monotone/dissipative for non-linear stability
to make sense — same convention as B-stability and algebraic
stability in §357). We surface it as an explicit hypothesis. -/
theorem GeneralLinearMethod.algebraicStability_inequality
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (hM_psd : (M.algebraicStabilityMatrix D G).PosSemidef)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j)
    (hDiss : (fun i => h * F i) ⬝ᵥ (D *ᵥ Y) ≤ 0) :
    y_next ⬝ᵥ (G *ᵥ y_next) ≤ y_prev ⬝ᵥ (G *ᵥ y_prev) := by
  have hId := M.algebraicStability_identity D G hD h F Y y_prev y_next hStage hOut
  -- Apply PSD: M-quadratic form is ≥ 0.
  have hMq :
      0 ≤ (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
    have := hM_psd.dotProduct_mulVec_nonneg
      (Sum.elim (fun i => h * F i) y_prev)
    -- `star x = x` for real x; collapse via `simpa`.
    simpa using this
  linarith
```

### Proof recipe (concrete)

1. Apply cycle 241's `algebraicStability_identity` to obtain the
   equality
   `y_next ⬝ᵥ (G y_next) = y_prev ⬝ᵥ (G y_prev) + 2⟨hF, Y⟩_D − ‖hF⊕y_prev‖²_M`.
2. Apply `Matrix.PosSemidef.dotProduct_mulVec_nonneg` (verified
   present at `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:298`
   with signature
   `hM : M.PosSemidef → ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x)`) to get the
   M-quadratic-form non-negativity.
3. Bridge `star x = x` for real-valued `x : Fin s ⊕ Fin r → ℝ` via
   `simpa` (real has `TrivialStar` ⇒ `star x = x` reduces by `simp`
   under the default simp set). If `simpa` does not collapse `star`
   cleanly, fall back to `show 0 ≤ ... ⬝ᵥ ...; exact this` after
   a `Pi.star_apply` rewrite.
4. Discharge the final inequality via `linarith` from the three
   named facts:
   * `hId` gives `LHS = RHS + 2·hF·D·Y − M_quad` (equality).
   * `hDiss` gives `hF·D·Y ≤ 0`.
   * `hMq` gives `0 ≤ M_quad`.
   These three combine algebraically to `LHS ≤ RHS`, which is
   exactly what `linarith` handles.

### Estimated LOC

≈25 LOC for the theorem + docstring; ≈15 LOC for the non-vacuity
`example` (see Priority 2). Total ≈40 LOC.

## Priority 2 — non-vacuity witness

Add an `example` at `(s, r) = (1, 1)` `explicitEulerGLM` with
`D = Matrix.diagonal (fun _ => d)` and `G = Matrix.diagonal (fun _ => g)`.
PSD of the block matrix `algebraicStabilityMatrix D G` at this concrete
GLM will be passed as a hypothesis (preferred — keeps the witness
lightweight; constructing PSD of the concrete block matrix is a
separate off-path calculation).

Suggested shape:

```lean
example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hPSD : (explicitEulerGLM.algebraicStabilityMatrix
              (Matrix.diagonal (fun _ : Fin 1 => d))
              (Matrix.diagonal (fun _ : Fin 1 => g))).PosSemidef)
    (hStage : ∀ i, Y i = h * (∑ j, explicitEulerGLM.A i j * F j)
                    + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, explicitEulerGLM.B i j * F j)
                    + ∑ j, explicitEulerGLM.V i j * y_prev j)
    (hDiss : (fun i => h * F i) ⬝ᵥ
             (Matrix.diagonal (fun _ : Fin 1 => d) *ᵥ Y) ≤ 0) :
    y_next ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_next)
      ≤ y_prev ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_prev) :=
  explicitEulerGLM.algebraicStability_inequality _ _
    (Matrix.isSymm_diagonal _) hPSD h F Y y_prev y_next hStage hOut hDiss
```

Taking `hPSD` as a hypothesis avoids the digression of constructing a
concrete PSD witness (which would require evaluating
`algebraicStabilityMatrix` at `s = r = 1` and proving the resulting
`2 × 2` matrix is PSD — a separate, off-topic calculation). This is
the standard pattern for non-vacuity witnesses that exercise the
typing of a hypothesis-heavy theorem, and mirrors cycle 241's own
example pattern (which similarly takes `hStage`/`hOut` as hypotheses
rather than constructing concrete witnesses).

## Priority 3 — verify and ship

1. `cd /mmfs1/gscratch/amath/mathai/butcher_exp_2`
2. `time timeout 180 lake env lean OpenMath/Chapter5/Section523.lean`
   — expect <60s (warm cache from cycle 241).
3. If clean: `time timeout 300 lake env lean OpenMath/Chapter5.lean`
   to confirm whole-chapter integrity.
4. **Axiom check** via `lean_verify`:
   `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_inequality`
   → expect `[propext, Classical.choice, Quot.sound]` only.
5. Confirm `grep -c sorry OpenMath/Chapter5/Section523.lean` returns `0`.

## Priority 4 — bookkeeping

* Update `extraction/formalization_data/lean_status.json`:
  add `thm:523B` row with `status: "formalized"`,
  `cycle: 242`, `file: "OpenMath/Chapter5/Section523.lean"`,
  `lean_symbol: "OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_inequality"`.
* Update `plan.md`: change `thm:523B`'s Chapter 5 row from
  `[ ]` to `[x]` with a one-line cycle-242 closure note.
* Write `.prover-state/task_results/cycle_242.md` per CLAUDE.md
  template (Worked on / Approach / Result / Faithfulness check /
  Dead ends / Discovery / Suggested next approach).

## What NOT to try this cycle

* **DO NOT** touch `OpenMath/Chapter4/Section441.lean` or attempt
  Phase C of `lem:441A`. 44 consecutive GPFS timeouts since cycle
  182 (see `.prover-state/issues/cycle_182_gpfs_slowness.md`).
* **DO NOT** attempt a constructive PSD witness for
  `explicitEulerGLM.algebraicStabilityMatrix` at the
  `(s, r) = (1, 1)` non-vacuity example. Take `hPSD` as a
  hypothesis (cleaner; off-path).
* **DO NOT** strengthen `D` to `D.PosSemidef`. Cycle 241's identity
  only needs `D.IsSymm`, and the inequality form only needs `D.IsSymm`
  plus the explicit `hDiss` hypothesis. Adding `D.PosSemidef` is a
  redundant strengthening (doesn't unlock anything in this proof
  body) and creates a faithfulness divergence from cycle 241.
* **DO NOT** fold the dissipativity hypothesis into the PSD
  hypothesis (e.g. by stating PSD of a larger block matrix that
  combines `M` and `D` somehow). The textbook keeps these
  conceptually distinct: M-PSD is a method-property; dissipativity
  is an IVP-property.
* **DO NOT** try to remove the step-equation hypotheses `hStage`,
  `hOut` (e.g. by re-coupling to `IsGLMSolution`). Cycle 241's
  decoupling was deliberate and pays off here — cycle 242 inherits
  the same explicit step equations without re-deriving anything.
* **DO NOT** attempt §302 (`thm:302C` Cayley) or §324 (any of the
  three RK order theorems). Both require multi-cycle rooted-tree
  combinatorial infrastructure NOT yet in `Section310.lean`. Single-
  cycle workers should prefer §523/§520/§521.
* **DO NOT** try `simp [PosSemidef]` or any tactic that unfolds
  PSD's definition. Use the API lemma `dotProduct_mulVec_nonneg`
  directly; PSD's underlying `IsHermitian ∧ ∀ x, ...` shape is not
  needed.
* **DO NOT** invoke `Matrix.PosSemidef.re_dotProduct_nonneg` —
  that variant is for ℂ-valued matrices. For real matrices use
  `dotProduct_mulVec_nonneg` directly.

## Known pitfalls (from cycle 241 task results)

* `dotProduct` lives at root namespace (not `Matrix.dotProduct`).
  Drop the `Matrix.` prefix when accessing dot-product lemmas
  (`add_dotProduct`, `dotProduct_add`, `dotProduct_comm`, etc.).
* `Matrix.mulVec_transpose : Aᵀ *ᵥ x = x ᵥ* A` (the direction may
  be unexpected). Not directly needed for thm:523B's proof, but
  flagging in case the `star x = x` bridge gets stuck and needs
  manual reformulation.
* `simpa` on the `star x ⬝ᵥ ... = x ⬝ᵥ ...` step should work because
  `ℝ` has a `TrivialStar` instance and `star_trivial` is a default
  simp lemma. If it doesn't fire, try `simpa [star_trivial]` or
  `simpa using ... |>.symm.le` after a manual `star` evaluation. As
  a last resort, prove a local helper
  `have hstar : star (Sum.elim α y_prev) = Sum.elim α y_prev := by
    funext i; cases i <;> rfl`
  and `rw [hstar] at this`.

## Stretch (only if Priority 1+2+3+4 ship cleanly with > 30 min budget)

If everything above lands and there's substantive time remaining,
ship one of:

(a) **`thm:523B` residual form helper** — Cycle 241's identity also
    produces a **residual** form
    `‖y_next‖²_G − ‖y_prev‖²_G = 2⟨hF, Y⟩_D − ‖hF ⊕ y_prev‖²_M`
    that is sometimes useful downstream. Add this as a small public
    helper theorem `algebraicStability_residual` (~15 LOC, direct
    `linarith` from the identity). Low-risk add-on if budget permits.

(b) **Skip the stretch and ship.** Score-2 deliverable does not
    need padding. If Priority 1+2+3+4 lands at any point during
    the cycle, COMMIT IMMEDIATELY. Do not chase additional content
    once the primary score-2 ship is secured.

Recommend (b) by default. Choose (a) only if Priority 1+2+3+4 lands
within the first half of the cycle budget.

## Estimated cycle outcome

* Sorry count: 0 → 0 (no new sorries).
* Axiom-clean count: +1 theorem axiom-clean.
* `lean_status.json` rows updated: +1 (`thm:523B` formalized).
* `plan.md` Ch.5 §523 row: `[ ]` → `[x]`.
* Progress: 71/175 → 72/175.
* Risk: very low. The proof recipe is fully concrete, uses one
  Mathlib API call (`dotProduct_mulVec_nonneg`) verified present
  this cycle, and `linarith` will close the final inequality from
  three named hypotheses.
