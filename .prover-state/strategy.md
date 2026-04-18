# Strategy — Cycle 110

## Status
- **0 sorry's** in the entire codebase — the project is sorry-free as of cycle 109.
- Last commit: `969bc8a` (close Padé approximation order polynomial proof).
- All existing theorems compile.

## What to work on

Since there are no sorry's, the cycle advances to **new formalization**. The plan.md
lists three in-progress items plus the broader textbook to draw from.

### Priority 1: Theorem 356C — AN-stability necessary conditions

**Why this**: It is the natural next theorem in Chapter 3's stability theory. It
is self-contained (zero formal dependencies in the extraction graph), has a clean
textbook proof, and builds on the existing algebraic stability infrastructure in
`OpenMath/RungeKutta.lean`. It connects to the existing `IsAlgebraicallyStable`
definition via the matrix `M = diag(b)A + Aᵀ diag(b) − bbᵀ`.

**What it says**: An implicit RK method is AN-stable only if:
1. `bⱼ ≥ 0` for all j
2. The matrix `M = diag(b)A + Aᵀ diag(b) − bbᵀ` is positive semi-definite

**Where to put it**: `OpenMath/RungeKutta.lean` (extend the existing algebraic
stability section) or a new `OpenMath/ANStability.lean` if the file is already
too long.

**Approach**:

1. **Define AN-stability** for an RK method acting on the test equation
   `y' = Zy` where `Z = diag(z₁, …, zₛ)` with `Re(zᵢ) ≤ 0`:
   ```
   IsANStable t := ∀ Z : Matrix (Fin s) (Fin s) ℂ,
     Z.IsDiag → (∀ i, (Z i i).re ≤ 0) →
     ‖stabilityFunctionMatrix t Z‖ ≤ 1
   ```
   where `R(Z) = 1 + bᵀ Z (I − AZ)⁻¹ 𝟏`.

2. **Prove the necessity of `bⱼ ≥ 0`**: Choose `Z = −t · diag(eⱼ)`.
   Then `R(Z) = 1 − t bⱼ + O(t²)`. If `bⱼ < 0`, then `|R(Z)| > 1`
   for small positive `t`.

3. **Prove the necessity of `M ≥ 0`**: Choose `Z = it · diag(v)` with
   `v ∈ ℝˢ`. Expand `|R(Z)|² = 1 − t² vᵀ M v + O(t³)`. If `M` is
   not positive semi-definite, choose `v` with `vᵀ M v < 0` to get
   `|R(Z)|² > 1`.

4. **Sorry-first**: Write the full structure with sorry at each step.
   Verify it compiles. Then close sorry's one by one.

5. **Submit to Aristotle**: Batch ~5 sub-lemmas (matrix expansion, stability
   function series, norm bound). Sleep 30 min. Check once.

### Priority 2 (if Priority 1 finishes early): Theorem 357C — Algebraic stability implies BN-stability

**Why**: It completes the stability equivalence chain: algebraic stability ⇔
AN-stability ⇔ BN-stability. Theorem 356C (Priority 1) provides the AN-stability
direction; 357C provides the BN direction.

**What it says**: If `bᵢ ≥ 0` and `M = diag(b)A + Aᵀ diag(b) − bbᵀ` is positive
semi-definite (algebraic stability), then the method is BN-stable.

**Approach**: The textbook proof uses the quasi-inner product identity
`‖yₙ − yₙ₋₁‖² = 2h Σ bᵢ ⟨Yᵢ, Fᵢ⟩ − h² Σ mᵢⱼ ⟨Fᵢ, Fⱼ⟩`. This is pure
algebraic manipulation — form inner products with the stage equations,
rearrange. The positive semi-definiteness of M makes the second sum non-negative,
and the dissipativity condition ⟨Fᵢ, Yᵢ⟩ ≤ 0 combined with bᵢ ≥ 0 makes the
first sum non-positive.

### Priority 3 (background): Update plan.md

The plan.md is stale. Several items marked `[ ]` or `[~]` are now complete:
- `padeQ_succ_left` and `padeP_succ_right` were proved in cycle 102
- Theorem 352C/352D should be marked `[x]`
- Current Target section needs updating

Update plan.md to reflect reality and add the new Chapter 3 targets.

## What NOT to try

- Do NOT work on Theorem 301A rooted trees (list→multiset upgrade). The payoff
  is low — it unblocks Theorem 342C implications (342j,k,l) which are about
  rooted-tree order conditions, but these require extensive tree-counting
  infrastructure that is far from the current codebase's strengths.
- Do NOT work on Theorem 352E (V-function recurrence). The issue file
  `theorem_352E_v_defect_mismatch` documents that the textbook's V-function
  definition does not match our `padeV` normalization, and the recurrence
  coefficients are wrong for the current setup. This needs a careful reconciliation
  with the textbook before any Lean work.
- Do NOT try to close the Ehle barrier (Theorem 355B). The issue file notes it
  requires winding number theory not available in Mathlib.
- Do NOT revisit any of the old spectral bound / Dahlquist barrier issues.
  Those theorems are now proved and sorry-free.
- Do NOT spend time on build environment / toolchain issues. If `lake env lean`
  hangs, use the Lean LSP MCP tools (`lean_verify`, `lean_diagnostic_messages`)
  instead.

## Concrete Step-by-Step Plan

1. **Read** `OpenMath/RungeKutta.lean` to understand the existing RK infrastructure
   (ButcherTableau, stability function, algebraic stability definitions).

2. **Read** `extraction/formalization_data/entities/thm_356C.json` for the full
   textbook statement and proof.

3. **Define AN-stability** (`IsANStable`) and the matrix stability function `R(Z)`.

4. **State Theorem 356C** with sorry at each step. Verify compilation.

5. **Submit ~5 Aristotle jobs** on the sorry'd sub-lemmas. Sleep 30 min.

6. **Prove the `bⱼ ≥ 0` direction** manually while waiting:
   - Define `Z = -t * stdBasisMatrix j j 1`
   - Show `R(Z) = 1 - t * bⱼ + O(t²)` using Neumann series for `(I - AZ)⁻¹`
   - Show `|R(Z)| > 1` for small t when `bⱼ < 0`

7. **Check Aristotle results** exactly once after 30 min. Incorporate.

8. **Prove the `M ≥ 0` direction** (or close remaining sorry's).

9. **Verify** all modified files compile via `lean_verify`.

10. **Write task result** to `.prover-state/task_results/cycle_110.md`.

11. **Commit and push**.

## Build Command

```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
lake env lean OpenMath/RungeKutta.lean
```

Or use lean-lsp: `lean_verify` on the file.

## Cycle Completion Checklist

1. Write task results to `.prover-state/task_results/cycle_110.md`
2. Update plan.md with new theorems
3. Verify all modified files compile
4. Commit and push
5. Update `.prover-state/cycle` to `110`
