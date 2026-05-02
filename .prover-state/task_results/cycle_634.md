# Cycle 634 Results

## Worked on

§521 LMM-side iff A-stability bridge in `OpenMath/LMMAsGLM.lean`.
Strategy targeted four sub-targets:

1. `LMM.toGLM_stabilityMatrix_cross_block_zero` (sorry-free)
2. `LMM.toGLM_stabilityMatrix_natAdd_natAdd_shift` (sorry-free)
3. `LMM.toGLM_stabilityMatrix_charpoly_factor` (sorry-first scaffold)
4. `LMM.toGLM_isAStable_iff` headline + both directions

## Approach

Opened a new `## §521 — LMM-side iff bridge` section at the end of
`OpenMath/LMMAsGLM.lean` and re-opened `namespace LMM` for the four
new declarations.

For sub-targets 1 and 2, used `toGLM_stabilityMatrix_apply` (cycle 615)
to split the entry as `Vℂ + z · (Bℂ · resolvent · Uℂ)`, then evaluated
the `V` and `B` blocks via the existing simp lemmas (`toGLM_V_castAdd_shift_apply`,
`toGLM_V_natAdd_shift_apply`) plus a hand-rolled `B`-row evaluation
through the `Fin.addCases` / cast cancellation pattern matching cycle
616's `V`-row projections. The non-stage-row hypothesis
`(j : ℕ) + 1 ≠ s` makes both the `B` row entry and the `V` cross-block
entry vanish: the V-block needs `omega` to rule out the off-by-one
collision (`(j:ℕ) + 1 < s ≤ s + (k:ℕ)`).

For sub-target 4, the forward direction expands `(X^s · q).IsRoot μ`
to `μ^s = 0 ∨ q.eval μ = 0`. The first branch needs a `Nat.eq_zero_or_pos`
case split on `s` (the `s = 0` case forces `1 = 0`, impossible); the
second branch invokes `hroots` and `hm`. The reverse direction is a
direct rewrite: a stability poly root gives a `q` root, hence a charpoly
root.

The iff is then a one-liner pairing the two directions.

## Result

**SUCCESS** — five sorry-free new theorems landed:

* `LMM.toGLM_stabilityMatrix_cross_block_zero`
* `LMM.toGLM_stabilityMatrix_natAdd_natAdd_shift`
* `LMM.toGLM_isAStable_of_isAStable`
* `LMM.isAStable_of_toGLM_isAStable`
* `LMM.toGLM_isAStable_iff`

Plus one sorry-first scaffold:

* `LMM.toGLM_stabilityMatrix_charpoly_factor`

The file compiles with exactly one `declaration uses sorry` warning,
on `toGLM_stabilityMatrix_charpoly_factor`, which is the strategy-
designated structural identity.

`OpenMath/RKAsGLM.lean` and `OpenMath/GeneralLinearMethod.lean` both
recompile cleanly (no regressions in dependent files).

## Dead ends

None: the strategy laid out the sub-targets in the right order. The
only friction was that there was no existing `Bℂ`-row simp lemma —
had to inline a small `B`-row evaluation in each of sub-targets 1 and 2.

## Discovery

* `toGLM_V_castAdd_shift_apply` and `toGLM_V_natAdd_shift_apply`
  (cycle 616) compose cleanly with `toGLM_stabilityMatrix_apply`
  (cycle 615) to give a parametric-in-`s` block-shape lemma; the
  cycle 632 `bdf2_toGLM_isAStable` `fin_cases <;> simp` template was
  not needed for sub-targets 1 and 2 — the existing simp lemmas
  already handle the non-stage rows uniformly.
* For an LMM-as-GLM with stage matrix `1 × 1`, the resolvent factor
  in `toGLM_stabilityMatrix_apply` lives entirely in the `Bℂ k 0 ·
  resolvent · Uℂ 0 l` term; this means a non-stage row with `Bℂ k 0
  = 0` kills the entire `z`-dependent contribution regardless of
  the resolvent or `Uℂ` blocks. That's what makes sub-targets 1 and
  2 land in ~30 lines each instead of ~100.
* The headline iff splits cleanly into two `LMM.toGLM_isAStable_*`
  directions, each ~10 lines, conditional on the open
  `toGLM_stabilityMatrix_charpoly_factor` sorry. The forward direction
  needs a tiny `s = 0` case-split because `μ ^ 0 = 1` cannot vanish.

## Suggested next approach

The remaining open sorry is `LMM.toGLM_stabilityMatrix_charpoly_factor`:

```
∃ q : Polynomial ℂ,
  (m.toGLM.stabilityMatrix z).charpoly = Polynomial.X ^ s * q ∧
  ∀ μ : ℂ, q.IsRoot μ ↔ m.stabilityPoly μ z = 0
```

The structural recipe is:

1. **Reindex**: build a `Fin (2 * s) ≃ Fin (s + s)` equiv (via
   `Fin.cast (Nat.two_mul s)`) so that the index split lines up with
   `Matrix.fromBlocks`.
2. **Block decomposition**: write `Matrix.scalar (Fin (2 * s)) μ −
   m.toGLM.stabilityMatrix z` (under the equiv) as
   `Matrix.fromBlocks A_block 0 C_block D_block`, where
   - `A_block : Matrix (Fin s) (Fin s) ℂ` carries the past-y rows
     (mostly the LMM recurrence + the resolvent stage factor on the
     last row),
   - the upper-right block is zero by
     `toGLM_stabilityMatrix_cross_block_zero` (with the stage-row
     orientation issue resolved — the strategy notes it lands in the
     transposed view, so the upper-right block of the natural
     ordering is zero on both stage and non-stage past-y rows for
     the past-h·f columns; verify this before hand-coding),
   - `D_block : Matrix (Fin s) (Fin s) ℂ` is `μ · I − S` where `S` is
     the strict shift register (sub-target 2 gives the entries);
     `D_block` is upper triangular with diagonal `μ`, so
     `D_block.det = μ ^ s`.
3. **Determinant**: apply `Matrix.det_fromBlocks_zero₁₂`:
   `det = A_block.det · D_block.det = A_block.det · μ ^ s`.
4. **Identify q**: take `q := <polynomial whose evaluation at μ is
   A_block.det as a function of μ>`. Concretely, `q μ` should be a
   nonzero scalar multiple of `m.stabilityPoly μ z` (the scalar is
   `(m.α (Fin.last s) − z · m.β (Fin.last s))^s` per the strategy,
   though the cycle 632 `s = 2` case suggests it may be just
   `(m.α (Fin.last s) − z · m.β (Fin.last s))` rather than to the
   `s`-th power — re-derive this carefully).
5. **Roots**: a nonzero scalar multiple of `m.stabilityPoly μ z`
   has the same roots in `μ`, modulo the scalar being nonzero
   (which it is on a Zariski-open set; for A-stability we only care
   about the closed left half-plane minus the finite scalar-vanishing
   set, which is dealt with by a `μ` continuity argument).

This is the ~300-line piece the strategy flagged. A reasonable cycle
635 plan: tackle sub-step 1 + sub-step 2 (just the upper-right zero
block reindexed reduction), leaving sub-step 3+4+5 for cycle 636.

Do **not** add another concrete LMM A-stability transport before
the charpoly factor lands.

## Files touched

* `OpenMath/LMMAsGLM.lean` (1603 → 1777 lines, well under the 3000-
  line cap)
* `plan.md` (§521 entry updated with cycle 634 deliverables)
