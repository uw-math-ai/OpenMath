# Cycle 167 Results

## Worked on

* `OpenMath/Chapter4/Section451.lean`: polymorphism refactor of
  `gTopLeft` and `gBottomRight` (ℝ → `{R : Type*} [Zero R]`).
* `OpenMath/Chapter4/Section454.lean`: ten new theorems —
  five private sub-lemmas + the main `gTopLeft_quadForm_eq`,
  five private sub-lemmas + the main `gBottomRight_quadForm_eq`.
* Aristotle project `89e8a962-b3eb-4f7d-b397-c77bf18773d4`
  (carry-over from cycle 166) was at 18% after 80+ minutes;
  cancelled per the strategy's single-poll discipline.

## Approach

Per the planner's Path A (`thm_454A_stage_2_3_stall.md`), the
cycle-166 monolithic proof of `algebraic_identity_454A` stalled
because the §451e quadratic-form identity unfolded
`gTopLeft G *ᵥ W` and `gBottomRight G *ᵥ W` simultaneously inside
one proof body. Lean's elaboration of nested `dif_pos`/`dif_neg`
on `Fin (k+1) × Fin (k+1)` blew up.

Cycle 167's remediation:

1. Refactor `gTopLeft`, `gBottomRight` to be polymorphic in the
   scalar ring `R` (only `[Zero R]` needed). The `gMatrix`
   definition still resolves at `R := ℝ` definitionally; BDF2
   witnesses in `Section451.lean` rebuilt without modification.
2. Add five `private` named sub-lemmas per block embedding,
   each ≤ 5 lines, computing one boundary case:
   * `gTopLeft_apply_castSucc / _last_row / _last_col`
   * `gTopLeft_mulVec_castSucc / _last`
   * Symmetric `gBottomRight_apply_succ / _zero_row / _zero_col`
   * `gBottomRight_mulVec_succ / _zero`
3. Assemble the two main theorems
   `gTopLeft_quadForm_eq` and `gBottomRight_quadForm_eq` from the
   sub-lemmas, splitting the dotProduct sum via
   `Fin.sum_univ_castSucc` (resp. `Fin.sum_univ_succ`) and
   collapsing the boundary term to `0` via the corresponding
   `_last` / `_zero` mulVec lemma.

The `show` tactic was used to expose the underlying
`∑ i, _ * _` representation of dotProduct, since
`simp only [Matrix.dotProduct]` does not fire (the def lives
in the root namespace as `dotProduct`, not `Matrix.dotProduct`).

## Result

**SUCCESS** — both quadratic-form factorisation theorems land
axiom-clean.

```
'OpenMath.Chapter4.Section454.gTopLeft_quadForm_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section454.gBottomRight_quadForm_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`OpenMath.Chapter4.Section451` rebuilt cleanly after the
polymorphism refactor; BDF2 G-stability witness
(`bdf2_gMatrix_eq_smul_vecMulVec`, `bdf2_gMatrix_posSemidef`,
`bdf2LMM_isGStable`) typechecked without modification (they
instantiate at `R := ℝ` definitionally).

`OpenMath.Chapter4.Section454` rebuilt cleanly (172s build
time, well within the 3-minute target).

Priority 3 (the stretch goal `algebraic_identity_454A`) was
**not** attempted: Priority 2 took roughly the full cycle
budget after the simp-name dead end (see Dead ends below).

## Faithfulness check

For each new theorem introduced this cycle:

### `Section404.gTopLeft` (refactored, polymorphic in R)
- Original: `Matrix (Fin k) (Fin k) ℝ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ`.
- Refactored: `{R : Type*} [Zero R] → Matrix (Fin k) (Fin k) R → Matrix (Fin (k+1)) (Fin (k+1)) R`.
- Captures: **same content**. The ℝ-instantiation is
  definitionally equal to the old definition; downstream BDF2
  witnesses unchanged.

### `Section404.gBottomRight` (refactored, polymorphic in R)
- Same as above.
- Captures: **same content**.

### `Section454.gTopLeft_quadForm_eq` (new)
- Mathematical content: `star W ⬝ᵥ (gTopLeft G *ᵥ W) =
  star (W ∘ Fin.castSucc) ⬝ᵥ (G *ᵥ (W ∘ Fin.castSucc))`.
- Not a Butcher entity; an infrastructure lemma supporting the
  §451e identity proof. Faithful to the textbook in the sense
  that the §454 proof writes:

  > Form the inner product W∗MW ... where M is the matrix
  > given by (451e) and W = (1, w, w², ..., wᵏ).

  The textbook then computes the §451e quadratic form by
  separating the `[G 0; 0 0]` and `[0 0; 0 G]` block contributions
  and identifying each with a quadratic form on a truncated
  Vandermonde. This theorem packages exactly that identification
  for the top-left block.

### `Section454.gBottomRight_quadForm_eq` (new)
- Mathematical content: `star W ⬝ᵥ (gBottomRight G *ᵥ W) =
  star (W ∘ Fin.succ) ⬝ᵥ (G *ᵥ (W ∘ Fin.succ))`.
- Same source-text justification as the top-left case;
  this packages the bottom-right block analogue.

### Five private gTopLeft sub-lemmas (`apply_castSucc`,
`apply_last_row`, `apply_last_col`, `mulVec_castSucc`,
`mulVec_last`) and five private gBottomRight sub-lemmas
(`apply_succ`, `apply_zero_row`, `apply_zero_col`, `mulVec_succ`,
`mulVec_zero`)
- All `private`; not exposed outside the file. Each is a
  pointwise computation of the matrix entry / one row of mulVec
  in a boundary case.
- **Tautology check**: none — each lemma's conclusion follows
  from the if-then-else dispatch on the val of the index, not
  from any hypothesis.
- **Identity check**: none are `exact h` — each lemma genuinely
  unfolds the def and discharges the boundary `dif`.
- **Hypothesis strength check**: minimal — only `[Zero R]` (or
  `[NonAssocSemiring R]` for the mulVec lemmas, which need
  `0 * W = 0` for `Finset.sum_eq_zero`). Strictly weaker than
  the cycle 166 ℝ-only versions.

### Why polymorphic R, not ℂ-only?
Cycle 168 needs the quadratic-form factorisations at `R := ℂ`
when proving `algebraic_identity_454A` (the §451e identity over
ℂ via Vandermonde). Polymorphism from cycle 167 lets cycle 168
instantiate at ℂ without a redundant complex-lifted definition.

The textbook uses `R = ℂ` only in the §454 proof; the §451e
matrix definition itself is over ℝ. Polymorphising the *block
embeddings* (not `gMatrix` itself) keeps the textbook semantic
intact — `gMatrix` is still ℝ-valued because it depends on
`alphaVec`/`betaVec` which are ℝ-valued; only the block
embeddings can be lifted polymorphically.

## Dead ends

* **`simp only [Matrix.dotProduct]`** — does not fire. The def
  in current Mathlib (`Mathlib/Data/Matrix/Mul.lean:72`) lives
  at the root namespace as `dotProduct`, **not**
  `Matrix.dotProduct`. The namespace `Matrix` opens around it
  but does not re-export. So `simp only [Matrix.dotProduct]`
  produces "Unknown constant `Matrix.dotProduct`" in some
  contexts and "simp made no progress" in others.

  **Fix**: use `show ∑ i, ...` to expose the sum form directly.
  This is more robust than `simp only [dotProduct]` because
  the resulting goal has explicit `∑` ready for
  `Fin.sum_univ_castSucc`.

* **Stale .olean cache for Section451** — after the polymorphism
  refactor, the existing `.olean` for Section451 still encoded
  the ℝ-only signature; downstream `lake env lean Section454`
  inherited the old type and gave "Application type mismatch"
  errors. Resolved by `rm Section451.olean*` + `lake build`.

* **Aristotle batch** — cancelled after 18% (80+ minutes). The
  cycle-166 retrospective predicted this; carrying the batch
  longer was not productive. Single-poll discipline + cancel-on-
  no-progress remains the right policy.

* **`congr 1` after `dif_pos`** in `gTopLeft_apply_castSucc`:
  Lean did not reduce
  `G ⟨i.castSucc.val, h.1⟩ ⟨j.castSucc.val, h.2⟩` to `G i j`
  after `rw [dif_pos]`. Closing with `rfl` works, since after
  the rewrite the residual proof obligations are
  proof-irrelevant. The symmetric `gBottomRight_apply_succ`
  needed `congr 1` (no `rfl`), since `i.succ.val - 1 = i.val`
  is *not* definitional and the Fin coercion drops it.

## Discovery

* The polymorphism refactor preserves all downstream witnesses
  by definitional equality at `R := ℝ`. This is a generally
  applicable pattern: *infrastructure-style definitions
  (block embeddings, projections, indexing rearrangements)
  should be polymorphic from the start*; the typeclass burden
  is minimal and downstream lifts are free.
* `dotProduct` is at root namespace, not `Matrix.dotProduct`.
  Future cycles should write `dotProduct` (or use the `⬝ᵥ`
  notation) and avoid `Matrix.dotProduct` in `simp only`
  argument lists.
* `show` (with the sum form) is a cleaner alternative to
  `simp only [Matrix.mulVec, dotProduct]` for exposing the
  fundamental sum representation, especially when followed by
  `Fin.sum_univ_castSucc` / `Fin.sum_univ_succ`.

## Suggested next approach

Cycle 168 should attempt the cycle-166 stretch goal —
`algebraic_identity_454A` — using the named pieces shipped
this cycle:

1. **Statement**: as in `thm_454A_stage_2_3_stall.md`'s
   "What was tried" section. Replace the inline expansion of
   `gTopLeft`/`gBottomRight` with `gTopLeft_quadForm_eq` and
   `gBottomRight_quadForm_eq` applied at `R := ℂ`.
2. **vecMulVec terms**: handled by `aeval_αPoly_eq` /
   `aeval_βPoly_eq` (cycle 166) plus
   `Matrix.dotProduct_vecMulVec` (or unfold).
3. **`(W ∘ Fin.succ) = w • (W ∘ Fin.castSucc)`** — under
   `vanW`, `(vanW w) i.succ = w^(i+1) = w * w^i = w * (vanW w) i.castSucc`.
   So the bottom-right quadratic form is `‖w‖² * (G-quad-form
   on truncated W)`, while the top-left quadratic form is the
   un-scaled version on the same truncated W. Subtract: factor
   of `(‖w‖² - 1)`.
4. **PSD lifts**: `complexLift_posSemidef_of_real_posSemidef`
   and `complexLift_re_dotProduct_pos_of_real_posDef` —
   probably best added to a new file
   `OpenMath/Chapter4/Section454Aux.lean` to keep
   Section454.lean focused on the §454 bridging proof.
5. **`gStable_isAStable`** then assembles `algebraic_identity_454A`
   + the two PSD lifts + `1 - ‖w‖² > 0`.
6. **`bdf2LMM_isAStable`** is then a one-liner from
   `bdf2LMM_isGStable` (cycle 165) + `gStable_isAStable`.

The estimated cycle 168 effort is ~1 cycle if Aristotle solves
the PSD lifts (decompose `x = a + i·b` over ℂ; expand
quadratic form; observe imaginary parts vanish for symmetric
real `A`). Mark Aristotle PSD lifts and `algebraic_identity_454A`
as Aristotle-batch candidates at cycle-168 start.

If cycle 168 hits any further elaboration stall, the cycle-167
named-decomposition pattern (5-line sub-lemmas, each
independent) is the established remediation playbook.
