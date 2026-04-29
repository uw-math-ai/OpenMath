# Cycle 034 Results

## Worked on

Fixing the `symplecticityMatrix` transpose bug discovered in cycle 033
and documented in
`.prover-state/issues/symplecticityMatrix_missing_transpose.md`.
Specifically:

- `OpenMath/Chapter3/Section370.lean`: definition of
  `symplecticityMatrix` and its docstring.
- `OpenMath/Chapter3/Section370.lean`:
  `implicitMidpoint_isSymplectic` simp set (defensive).
- `OpenMath/Chapter3/Section357.lean`: deletion of
  `algebraicallyStable_imp_A_symm`, simplification of
  `symplecticityMatrix_quadratic_form_eq` (drop `hSym`), call-site
  update in `algebraicallyStable_isBNStable`, and an obsolete
  docstring paragraph.
- `.prover-state/issues/symplecticityMatrix_missing_transpose.md`:
  added a "Resolution (cycle 034)" header marking it RESOLVED.

No new sorrys, no new theorems, no Aristotle submissions — exactly as
the cycle-034 strategy prescribed.

## Approach

Followed cycle-034 strategy verbatim.

### Step 1 — `symplecticityMatrix` definition (`Section370.lean`)

Replaced

```lean
Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
  Matrix.vecMulVec R.b R.b
```

with

```lean
Matrix.diagonal R.b * R.A + R.A.transpose * Matrix.diagonal R.b -
  Matrix.vecMulVec R.b R.b
```

and updated the LaTeX in the file-level docstring and the `def`
docstring from `A diag(b)` to `A^{\top} diag(b)`. Also updated the
faithfulness-notes bullet to mention `R.A.transpose`.

### Step 2 — `implicitMidpoint_isSymplectic` (`Section370.lean`)

Added `Matrix.transpose_apply` to the simp set, defensive even though
for `s = 1` the 1×1 case is invariant under transpose. Verified clean
compile via `lake env lean OpenMath/Chapter3/Section370.lean`.

### Step 3a — Deleted `algebraicallyStable_imp_A_symm`

The lemma is no longer provable: with the corrected
`symplecticityMatrix`, the matrix is automatically symmetric in
`(i, j)` regardless of `A`, so PSD/Hermitian no longer transports
information about `A i j = A j i`. It is also no longer needed, since
Lemma 1 has been simplified to drop the `A` symmetric hypothesis.
Removed the docstring + lemma body cleanly.

### Step 3b — Simplified `symplecticityMatrix_quadratic_form_eq`

Dropped the `(hSym : ∀ i j, M.A i j = M.A j i)` hypothesis. Replaced
the proof with the index-swap form from the strategy. The unfolding
identity `hM` now reads

```
symplecticityMatrix M i j = M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j
```

(textbook (357d)/(370a) entry-wise form), and the swap identity

```
∑ i, ∑ j, M.A j i * M.b j * inner ℝ (F i) (F j)
= ∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j)
```

is proved by `Finset.sum_comm` together with `real_inner_comm`,
without needing `A i j = A j i`. The rest of the proof (split LHS,
split RHS, `hswap`, `ring`) is unchanged from cycle 033 modulo the
index relabel `M.A i j → M.A j i`.

The unfolding `simp` set initially produced an unsolved
`M.A i j = M.A j i ∨ M.b j = 0` goal. The fix was to use
`Matrix.diagonal_apply` (instead of `Matrix.diagonal`), confirmed via
`lean_multi_attempt`. With that swap simp closes the goal directly,
no `ring` follow-up needed.

### Step 3c — Call-site update in `algebraicallyStable_isBNStable`

Removed

```lean
have hA_sym : ∀ i j, M.A i j = M.A j i :=
  algebraicallyStable_imp_A_symm ⟨hb_pos, hM_psd⟩
```

and changed

```lean
have hForm := symplecticityMatrix_quadratic_form_eq M hA_sym F
```

to

```lean
have hForm := symplecticityMatrix_quadratic_form_eq M F
```

### Step 3d — Docstring update in `Section357`

Replaced the obsolete cycle-033 caveat paragraph
("the existing `symplecticityMatrix` (cycle 027) unfolds to
`(b_i + b_j) a_{ij} − b_i b_j` rather than the textbook's
`b_i a_{ij} + b_j a_{ji} − b_i b_j`. …") with a short positive
sentence stating that `symplecticityMatrix M` is now the textbook
form `m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`, which the §357C
proof uses directly via the index-swap identity in Lemma 1.

### Step 4 — Build verification

```
$ lake env lean OpenMath/Chapter3/Section370.lean
(clean exit, no warnings)

$ lake env lean OpenMath/Chapter3/Section357.lean
warning: OpenMath/Chapter3/Section357.lean:433:20: `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` has been deprecated (pre-existing, not introduced this cycle)
EXIT 0

$ lake build
✔ [2906/2907] Built OpenMath (2.8s)
Build completed successfully (2907 jobs).
```

### Axiom check

```
'OpenMath.Chapter3.Section370.implicitMidpoint_isSymplectic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section357.implicitMidpoint_isAlgebraicallyStable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter3.Section357.algebraicallyStable_isBNStable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three entrypoints rest on the standard set, with no
`sorryAx` and no new axioms introduced.

### Step 5 — Issue file marked resolved

Added a "Resolution (cycle 034)" section at the top of
`.prover-state/issues/symplecticityMatrix_missing_transpose.md`
documenting the fix, the deletion of
`algebraicallyStable_imp_A_symm`, and the simpler
`symplecticityMatrix_quadratic_form_eq` signature. The original
diagnostic text is preserved as historical record.

### Step 6 — `lean_status.json` audit

Confirmed `def:357A`, `def:357B`, `thm:357C`, and `def:370A` rows
still point at the correct files and symbols
(`Section357.lean` / `IsBNStable`, `IsAlgebraicallyStable`,
`algebraicallyStable_isBNStable`; `Section370.lean` / `IsSymplectic`).
No edits needed.

## Result

SUCCESS. Bug fix landed exactly as the strategy prescribed:

- `symplecticityMatrix` is the textbook form (357d) ⇔ (370a).
- `IsAlgebraicallyStable` no longer silently restricts to symmetric `A`.
- `algebraicallyStable_imp_A_symm` deleted (no longer derivable).
- `symplecticityMatrix_quadratic_form_eq` now hypothesis-light
  (`hSym` dropped).
- `algebraicallyStable_isBNStable` and
  `implicitMidpoint_isAlgebraicallyStable` still compile under the
  standard axioms.

## Faithfulness check

This cycle introduced **no new** `def`s, `structure`s, or `theorem`s.
It only modified existing artefacts. The faithfulness review
nevertheless covers the modified objects.

### Modified `def`: `symplecticityMatrix` (Section370)

- Entity ID: `def:370A` (and indirectly `def:357B` which reuses it).
- Textbook statement (`def_370A.json`):
  > A Runge–Kutta method `(A, b, c)` is *symplectic* if
  > `M = diag(b) A + Aᵀ diag(b) − bbᵀ` (entry-wise:
  > `m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`) is the zero matrix.
- New Lean definition:
  `Matrix.diagonal R.b * R.A + R.A.transpose * Matrix.diagonal R.b -
   Matrix.vecMulVec R.b R.b`.
- Lean entry-wise form (verified by simp inside Lemma 1's `hM`):
  `m_{ij} = b_i a_{ij} + a_{ji} b_j − b_i b_j`, exactly the textbook
  form.
- Captures: **same content** as the textbook. The cycle-033 caveat
  ("the Lean form is `(b_i + b_j) a_{ij} − b_i b_j`, not the
  textbook's `b_i a_{ij} + b_j a_{ji} − b_i b_j`") no longer applies.

### Modified `def`: `IsAlgebraicallyStable` (Section357, body unchanged but semantics now broader)

- Entity ID: `def:357B`.
- Textbook statement (`def_357B.json`):
  > A Runge–Kutta method `(A, b, c)` is 'algebraically stable' if
  > `bᵢ > 0` for `i = 1, …, s`, and if the matrix `M = diag(b) A +
  > A diag(b) − bbᵀ` (357d) is positive semi-definite.
  >
  > (Note: Butcher's prose at (357d) writes `A` in the second slot,
  > but Burrage–Butcher and the entry-wise form `m_{ij} = b_i a_{ij}
  > + b_j a_{ji} − b_i b_j` make clear that the second slot is
  > `Aᵀ`. `def_370A.json` has the textbook formula written with the
  > transpose explicitly.)
- New Lean meaning (predicate body unchanged, but now uses corrected
  `symplecticityMatrix`): `(∀ i, 0 < R.b i) ∧ (symplecticityMatrix R)`
  is `PosSemidef`, where `symplecticityMatrix` is now the textbook
  form.
- Captures: **same content** as the textbook, no longer silently
  strengthened. Pre-fix, PSD on the buggy matrix forced
  `A i j = A j i`; post-fix, the matrix is automatically symmetric
  for every `A`, so PSD imposes no symmetric-`A` hidden hypothesis.

### Modified `lemma`: `symplecticityMatrix_quadratic_form_eq` (Section357)

- Status: helper lemma, not a numbered textbook entity.
- Statement: `∑ i, ∑ j, (2 b_i a_{ij} − b_i b_j) ⟨F_i, F_j⟩
  = ∑ i, ∑ j, symplecticityMatrix M i j * ⟨F_i, F_j⟩` for every `M`
  and every `F : Fin s → N` in a real inner-product space.
- Captures: **same content** as the cycle-033 statement, with
  hypothesis `(hSym : ∀ i j, M.A i j = M.A j i)` dropped (the swap
  identity now goes through without it). This is a strict
  weakening of hypotheses, so the lemma is genuinely stronger.

### Deleted helper: `algebraicallyStable_imp_A_symm` (Section357)

- Removed because the new `symplecticityMatrix` is automatically
  symmetric in `(i, j)`, so the PSD/Hermitian hypothesis no longer
  transports any information about `M.A`. The lemma was *false*
  under the new definition (or rather, `M.A i j = M.A j i` is no
  longer derivable from `IsAlgebraicallyStable`), and is also no
  longer used anywhere — the only consumer was Lemma 1, which now
  works without it.

### Modified `theorem`: `algebraicallyStable_isBNStable` (Section357)

- Entity ID: `thm:357C` (Burrage–Butcher: algebraic stability ⇒
  BN-stability).
- Textbook statement: unchanged from cycle 033 — algebraic stability
  ⇒ BN-stability for every dissipative non-autonomous IVP and step.
- Lean statement: unchanged.
- Lean proof: simplified by removing the `hA_sym` invocation and
  passing one fewer argument to Lemma 1.
- Captures: **same content** as cycle 033. The fix removes the
  hidden over-restriction in the hypothesis (`IsAlgebraicallyStable`
  no longer forces `A` symmetric), while preserving the textbook
  conclusion. The proof uses no new axioms.

## Dead ends

One small hiccup: the initial entry-wise unfolding `simp` set
copy-pasted from the strategy

```
simp [symplecticityMatrix, Matrix.mul_apply, Matrix.diagonal,
      Matrix.vecMulVec, Matrix.sub_apply, Matrix.add_apply,
      Matrix.transpose_apply]
```

left an unsolved goal `M.A i j = M.A j i ∨ M.b j = 0`. Replacing
`Matrix.diagonal` with `Matrix.diagonal_apply` (so that the
`if-then-else` from the diagonal entry is normalised eagerly via
`Finset.sum_ite_eq`) closed the goal directly. No `ring` cleanup
needed. Verified via `lean_multi_attempt` on a single line before
applying.

## Discovery

- `Matrix.diagonal` (the `simp` lemma) leaves the diagonal as
  `if i = j then b i else 0` and lets simp sort out the resulting
  `Finset` reductions; for entry-wise unfolding under
  `Matrix.mul_apply`, `Matrix.diagonal_apply` is more reliable
  because it pairs more directly with `Finset.sum_ite_eq`. Save
  this for future cycles that unfold `diagonal _` × matrix products.
- `Matrix.transpose_apply` (with the `R.A.transpose` placement) does
  not need to be in the simp set when `Matrix.diagonal_apply` is
  also present — simp handles the chain of rewrites without it. The
  defensive include is harmless but Lean will warn it is unused, so
  keep it only when needed for clarity.
- After this fix, the §357C proof's intermediate Lemma 1 is one
  hypothesis lighter and its statement type-checks for **every**
  `RKTableau`, not just methods with symmetric `A`. This means
  future §356/§357 consumers of `IsAlgebraicallyStable` (e.g.,
  `thm:356C` once AN-stability lands) won't need an `A symm`
  precondition either.

## Suggested next approach

The cycle-034 strategy already lays out two viable next-cycle
candidates; restating them here for the planner's convenience:

- **Option A (recommended): a §3 leaf entry that doesn't depend on
  AN-stability or §142 Schur.** From `plan.md`, strong candidates
  are:
  - `def:381B` (Φ-equivalent),
  - `def:381D` (P-reducible),
  - `def:381F` (P-equivalent),
  - `lem:310B` (elementary differential weight formula).

  These chip away at the §380 and §31x clusters and are unblocked
  by current infrastructure.

- **Option B: open the AN-stability infrastructure.** Per
  `AN_stability_deferred.md`, this unlocks `thm:357D`,
  `thm:356C`, `cor:356D`, and the non-trivial parts of §358/§359.
  Required ingredients (none currently present in the repo):
  `Matrix.diagonal` of complex eigenvalues, the resolvent
  `(I − AZ)⁻¹` via `Matrix.nonsing_inv`, the scalar `R(Z)`, the
  closed-left-half-plane condition, and `|R(Z)| ≤ 1`. Estimated
  1–2 cycles. Higher leverage but heavier lift.

The cycle-033 deprecation warning on
`Matrix.posSemidef_iff_eq_conjTranspose_mul_self` is also worth
noting — Mathlib has moved to `CStarAlgebra.nonneg_iff_eq_star_mul_self`
in a different namespace with a different type signature. Out of
scope for this cycle, but a future hygiene cycle should migrate
the `posSemidef_inner_form_nonneg` helper.
