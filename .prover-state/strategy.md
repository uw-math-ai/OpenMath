# Cycle 034 Strategy — Fix the `symplecticityMatrix` transpose bug

## TL;DR

This is a **focused infrastructure cycle**. The single deliverable is fixing
the `symplecticityMatrix` bug discovered in cycle 033 and documented in
`.prover-state/issues/symplecticityMatrix_missing_transpose.md`. After the
fix, three things change in the codebase:

1. `IsAlgebraicallyStable` covers the textbook's intended class (no longer
   silently restricted to symmetric `A`).
2. `algebraicallyStable_imp_A_symm` becomes unprovable (and unnecessary)
   and must be **deleted**.
3. The `hSym` hypothesis on `symplecticityMatrix_quadratic_form_eq`
   (Lemma 1) becomes unnecessary; the lemma's proof must be reworked to
   use an index-swap argument instead.

No new theorems, no new sorrys, no Aristotle submissions this cycle. The
bug fix is the entire job. After the fix lands, downstream cycles (357D,
356C, …) can rest on a faithful predicate.

## Why this is the priority (not 357D, not §3 leaf entries)

`thm:357D` (BN ⇒ AN) — the natural successor to `thm:357C` — depends on
`def:356A`'s **AN-stability** component, which is deferred (see
`AN_stability_deferred.md`). That cycle is several cycles of complex
matrix resolvent infrastructure away. So §357 is **blocked above**.

§357 is also blocked **below** by today's bug: the entire §357C theorem
proved last cycle relies on a predicate (`IsAlgebraicallyStable`) that
silently excludes most useful RK methods. Leaving the bug unfixed
means every later §357/§356C consumer of `IsAlgebraicallyStable`
inherits the silent restriction. This must be cleaned up before more
weight is built on top.

This cycle is small (the cycle-033 task results estimate "one-line
change + simplification"), high-leverage, and has zero novel
mathematics. It is exactly the kind of work that should not be
postponed.

## Step-by-step task list

### Step 1: Edit `OpenMath/Chapter3/Section370.lean:55–58`

Change the second `R.A` to `R.A.transpose`:

```lean
def symplecticityMatrix {s : ℕ} (R : RKTableau s) :
    Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal R.b * R.A + R.A.transpose * Matrix.diagonal R.b -
    Matrix.vecMulVec R.b R.b
```

Also update the docstring at lines 48–54 to match Butcher's actual
formula:

```
\[
  M = \operatorname{diag}(b) A + A^{\top} \operatorname{diag}(b) - b b^{\top}.
\]
```

(Keep the entry-wise sentence "`m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`"
— that was already the textbook form and it is now correct as written.)

**Verify the entry-wise unfolding** with `lean_multi_attempt` if
needed. The new entries are:

- `(diag(b) * A) i j = b i * A i j`
- `(Aᵀ * diag(b)) i j = A j i * b j`
- `(bbᵀ) i j = b i * b j`
- Sum: `b_i * A i j + A j i * b j - b_i * b_j` ✓

### Step 2: Verify / fix `implicitMidpoint_isSymplectic`

The `s = 1` 1×1 case is invariant under transpose (`A 0 0 = A 0 0`),
so the proof at `Section370.lean:76–82` should still work. But the
`simp` lemma set may need `Matrix.transpose_apply` added:

```lean
simp [Matrix.diagonal, Matrix.vecMulVec, Matrix.mul_apply,
      Matrix.transpose_apply]
```

Run `lake env lean OpenMath/Chapter3/Section370.lean`. If it fails,
inspect the goal with `lean_goal` and add the missing simp lemma.
This is a 1-line fix at most.

### Step 3: Rework `OpenMath/Chapter3/Section357.lean`

#### Step 3a: Delete `algebraicallyStable_imp_A_symm` (lines 261–289)

It is no longer provable (the new symplecticity matrix is automatically
symmetric in `(i, j)` regardless of `A`) and no longer needed. Delete
the docstring + lemma body entirely.

#### Step 3b: Simplify `symplecticityMatrix_quadratic_form_eq` (lines 291–345)

Drop the `(hSym : ∀ i j, M.A i j = M.A j i)` hypothesis. Update the
docstring to drop the "under `A` symmetric" wording and mention that
the equality now holds for **all** `M`, by an index-swap argument.

The new proof outline (replace the existing 50-line proof):

```lean
private lemma symplecticityMatrix_quadratic_form_eq {s : ℕ}
    (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (F : Fin s → N) :
    ∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
        inner ℝ (F i) (F j)
    = ∑ i, ∑ j, symplecticityMatrix M i j * inner ℝ (F i) (F j) := by
  -- Step 1: unfold symplecticityMatrix entry-wise to the textbook form.
  have hM : ∀ i j, symplecticityMatrix M i j =
      M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j := by
    intro i j
    simp [symplecticityMatrix, Matrix.mul_apply, Matrix.diagonal,
          Matrix.vecMulVec, Matrix.sub_apply, Matrix.add_apply,
          Matrix.transpose_apply]
  -- Step 2: rewrite RHS to its expanded form.
  conv_rhs =>
    rw [show (∑ i, ∑ j, symplecticityMatrix M i j * inner ℝ (F i) (F j))
       = ∑ i, ∑ j, (M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j)
                    * inner ℝ (F i) (F j)
        from Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => by rw [hM]]
  -- Step 3: the key index-swap identity:
  --   ∑ᵢⱼ a_{ji} b_j ⟨F i, F j⟩ = ∑ᵢⱼ b_i a_{ij} ⟨F i, F j⟩
  -- via i ↔ j swap and ⟨F j, F i⟩ = ⟨F i, F j⟩.
  have hswap :
      ∑ i, ∑ j, M.A j i * M.b j * inner ℝ (F i) (F j)
      = ∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (F j) (F i)]
    ring
  -- Step 4: split LHS and RHS into the linear pieces and use hswap.
  have lhs_split :
      (∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) * inner ℝ (F i) (F j))
      = (2 : ℝ) * (∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j))
        - (∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)) := by
    simp only [sub_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have rhs_split :
      (∑ i, ∑ j, (M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j)
                * inner ℝ (F i) (F j))
      = (∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j))
        + (∑ i, ∑ j, M.A j i * M.b j * inner ℝ (F i) (F j))
        - (∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)) := by
    simp only [add_mul, sub_mul, ← Finset.sum_sub_distrib,
               ← Finset.sum_add_distrib]
  rw [lhs_split, rhs_split, hswap]
  ring
```

The key observation: `hswap` proves
`∑ᵢⱼ a_{ji} b_j ⟨F_i, F_j⟩ = ∑ᵢⱼ b_i a_{ij} ⟨F_i, F_j⟩` by
`Finset.sum_comm` plus inner-product symmetry, with no need for
`A` symmetric. The `ring` at the end of step 4 sees `2 X - Y =
X + X - Y` (since `hswap` rewrites the second RHS sum to match
the first).

If the proof above does not type-check verbatim, the cycle's
fallback is to keep the structure but use `lean_multi_attempt` /
`lean_goal` at the points where rewrites stall. Do **not** add
`hSym` back — that would mean the bug isn't actually fixed.

#### Step 3c: Update the call site in `algebraicallyStable_isBNStable`

At lines 516–517 (after `obtain ⟨hb_pos, hM_psd⟩ := hAS`):

```lean
have hA_sym : ∀ i j, M.A i j = M.A j i :=
  algebraicallyStable_imp_A_symm ⟨hb_pos, hM_psd⟩
```

**Delete this `have`**. It is no longer derivable and no longer
needed.

At line 535:

```lean
have hForm := symplecticityMatrix_quadratic_form_eq M hA_sym F
```

Change to:

```lean
have hForm := symplecticityMatrix_quadratic_form_eq M F
```

(Drop the `hA_sym` argument — the lemma no longer takes it.)

#### Step 3d: Update the docstring at lines 233–259

The "Note: the existing `symplecticityMatrix` (cycle 027) unfolds to
`(b_i + b_j) a_{ij} − b_i b_j` rather than the textbook's …"
paragraph (lines 251–258) is now obsolete and must be **deleted**.
Replace it with a short positive sentence: "`symplecticityMatrix M`
is now the textbook form `m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`
(equation (357d) and equivalently (370a)); the proof below uses this
form directly."

### Step 4: Verify the build

Run, in order, expecting clean exits:

```bash
lake env lean OpenMath/Chapter3/Section370.lean
lake env lean OpenMath/Chapter3/Section357.lean
lake build
```

Verify the axiom set on the affected entrypoints:

```
#print axioms OpenMath.Chapter3.Section370.implicitMidpoint_isSymplectic
#print axioms OpenMath.Chapter3.Section357.implicitMidpoint_isAlgebraicallyStable
#print axioms OpenMath.Chapter3.Section357.algebraicallyStable_isBNStable
```

All three should report `[propext, Classical.choice, Quot.sound]`.

### Step 5: Update the resolved issue file

Edit `.prover-state/issues/symplecticityMatrix_missing_transpose.md`:
add a "## Resolution (cycle 034)" section at the top documenting:

- The fix that landed (`R.A` → `R.A.transpose` in Section370 line 57).
- That `algebraicallyStable_imp_A_symm` was deleted.
- That `symplecticityMatrix_quadratic_form_eq` no longer needs the
  `hSym` hypothesis.
- A pointer to the new commit hash.

Do NOT delete the issue file — leave it as a historical record. Just
mark it resolved at the top.

### Step 6: Verify `extraction/formalization_data/lean_status.json`

Confirm that the `def:357B`, `thm:357C`, `def:357A`, and `def:370A`
rows still point at the correct files; the bug fix preserves all of
them. No edits expected.

## Faithfulness check (mandatory before commit)

For the modified `symplecticityMatrix`:

- [ ] Quote the textbook formula from `def_357B.json` /
      `entities/def_370A.json` and confirm it matches the new Lean
      definition (`diag(b) A + Aᵀ diag(b) − bbᵀ`, entries
      `b_i a_{ij} + b_j a_{ji} − b_i b_j`).
- [ ] Confirm `IsAlgebraicallyStable` no longer silently entails
      symmetric `A` (the new symplecticity matrix is symmetric in
      `(i, j)` automatically, so `IsHermitian` is non-restrictive on
      `A`).
- [ ] The cycle-033 `algebraicallyStable_isBNStable` proof must
      still work after the simplification (Lemma 1 simpler, no
      `algebraicallyStable_imp_A_symm`).

## What NOT to try

- **Do not** preserve `algebraicallyStable_imp_A_symm` "for backwards
  compatibility". It is not exported, it is `private`, and after the
  fix it would be unprovable. Delete it cleanly.
- **Do not** add a parallel `symplecticityMatrixSym` definition.
  Solution 2 in the issue file (parallel definitions) was explicitly
  not recommended; pick solution 1 (fix the definition).
- **Do not** weaken `IsAlgebraicallyStable` to add `A` symmetric as
  an explicit hypothesis. The textbook does NOT require `A` symmetric.
- **Do not** modify `IsBNStable`, `bn_stability_identity`, or
  `posSemidef_inner_form_nonneg`. None of them depend on the bug.
- **Do not** start `thm:357D` this cycle. It depends on AN-stability
  (deferred), and bundling it with the bug fix would make the cycle
  unreviewable.
- **Do not** raise `maxHeartbeats`. The Section357 proof was
  comfortably within budget last cycle and the simplification should
  reduce heartbeat usage, not increase it.
- **Do not** introduce `axiom` / `constant` if any rewrite stalls.
  Decompose with `lean_multi_attempt` / `lean_goal` instead.
- **Do not** modify `scripts/autonomous_loop.py` or any
  `.prover-state/` infrastructure. Per CLAUDE.md and the cycle-014
  consultant guidance, scanner / loop changes are the loop
  maintainer's responsibility.
- **Do not** chase the "stuck" entries from older `attempts.md`
  rows — both Section112 and Section212 false positives have been
  resolved (cycles 014 and 015). The current `OpenMath/` tree has
  zero scanner hits, verified via
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`.

## Aristotle usage this cycle

**None.** This cycle has zero new sorrys and zero new theorems. The
bug fix is a refactor + a one-paragraph proof simplification, both
of which are quicker manually than via Aristotle.

If for any reason `symplecticityMatrix_quadratic_form_eq` fails to
type-check after the rewrite and resists `lean_multi_attempt`, file
the goal as a sorry'd helper lemma and submit to Aristotle as a
single-job fallback. Do NOT submit speculative jobs in advance.

## Task results expectations

Write `.prover-state/task_results/cycle_034.md` documenting:

- The exact diff applied to `Section370.lean` (definition + docstring).
- The exact diff applied to `Section357.lean` (Lemma 1 simplification,
  helper deletion, theorem-call update, docstring update).
- The `lake env lean` and `lake build` results.
- The `#print axioms` outputs for the three entrypoints in Step 4.
- A faithfulness section confirming the new `symplecticityMatrix`
  matches the textbook (357d)/(370a) formula verbatim.
- The cross-link to the resolved
  `symplecticityMatrix_missing_transpose.md` issue.

## After this cycle (for the next planner)

Once the bug is fixed, the natural cycle-035 candidates are:

- **Option A (recommended): a §3 leaf entry that doesn't depend on
  AN-stability or §142 Schur.** Strong candidates from the plan:
  `def:381B` (Φ-equivalent), `def:381D` (P-reducible), `def:381F`
  (P-equivalent), `lem:310B` (elementary differential weight formula).
  These are unblocked by current infrastructure and chip away at the
  §380 and §31x clusters.

- **Option B: open the AN-stability infrastructure.** Per
  `AN_stability_deferred.md`, this is the path that unlocks `thm:357D`,
  `thm:356C`, `cor:356D`, and the non-trivial parts of §358/§359. The
  required pieces are: `Matrix.diagonal` of complex eigenvalues, the
  resolvent `(I − AZ)⁻¹` via `Matrix.nonsing_inv`, the scalar `R(Z)`,
  the closed-left-half-plane condition, and the magnitude bound
  `|R(Z)| ≤ 1`. Estimated 1–2 cycles. Higher leverage but heavier
  lift.

The next planner should pick based on whether the project is
prioritising breadth (Option A) or depth in §356/§357 (Option B).
