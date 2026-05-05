# Cycle 134 — Strategy

## Goal (this cycle)

**Strengthen `def:542A` (Runge–Kutta stability) non-vacuity by adding a
substantive `r = 2` witness `padded2DEulerGLM_isRKStable`** alongside
the cycle 130 vacuous-by-`r=1` witness `explicitEulerGLM_isRKStable`.

This mirrors what cycle 133 did for `def:551A` (added
`padded2DEulerGLM_isIRKStable`). The same `padded2DEulerGLM` from
`OpenMath/Chapter5/Section520.lean:632` is reused.

### Why this is the highest-leverage cycle next

* `def:542A`'s cycle 130 witness `explicitEulerGLM_isRKStable` discharges
  the factorisation `Φ(w, z) = w^{r−1} · (w − R(z))` *trivially* at
  `r = 1`: `w^0 · (w − R(z)) = w − R(z)` matches Φ structurally.
  The clause "factorisation is non-trivial" is therefore **vacuously**
  satisfied — the same kind of vacuity that cycle 132/133 fixed for
  `def:551A`.
* For `r ≥ 2`, the factorisation is a real claim about the structure of
  `det(wI − M(z))`. Exhibiting an `r = 2` GLM where `Φ(w, z) = w · (w − R(z))`
  closes the structural-vacuity gap.
* `padded2DEulerGLM` (cycle 133) is purpose-built for this: its `M(z)`
  has the explicit form `!![1+z, 0; 0, 0]` (verified by hand below),
  giving `Φ(w, z) = w · (w − (1+z))` — exactly the `w^{r−1}(w − R(z))`
  shape with `R(z) = 1 + z`.

### The math (do not deviate)

Per `OpenMath/Chapter5/Section520.lean:632`:

```
padded2DEulerGLM : GeneralLinearMethod 1 2
  A := !![0]
  U := !![1, 0]
  B := !![1; 0]
  V := !![1, 0; 0, 0]
```

Stability matrix `M(z) = V + z·B·(I − z·A)⁻¹·U`:

* `(1 − z · complexify A) = (1 : Matrix (Fin 1) (Fin 1) ℂ)` (since `A = !![0]`).
* `(...)⁻¹ = 1`.
* `z • complexify B = !![z; 0]`.
* `!![z; 0] * !![1] * !![1, 0] = !![z, 0; 0, 0]`.
* `M(z) = !![1, 0; 0, 0] + !![z, 0; 0, 0] = !![1+z, 0; 0, 0]`.

Stability function `Φ(w, z) = det(wI − M(z))`:

* `wI − M(z) = !![w − (1+z), 0; 0, w]`.
* `det = (w − (1+z)) · w − 0 · 0 = w · (w − (1+z))`.

So `Φ(w, z) = w^{2−1} · (w − R(z))` with `R(z) := 1 + z`.

## Concrete deliverables

Add three theorems to `OpenMath/Chapter5/Section520.lean`, immediately
**after** the existing `explicitEulerGLM_isRKStable` block (line 543)
and **before** the `### Definition 551A` section header (line 545):

### 1. `padded2DEulerGLM_stabilityMatrix` — closed-form M(z)

```lean
/-- Closed-form stability matrix of `padded2DEulerGLM`:
`M(z) = !![1 + z, 0; 0, 0]`.

Computation: `(1 − z·A) = !![1]` since `A = !![0]`, so
`(1 − z·A)⁻¹ = !![1]`. Then `z·B·(1−z·A)⁻¹·U = !![z, 0; 0, 0]`,
which added to `V = !![1, 0; 0, 0]` gives `!![1+z, 0; 0, 0]`. -/
theorem padded2DEulerGLM_stabilityMatrix (z : ℂ) :
    padded2DEulerGLM.stabilityMatrix z =
      !![1 + z, 0; 0, 0] := by
  -- mirror the explicitEulerGLM_stabilityMatrix proof structure (line 123)
  have hA :
      (1 - z • complexify padded2DEulerGLM.A)
        = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [padded2DEulerGLM, complexify]
  unfold GeneralLinearMethod.stabilityMatrix
  rw [hA, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [padded2DEulerGLM, complexify, Matrix.mul_apply,
          Fin.sum_univ_succ, Fin.sum_univ_zero]
```

If the closing `simp` set is overkill (linter unused-args warning),
trim to `simp [padded2DEulerGLM, complexify, Matrix.mul_apply]` —
the matrix-literal simp lemmas in `Mathlib.Data.Matrix.Notation`
should handle the small-`Fin` summations automatically (per cycle 133
finding).

### 2. `padded2DEulerGLM_stabilityFunction` — closed-form Φ(w, z)

```lean
/-- Closed-form stability function of `padded2DEulerGLM`:
`Φ(w, z) = w · (w − (1 + z))`.

This is the `(s, r) = (1, 2)` case of `Φ(w, z) = det(wI − M(z))`
with `M(z) = !![1+z, 0; 0, 0]`. The `2×2` determinant of the
upper-triangular matrix `!![w − (1+z), 0; 0, w]` is the product
of its diagonal entries `(w − (1+z)) · w = w · (w − (1+z))`. -/
theorem padded2DEulerGLM_stabilityFunction (w z : ℂ) :
    padded2DEulerGLM.stabilityFunction w z =
      w * (w - (1 + z)) := by
  unfold GeneralLinearMethod.stabilityFunction
  rw [padded2DEulerGLM_stabilityMatrix]
  rw [Matrix.det_fin_two]
  simp [Matrix.smul_apply, Matrix.one_apply]
  ring
```

If `Matrix.det_fin_two` does not exist in pinned Mathlib, fall back to
`simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]`
followed by `ring`. (`Matrix.det_fin_two` is in
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic` — verify with
`lean_local_search "det_fin_two"` if needed.)

### 3. `padded2DEulerGLM_isRKStable` — the substantive witness

```lean
/-- **Substantive** non-vacuity witness for `IsRKStable`:
`padded2DEulerGLM` (s = 1, r = 2) has Runge–Kutta stability with
stability function `R(z) = 1 + z`.

Unlike the cycle 130 witness `explicitEulerGLM_isRKStable`
(`r = 1`, where `w^{r−1} = w^0 = 1` makes the factorisation trivial),
the `r = 2` case requires a genuine factorisation of a quadratic in `w`.
From `padded2DEulerGLM_stabilityFunction`,
`Φ(w, z) = w · (w − (1 + z)) = w^{2−1} · (w − R(z))` with
`R(z) := 1 + z`. -/
theorem padded2DEulerGLM_isRKStable :
    padded2DEulerGLM.IsRKStable := by
  refine ⟨fun z => 1 + z, ?_⟩
  intro w z
  rw [padded2DEulerGLM_stabilityFunction]
  -- Goal: w * (w - (1 + z)) = w ^ (2 - 1) * (w - (1 + z))
  simp [pow_one]
  ring
```

Note `r - 1` here is `2 - 1 = 1` (Nat.sub), so `w ^ (r - 1) = w ^ 1 = w`.
The `simp [pow_one]` reduces `w ^ 1` to `w`; `ring` then closes.
If `pow_one` doesn't fire under the `r - 1` Nat.sub, add `show 2 - 1 = 1`
+ `norm_num` first, or use `simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]`.

## What NOT to do

* **Do NOT modify `IsRKStable` or `padded2DEulerGLM`.** Both are stable
  cycle-130/133 deliverables. This cycle adds new theorems only.
* **Do NOT add a new GLM.** Reusing `padded2DEulerGLM` is by design —
  it lets the same s=1, r=2 witness object discharge non-vacuity for
  three predicates (cycle 133 IRK-stability; cycle 134 RK-stability;
  potentially `def:520E` A-stability and `def:520F` L-stability if
  proxied through `R(z) = 1 + z`).
* **Do NOT add Aristotle jobs.** The total proof is ≤ 40 LOC of
  matrix algebra; Aristotle round-trip overhead exceeds the manual
  cost. Cycle 133 reached this same conclusion on a structurally
  identical task.
* **Do NOT raise `maxHeartbeats`.** If `padded2DEulerGLM_stabilityMatrix`
  is slow, decompose by proving `z • complexify B * 1 * complexify U =
  !![z, 0; 0, 0]` as a separate `have`, then rewrite into the main
  goal.
* **Do NOT update `lean_status.json`.** `def:542A` is already
  `formalized` (its `lean_symbol` is the `IsRKStable` predicate, which
  is unchanged). Adding a substantive witness is strengthening
  evidence, not a status change — same logic as cycle 133's `def:551A`
  handling.
* **Do NOT update `plan.md`'s entity-count number.** `def:542A` is
  already counted at 69/175. Append a note to the `def:542A` row
  pointing at the new substantive witness, mirroring cycle 133's
  edit to the `def:551A` row.
* **Do NOT pursue `thm:551B`, `thm:553A`, `thm:520B` companion lemmas,
  or §550 doubly-companion-matrix infrastructure.** Those are
  multi-cycle items. This cycle is a single-priority structural
  closure.
* **Do NOT add a third witness GLM.** One substantive witness per
  predicate is enough for the non-vacuity contract.
* **Do NOT take the cycle-prompt's "What I'm stuck on" framing
  (if any) at face value if it claims commit failure / scanner false
  positive.** Per cycles 008/014/015/040/121 consultant analyses,
  these are stale `attempts.md` carry-overs; verify against `HEAD`
  with `git log -1 --format='%H %s'` before reacting.

## Pre-commit checklist (mandatory; mirror cycle 133 §"Faithfulness check")

For each of the three new theorems:

* **`padded2DEulerGLM_stabilityMatrix`** — N/A for textbook entity
  ID. This is a computational closed-form lemma about a witness
  object, not a textbook concept. The "faithfulness" question reduces
  to "does the closed form actually equal `M(z)`?", verified by the
  proof (which mechanically unfolds the definition).

* **`padded2DEulerGLM_stabilityFunction`** — same as above.

* **`padded2DEulerGLM_isRKStable`** — entity ID `def:542A`.
  - Quote textbook statement (from
    `extraction/formalization_data/entities/def_542A.json`):
    > "A general linear method `(A, U, B, V)` has 'Runge–Kutta
    > stability' if the characteristic polynomial given by (542a) has
    > the form `Φ(w, z) = w^{r−1}(w − R(z))`."
  - Lean statement captures: **same content** as cycle 130. The
    `IsRKStable` predicate is unchanged. This theorem exhibits a
    second inhabitant (`padded2DEulerGLM`) of the same predicate. No
    divergence.
  - Tautology check: conclusion `padded2DEulerGLM.IsRKStable` is not
    a hypothesis (zero hypotheses).
  - Identity check: the proof is not `exact h` — it produces an
    explicit `R := fun z => 1 + z` and then proves the `∀ w z`
    factorisation by unfolding to the closed form from theorem 2.
  - Substantive vs vacuous check: **substantive**. With `r = 2`,
    `w ^ (r − 1) = w ^ 1 = w`, so the factorisation is a genuine
    statement that `Φ(w, z)` has `w` as a root for every `z`, plus
    the second factor `(w − R(z))`. The cycle 130 `r = 1` witness
    has `w ^ 0 = 1`, making the factorisation a trivial restatement
    of `Φ(w, z) = w − R(z)`.

## Build verification (mandatory before commit)

In order:

1. `lake env lean OpenMath/Chapter5/Section520.lean` — must exit 0,
   no warnings, no errors, no `sorry`.
2. `lake build OpenMath.Chapter5.Section520` — must complete
   successfully.
3. Axiom check on each new theorem (in a scratch `.lean` file or via
   `#print axioms` appended to the bottom of `Section520.lean` and
   removed before commit):
   * `#print axioms padded2DEulerGLM_stabilityMatrix`
   * `#print axioms padded2DEulerGLM_stabilityFunction`
   * `#print axioms padded2DEulerGLM_isRKStable`

   All three must print `[propext, Classical.choice, Quot.sound]`
   (axiom-clean — no `sorryAx`).
4. Regression check on cycle 130/133 witnesses (axiom-clean must be
   preserved):
   * `#print axioms explicitEulerGLM_isRKStable`
   * `#print axioms padded2DEulerGLM_isIRKStable`
   * `#print axioms explicitEulerGLM_isIRKStable`

## Plan / status edits (mandatory)

* **`plan.md`** — find the `def:542A` row (currently
  `[x] def:542A …  (cycle 130, axiom-clean; predicate +
  explicitEulerGLM_isRKStable witness with R(z) = 1 + z)`). Append a
  cycle 134 note in the same shape as cycle 133's `def:551A` edit:
  e.g. `… (cycle 130 predicate + explicitEulerGLM_isRKStable r=1
  vacuous witness; cycle 134 substantive r=2 witness
  padded2DEulerGLM_isRKStable via padded2DEulerGLM (reused from
  cycle 133); both axiom-clean.)`.
* **`lean_status.json`** — DO NOT edit. `def:542A` remains
  `formalized`.

## Task results (mandatory)

Write `.prover-state/task_results/cycle_134.md` with:

* **Worked on**: `def:542A` substantive `r = 2` non-vacuity witness.
* **Approach**: reuse `padded2DEulerGLM` from cycle 133; build closed
  forms for `M(z)` and `Φ(w, z)`; close `IsRKStable` with `R(z) = 1 + z`.
* **Result**: SUCCESS / FAILED — explanation; if SUCCESS, list the
  three new theorems and their axiom-clean status.
* **Faithfulness check**: full per-theorem block per the checklist
  above.
* **Dead ends**: anything that didn't fire (`Matrix.det_fin_two`
  unavailable? `inv_one` not applying? `pow_one` not firing under
  `Nat.sub`? etc.).
* **Discovery**: any new pattern learned that future witness cycles
  can reuse.
* **Suggested next approach**: based on the resulting state, the
  most likely next planner moves are
  (1) `thm:551B` — Single Non Zero Eigenvalue Stability — read
      `extraction/formalization_data/entities/thm_551B.json` to
      classify the prerequisite stack first;
  (2) Open the next leaf-node Chapter 3 entity (e.g. `def:381F`
      P-equivalent, `lem:351A` criteria for A-stability, or one of
      the §302 enumeration lemmas);
  (3) Negative-witness work on `def:520E` A-stability — `R(z) = 1+z`
      is *not* A-stable; this would be a different shape from the
      positive-witness pattern of cycles 130–134 and may be deferred.

## Risks and mitigations

* **Risk**: `Matrix.det_fin_two`'s simp normal form may not match the
  expected `(M 0 0) * (M 1 1) - (M 0 1) * (M 1 0)` shape under the
  `wI - M(z)` substitution.
  - **Mitigation**: after `rw [padded2DEulerGLM_stabilityMatrix]`,
    apply `Matrix.det_fin_two` then `simp` with explicit lemmas
    `Matrix.sub_apply`, `Matrix.smul_apply`, `Matrix.one_apply` to
    normalise. Worst case, fall back to
    `simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.smul_apply, Matrix.one_apply]; ring`.
* **Risk**: `pow_one` doesn't fire because Lean sees `w ^ (2 - 1 : ℕ)`
  with the `Nat.sub` not reduced.
  - **Mitigation**: `show w * (w - (1 + z)) = w ^ 1 * (w - (1 + z))`
    + `rw [pow_one]`. Or `simp only [show (2 : ℕ) - 1 = 1 from rfl,
    pow_one]`.
* **Risk**: matrix multiplication closure in step 1 fails on
  individual `Fin` indices because `Matrix.mul_apply` doesn't unfold
  cleanly.
  - **Mitigation**: explicitly `unfold Matrix.mul Matrix.HMul.hMul`
    + `simp [Fin.sum_univ_succ, Fin.sum_univ_zero,
    padded2DEulerGLM, complexify]` per index. Worst case, prove each
    of the four entries `M(z) i j` for `(i,j) ∈ Fin 2 × Fin 2` as
    individual `have`s and assemble.
* **Risk**: `lake build` cache invalidation forces a long re-elaborate.
  - **Mitigation**: time budget. If `lake env lean
    OpenMath/Chapter5/Section520.lean` exits 0 standalone, the file
    is correct — `lake build` is the final regression check, not the
    inner-loop verification tool.

## Cycle budget

* New code: ~40 LOC (3 theorems + docstrings).
* Edits to `plan.md`: 1 line.
* No edits to `lean_status.json`, no new files (other than
  `task_results/cycle_134.md`).
* Single commit.
* Expected total wall time: 60–90 minutes including verification.
