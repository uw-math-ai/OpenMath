# Cycle 144 Strategy

## Context summary

* No pending Aristotle results; no sorries in the codebase.
* Cycle 143 closed Priority 1 cleanly (axiom-clean r = 2 substantive
  L-stability witness `padded2DBackwardEulerGLM_isLStable` for
  `def:520F`).
* §520 four-corner non-vacuity coverage of `def:520E` × `def:520F` is
  now strong: r = 1 positive (cycle 135 `implicitMidpointGLM`,
  cycle 142 `backwardEulerGLM`), r = 1 negative (cycle 136
  `explicitEulerGLM`, cycle 137 `implicitMidpointGLM_not_isLStable`),
  r = 2 positive (cycle 134 `padded2DEulerGLM_isRKStable`, cycle 143
  `padded2DBackwardEulerGLM_isLStable`).
* §550 has axiom-clean witnesses at `n = 1` (cycle 138) and `n = 2`
  (cycle 140 via Aristotle Job B). General-`n` is still deferred per
  `.prover-state/issues/thm_550A_general_n.md`.
* Cycle 141 cancelled Aristotle Job A (general-`n` thm:550A) at 6%
  after 24 h — confirmed intractable for the prover; manual cofactor
  expansion is multi-cycle work and is **off the table** for cycle 144.

## Priority 1 (PRIMARY): thm:550A n = 3 stepping stone

**Target.** Add a third concrete-`n` axiom-clean witness for
Theorem 550A:

```lean
theorem doublyCompanionMatrix_det_factorization_n_three
    (α β : Fin 3 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 4)
```

(Note `z ^ (n + 1) = z ^ 4` for `n = 3`.)

**Location**: `OpenMath/Chapter5/Section550.lean`, immediately after
`doublyCompanionMatrix_det_factorization_n_two` (currently the last
declaration in the namespace, ending around line 192).

**Why this target**:

1. Builds steadily on cycles 138 (n = 1) and 140 (n = 2).
2. Establishes a third data point for the leading-coefficient
   pattern `−Σᵢ α_i · β_{n-i} z^{n+1} − …` that any future general-`n`
   proof must match.
3. Mechanical via `Matrix.det_fin_three` + `IsBigO.of_bound`; no new
   infrastructure.
4. Axiom-clean target with realistic ~80–120 LOC budget.
5. Strict net advance (sorry count stays at 0; one new public theorem).

**Approach** (follow the cycle 140 n = 2 template at
`Section550.lean:167–192` step-by-step):

### Step 0 (read precedent — first action of the cycle)

Open `OpenMath/Chapter5/Section550.lean` and re-read
`doublyCompanionMatrix_det_factorization_n_two` (lines ~167–192).
Note the proof sequence:

1. `unfold alphaPoly betaPoly`
2. `unfold doublyCompanionMatrix`
3. `norm_num [Fin.sum_univ_two, Matrix.det_fin_two]`
4. `ring_nf`
5. Restate the residue as `z^3 * (linear-in-z polynomial)` via
   `suffices h_factor : … =O[nhds 0] z^3` block.
6. `convert h_factor using 2; ring` to align the residue.
7. `Asymptotics.IsBigO.of_bound C` with explicit constant
   (sum of absolute values of coefficients).
8. `Metric.eventually_nhds_iff` + `⟨1, by norm_num, fun y hy => ?_⟩`
   to localize to `‖y‖ < 1`.
9. Norm bound via `norm_sub_le` + `mul_le_mul_of_nonneg_*` chain
   exploiting `‖y‖ ≤ 1`.

### Step 1 (compute the n = 3 residue — paper algebra first)

Before touching Lean, expand:

* `det(I − z X)` for `X = doublyCompanionMatrix α β` at `n = 3` via
  `Matrix.det_fin_three`. The matrix `1 − z X` at `n = 3` has shape
  ```
  ! [ 1 + z α 0,           z α 1,           z (α 2 + β 2);
      −z,                  1,               z β 1;
      0,                  −z,               1 + z β 0 ]
  ```
  (verify against the `doublyCompanionMatrix` definition — row-0 case
  uses `-α j` for `j.val + 1 ≠ n`, the corner `-α (n−1) − β (n−1)`,
  and non-zero rows use `-β (n − i.val − 1)` for `j.val + 1 = n` and
  `1` for `i.val = j.val + 1`).
* `alphaPoly α z = 1 + α 0 · z + α 1 · z² + α 2 · z³`.
* `betaPoly β z = 1 + β 0 · z + β 1 · z² + β 2 · z³`.
* Compute `α(z) · β(z)` symbolically up to and including the `z³`
  term.
* Subtract: the `z⁰`, `z¹`, `z²`, `z³` coefficients **must cancel
  exactly** (this is the content of Theorem 550A).
* The residue's leading `z⁴` coefficient should be
  `−(α 0 · β 2 + α 1 · β 1 + α 2 · β 0)` (matching the n = 2 pattern
  `−(α 0 · β 1 + α 1 · β 0)`).
* Higher-order terms `z⁵`, `z⁶` are products of `α_i · β_j` with
  `i + j ≥ 4`.

**If the paper expansion does NOT show the z⁰…z³ coefficients
cancelling, STOP and re-check the matrix entries against the
definition** — this is the most common source of error and a
miscomputation here will burn the entire cycle. The cancellation is
the textbook claim itself, so it MUST hold.

### Step 2 (Lean encoding)

1. Stub the theorem statement (analogous to n = 2 but with
   `(fun z : ℂ => z ^ 4)` as the bound).
2. `unfold alphaPoly betaPoly`.
3. `unfold doublyCompanionMatrix`.
4. `norm_num [Fin.sum_univ_three, Matrix.det_fin_three]` — verify
   `Fin.sum_univ_three` exists (it does in Mathlib; if it doesn't
   match, fall back to `Fin.sum_univ_succ` chained twice).
5. `ring_nf` to canonicalize the residue.
6. `suffices h_factor : (fun z : ℂ => z^4 * (residue-polynomial-in-z))
       =O[nhds 0] (fun z : ℂ => z^4)` — write the residue polynomial
   from the paper expansion of Step 1.
7. `convert h_factor using 2; ring`.
8. `Asymptotics.IsBigO.of_bound C ?_` with `C := Σ ‖coefficient‖`
   (sum of norms of all residue coefficients).
9. `Metric.eventually_nhds_iff` + `⟨1, by norm_num, fun y hy => ?_⟩`.
10. `norm_num [mul_assoc, mul_comm, mul_left_comm]`.
11. Bound the inner residue via `norm_sub_le` recursively.

### Step 3 (verify and commit)

* `lake env lean OpenMath/Chapter5/Section550.lean` — clean.
* `lake build OpenMath.Chapter5.Section550` — clean (this is what
  `lean_verify` consults for axiom checks; do not skip it).
* `lean_verify OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_three`
  — must return `[propext, Classical.choice, Quot.sound]` only.
* Update `lean_status.json` row for `thm:550A` to bump cycle marker
  and note the new n = 3 stepping stone.
* Update `plan.md` Chapter 5 row for `thm:550A` to mention n = 3
  alongside the existing n = 1, n = 2 progress.
* Update `.prover-state/issues/thm_550A_general_n.md`'s "Status
  update" to add a cycle 144 entry: "n = 3 stepping stone landed
  axiom-clean via `Matrix.det_fin_three` + `IsBigO.of_bound`. Three
  data points (n = 1, 2, 3) now confirm the leading-coefficient
  pattern `−Σᵢ α_i · β_{n−i} z^{n+1}`. General-`n` closure remains
  deferred."

## What NOT to try this cycle

1. **Do NOT attempt `thm:550A` at general `n`.** Cycle 141 cancelled
   Aristotle Job A at 6% after 24 h; manual cofactor expansion or
   eigenvalue-density argument is multi-cycle infrastructure (per
   `.prover-state/issues/thm_550A_general_n.md`). Stay at concrete
   `n = 3`.

2. **Do NOT re-submit `thm:550A` general-`n` to Aristotle.** The 24 h
   wall-clock cancellation is dispositive; another batch will burn
   compute without converging.

3. **Do NOT raise `maxHeartbeats`** if Step 2 fails. If the residue
   expansion blows up `norm_num` or `ring_nf`, decompose into
   per-coefficient `have` lemmas that reduce each `z^k` coefficient
   in isolation.

4. **Do NOT use `decide` on the matrix-entry case split.** The matrix
   entries are `ℂ`-valued (not Decidable). Use `fin_cases i; fin_cases j`
   + `simp [doublyCompanionMatrix]` instead — same template as
   cycle 138's `doublyCompanionMatrix_one_eq` lemma.

5. **Do NOT introduce new `def`s of named mathematical concepts**
   beyond the n = 3 statement of `thm:550A`. No new structures, no
   new predicates.

6. **Do NOT touch `scripts/autonomous_loop.py`.** Worker rule per
   CLAUDE.md and `.prover-state/issues/tautology_scanner_false_positives.md`.

7. **Do NOT open `def:530B` / `def:530C` (Order relative to starting
   method) or `def:442A` (principal sheet)** — both are multi-cycle
   infrastructure investments per the cycle 142/143 strategy guidance.

8. **Do NOT attempt `thm:550B`, `thm:551B`, `thm:553A`, or `cor:550C`**
   — all depend on `thm:550A` general-`n` which is still deferred.

## Backup plan A — if Step 1 paper expansion shows non-cancellation

If, at Step 1, the `z⁰…z³` coefficients of `det(I − z X) − α(z) · β(z)`
do NOT cancel symbolically (i.e. you suspect a miscomputation rather
than a textbook error), STOP the n = 3 path and pivot to **Backup A:
def:530A r = 3 heterogeneous-stages witness**.

**Target**:

* Add `nontrivialThreeStageGRK : GeneralizedRungeKuttaMethod 3` with
  `b₀ := 3`, all-zero matrix/abscissae/weights (mirror of cycle 141's
  `nontrivialTwoStageGRK`).
* Add `mixedStages3 : Fin 3 → ℕ` returning `(1, 2, 3)`.
* Add `mixedMethod3 : (i : Fin 3) → GeneralizedRungeKuttaMethod (mixedStages3 i)`
  pattern-matching on `Fin 3` (constituents:
  `trivialGeneralizedRK`, `nontrivialTwoStageGRK`,
  `nontrivialThreeStageGRK`).
* Add `mixedStartingMethod3 : StartingMethod 3` and the witness
  `mixedStartingMethod3_isNonDegenerate`.
* Optionally add `mixedStartingMethod3_stages_pairwise_distinct`
  asserting `stages 0 ≠ stages 1 ∧ stages 1 ≠ stages 2 ∧
  stages 0 ≠ stages 2` to confirm the dependent design extends to
  three distinct stage counts.

**Location**: `OpenMath/Chapter5/Section530.lean`, after the existing
`mixedStartingMethod_*` block (around line 237).

**Estimated LOC**: ~80–100, axiom-clean.

**Why valid as backup**: extends cycle 141's heterogeneous-stages
design test from r = 2 to r = 3, confirming the dependent
`stages : Fin r → ℕ` field scales without combinatorial obstruction.

## Backup plan B — if both Priority 1 and Backup A stall

Pivot to **a negative L-stable r = 2 witness** for `def:520F`,
mirroring cycle 137's negative r = 1 witnesses on the r = 2 side:

**Target**: define a `padded2DImplicitMidpointGLM` (cycle 135's
`implicitMidpointGLM` lifted to r = 2 via the same
zero-channel padding scheme as `padded2DEulerGLM` /
`padded2DBackwardEulerGLM`) and prove
`padded2DImplicitMidpointGLM_not_isLStable` by reducing to cycle 137's
`implicitMidpointGLM_not_isLStable` (the r = 2 case inherits the
non-zero spectral radius from the r = 1 inner block).

**Estimated LOC**: ~120, axiom-clean.

**Use only if both Priority 1 and Backup A genuinely block.** Do NOT
use as a parallel deliverable.

## Cycle deliverable expectations

* **Strict net advance**: sorry count remains at 0; at minimum ONE
  new axiom-clean public theorem.
* **Faithfulness check** per CLAUDE.md: the n = 3 statement is a
  named instance of Theorem 550A's claim, not a new mathematical
  concept; no entity-JSON lookup needed beyond confirming the
  textbook claim's z⁰…z³ cancellation matches `entities/thm_550A.json`.
* **Tautology scanner**: zero hits on the new theorem.
* **No §513/§514/§520 cascade regressions**: if you touch
  `Section550.lean` only, this is automatic; if you also do Backup A,
  `Section530.lean` is independent of §513/§514 too.

## Process notes

* Aristotle is **not** the right tool this cycle (general-`n` failed;
  the n = 3 case is small enough to prove directly via Mathlib's
  fin-3 determinant infrastructure, and submitting would burn
  compute without speedup).
* If `Fin.sum_univ_three` doesn't exist, use `Fin.sum_univ_succ`
  chained twice OR `simp [Fin.sum_univ_succ, Fin.sum_univ_zero]`.
* Standard precedent: `Matrix.det_fin_three` exists in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` (already imported
  by `Section550.lean`).
* If the residue's leading constant is unmanageable (the `IsBigO.of_bound`
  constant `C := Σ ‖coefficient‖` may have ~6 terms for n = 3),
  factor out the bound into a separate `private theorem` so the
  main proof reads cleanly.
