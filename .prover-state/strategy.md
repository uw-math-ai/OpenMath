# Strategy — Cycle 086

## Cycle target

Formalize **`def:520A` — stability matrix `M(z)` of a general linear
method** (Butcher §520, p. 418).

> **Textbook statement** (`extraction/formalization_data/entities/def_520A.json`):
> "For a general linear method `(A, U, B, V)`, the 'stability matrix'
> `M(z)` is defined by
>
>   `M(z) = V + z · B · (I − z·A)⁻¹ · U`."

This is a **single-cycle definition + non-vacuity** deliverable.
Predecessor cycles 083/084/085 closed the §510 trilogy
(`def:510A`, `def:510B`, `def:510C`); §520 is the natural next
chapter-5 entry point per `plan.md` ordering, and the cycle 085
worker explicitly recommended it as the next target ("tackle §520
first to build out a wider stability landscape before committing to
the bigger `def:512A` push").

No Aristotle results are pending. No active sorries in the codebase.

## Why this target (and not def:512A)

* **`def:520A`** = a concrete formula with one infrastructure piece
  (matrix resolvent over ℂ). Fits in 1 cycle. Unblocks `def:520C`,
  `def:520E`, `def:520F`, `def:521A`, `thm:520B`, `thm:520D`,
  `thm:551B`.
* **`def:512A` (convergent GLM)** = a heavyweight predicate
  analogous to LMM `IsConvergent` (cycles 037–038), which itself
  took 2 cycles for the predicate alone and another 4 cycles
  (064–068) for any non-trivial witness/theorem. Defer 1+ cycles.

Strategic bonus: `def:520A`'s complex matrix resolvent
infrastructure **directly overlaps** with the
`AN_stability_deferred` issue
(`.prover-state/issues/AN_stability_deferred.md`). Once this cycle
lands, AN-stability becomes a much smaller follow-up — the
stability function `R(Z) = 1 + b'Z(I − AZ)⁻¹𝟙` for AN-stability
is a scalar specialization of the same `(I − z·A)⁻¹` resolvent
pattern.

## Priority 0 — Housekeeping

None this cycle.

## Concrete plan

### File to create

`OpenMath/Chapter5/Section520.lean` (new file — Chapter 5 currently
contains only `Section510.lean`).

### Imports

```lean
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import OpenMath.Chapter5.Section510
```

If a build error indicates a missing complex-analysis import for
`Complex.ofReal`, add `import Mathlib.Data.Complex.Basic` (already
listed) and verify with `lean_hover_info` on `Complex.ofReal` at the
first call site.

### Step 1 — Complexification helper

Define a small helper that lifts a real matrix to a complex matrix
via entrywise `Complex.ofReal`:

```lean
namespace OpenMath.Chapter5.Section520

open Matrix

/-- Lift a real matrix to a complex matrix entrywise via
`Complex.ofReal`. -/
def complexify {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map (Complex.ofReal ·)
```

Before writing this, run `lean_local_search "Matrix.map.*ofReal"`
and `lean_loogle "Matrix _ _ ℝ → Matrix _ _ ℂ"`. If Mathlib already
provides this idiom under another name (e.g. via
`Complex.ofRealHom.mapMatrix : Matrix m n ℝ →+* Matrix m n ℂ`),
prefer the existing version — algebraic homomorphism wrappers come
with `mul`/`add`/`one`/`zero` lemmas for free, which simplifies the
non-vacuity proofs below.

### Step 2 — Stability matrix definition

```lean
/-- **Definition 520A** — The *stability matrix* `M(z)` of a general
linear method `(A, U, B, V)` at a complex parameter `z` is

  `M(z) = V + z · B · (I − z·A)⁻¹ · U`.

The matrix `(I − z·A)⁻¹` is taken via `Matrix.inv` (Mathlib's
`Matrix.NonsingularInverse`); it equals the genuine resolvent when
`(I − z·A)` is invertible, and equals zero (the Mathlib convention)
otherwise. This is the standard partial-function-via-junk-value
encoding used throughout Mathlib for `Ring.inverse`, `Matrix.inv`,
etc.

Butcher (Definition 520A, p. 418): "For a general linear method
`(A, U, B, V)`, the 'stability matrix' `M(z)` is defined by
`M(z) = V + zB(I − zA)⁻¹U`."

The textbook implicitly restricts attention to `z` outside the
spectrum of `A⁻¹` (where `(I − z·A)` is invertible). Our encoding
matches the textbook formula on that domain and produces a
well-defined "junk" elsewhere; downstream theorems that need
invertibility (e.g. `def:520C` stability function via
`det(wI − M(z))`) will provide the appropriate hypothesis. -/
noncomputable def GeneralLinearMethod.stabilityMatrix
    {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
    (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  complexify M.V +
    z • complexify M.B *
      (1 - z • complexify M.A)⁻¹ *
      complexify M.U
```

Notes:
* `noncomputable` is required because `Matrix.inv` is noncomputable.
* `1` here is the `s × s` identity matrix (since `complexify M.A` is
  `s × s`). Let Lean infer it from context. If elaboration
  struggles, write
  `(1 : Matrix (Fin s) (Fin s) ℂ)` explicitly inside the resolvent.
* Index-shape sanity: the resolvent `(1 - z·A)⁻¹` is `s × s`. Then
  `B` is `r × s` (per `Section510.lean:69`), so
  `B · (1 - z·A)⁻¹` is `r × s`, and
  `B · (1 - z·A)⁻¹ · U` is `r × r`. The `+ V` term is `r × r`.
  Double-check by elaborating in Lean — if you get a dimension
  mismatch, re-read `Section510.lean:63–71` for the index
  conventions.

### Step 3 — Non-vacuity witnesses

Three small theorems documenting the definition's behavior:

**(a)** Behavior at `z = 0` (every GLM):
```lean
theorem GeneralLinearMethod.stabilityMatrix_at_zero
    {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r) :
    M.stabilityMatrix 0 = complexify M.V := by
  unfold GeneralLinearMethod.stabilityMatrix
  simp
```
This is the "`M(0) = V`" textbook fact. Establishes the definition
unfolds correctly on the simplest test. If `simp` alone doesn't
close, add `[zero_smul, zero_mul, mul_zero, add_zero]` to the simp
set.

**(b)** Concrete formula for explicit Euler:
```lean
theorem explicitEulerGLM_stabilityMatrix (z : ℂ) :
    OpenMath.Chapter5.Section510.explicitEulerGLM.stabilityMatrix z
      = !![1 + z] := by
  -- explicitEulerGLM has A = !![0], B = U = V = !![1].
  -- (1 - z·A) = (1 - z·!![0]) = 1 = !![1], so (1 - z·A)⁻¹ = !![1].
  -- M(z) = !![1] + z · !![1] · !![1] · !![1] = !![1 + z].
  ext i j
  fin_cases i; fin_cases j
  unfold GeneralLinearMethod.stabilityMatrix complexify
  simp [OpenMath.Chapter5.Section510.explicitEulerGLM,
        Matrix.mul_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.map_apply]
  ring
```
This is the load-bearing non-vacuity check. If the `simp` chain
doesn't close cleanly, the fallback decomposition is:

  1. First prove the auxiliary fact
     `(1 - z • complexify Section510.explicitEulerGLM.A) = 1`
     (since the A-block is `!![0]`) via
     `ext; fin_cases; simp [...]`.
  2. Then rewrite using `Matrix.inv_one` (verify the exact name
     with `lean_local_search "inv_one"` — alternative names:
     `Matrix.nonsing_inv_one`, `Matrix.one_inv`).
  3. Reduce the multiplication chain with
     `Matrix.one_mul` / `Matrix.mul_one`.
  4. Compute the final 1×1 matrix entry separately via
     `Matrix.cons_val_zero` / `Matrix.cons_val_fin_one`.

If the `1×1` matrix machinery (`!![1+z]` notation, `Matrix.cons`
unfolding) gives trouble, decompose further by computing each
matrix entry as a separate `have` block.

**(c)** (optional, only if needed) `complexify`-respects-zero
sanity:
```lean
@[simp]
theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℝ) = 0 := by
  ext; simp [complexify]
```
Skip if `complexify` is just `Matrix.map` and the simp set already
handles it. If you adopted the `Complex.ofRealHom.mapMatrix`
formulation (Step 1 alternative), most `simp` lemmas are inherited
and this auxiliary is unnecessary.

### Step 4 — Update bookkeeping

* `extraction/formalization_data/lean_status.json`: mark
  `def:520A` as `formalized` with
  `lean_file = "OpenMath/Chapter5/Section520.lean"` and
  `lean_symbol = "OpenMath.Chapter5.Section520.GeneralLinearMethod.stabilityMatrix"`.
* `plan.md` Chapter 5 row: change `[ ] def:520A` → `[x] def:520A
  **Introduction** (§520) — \`OpenMath/Chapter5/Section520.lean\``.
  Update progress count `56 / 175` → `57 / 175`.

## Aristotle batch (MANDATORY per CLAUDE.md)

The cycle's manual content is small (~80–120 lines total). Submit
**one** focused job to Aristotle in case the matrix-inverse
arithmetic for `explicitEulerGLM_stabilityMatrix` is fiddly:

* **Job 1**: just the `explicitEulerGLM_stabilityMatrix` theorem,
  with all surrounding definitions inlined. Aristotle is good at
  matrix-of-fixed-size goals where Mathlib has explicit
  `Matrix.cons` / `Matrix.smul_apply` / `Matrix.inv_one` lemmas.

Submit at the start of the cycle (after writing the sorry-first
scaffold for steps 1–3). Sleep 30 min. Return to incorporate
results, then close any remaining manually.

Do **NOT** submit the `complexify` definition or
`stabilityMatrix_at_zero` to Aristotle — the former is data, not a
proof, and the latter is a one-line `simp` that should not need any
help.

## Pre-commit faithfulness check

Run the CLAUDE.md checklist for each new declaration:

### `complexify`
* Definition. Type is `Matrix m n ℝ → Matrix m n ℂ`. Captures the
  textbook's implicit lift "treat the real GLM matrices as complex".
* No textbook entity — this is a private helper. Document as such
  in the docstring.

### `GeneralLinearMethod.stabilityMatrix`
* Quote textbook from `def_520A.json`:
  > "For a general linear method `(A, U, B, V)`, the 'stability
  > matrix' `M(z)` is defined by `M(z) = V + zB(I − zA)⁻¹U`."
* Lean type matches: `ℂ → Matrix (Fin r) (Fin r) ℂ` ✓.
* **Definition smuggling check**: does our definition capture the
  textbook's `M(z)` literally? Yes:
  `complexify V + z • complexify B * (1 - z • complexify A)⁻¹ *
  complexify U`. The `(I − z·A)⁻¹` uses Mathlib's `Matrix.inv`
  which agrees with the textbook resolvent on the invertible domain
  and produces a junk value (zero) elsewhere. Document this
  convention in the docstring as per the draft above. ✓
* No subtle hypothesis strengthening — the textbook silently
  assumes `(I − zA)` invertible at the point where it's evaluated,
  and our encoding makes this explicit (the value is "junk" outside
  that set). This is a faithful reformulation, not a strengthening.

### `stabilityMatrix_at_zero`
* Tautology check: conclusion `M(0) = complexify V` is not a
  hypothesis. ✓
* Identity check: proof unfolds the definition; not just `exact h`.
  ✓
* Hypothesis strength: hypothesis-free. ✓

### `explicitEulerGLM_stabilityMatrix`
* Tautology / identity / hypothesis-strength: all clean (concrete
  computation on a fixed instance).
* This is the non-vacuity witness — confirms `stabilityMatrix` is
  not a vacuous abstraction.

## Rules and prohibitions

### MUST NOT do this cycle
* Do **NOT** make `stabilityMatrix` a partial function over a
  subtype `{z : ℂ // (1 - z • complexify M.A).IsUnit}`. The
  `Matrix.inv` junk-value pattern is the standard Mathlib
  convention; subtypes here would create downstream friction.
* Do **NOT** define the stability function `Φ(w, z) =
  det(wI − M(z))` in this cycle. That is `def:520C`, a separate
  target.
* Do **NOT** define A-stability or instability region in this cycle
  — those are `def:520E` / `def:520F` / `def:520C`.
* Do **NOT** introduce `axiom` or `constant` if matrix-inverse
  computation hits a Mathlib gap. The fallback is decomposition into
  smaller `simp` steps (per Step 3 fallback above).
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** modify `Section510.lean` — `def:520A` should be
  self-contained in the new Section520 file.
* Do **NOT** edit `scripts/autonomous_loop.py` (per standing rule).

### Past-cycle traps to avoid
* The cycle 083 / 084 / 085 worker reports show the `1×1` matrix
  unfolding pattern (`fin_cases i; fin_cases j; simp [...]`) works
  reliably for explicit-Euler-GLM goals. Reuse it. Do **NOT** try
  `decide` on matrix-equality goals — the `Matrix` type is not
  decidable-equal.
* Per cycle 085 task results: `simp [explicitEulerGLM, dotProduct]`
  is sufficient for many 1×1 GLM goals; `Matrix.mulVec` in the simp
  set is often *redundant* (linter warning) once `dotProduct` is
  present. Don't over-specify the simp set; start minimal and add
  if needed.
* Per `feedback_finset_sum_le_sum_nbij_nonexistent.md`: do not use
  `Finset.sum_le_sum_nbij'` — not relevant here, but a reminder
  about Mathlib API gaps.
* Per `feedback_planner_faithfulness_spotcheck.md`: this strategy's
  proposed Lean encoding for `M(z)` was checked against Butcher
  §520's textbook formula. The encoding matches verbatim modulo
  the `Matrix.inv` junk-value convention (documented in the
  docstring). No definition smuggling.

## Worked-on-recently exclusion list

(Per CLAUDE.md "what was tried" log — not applicable to this
cycle's target, but flagged for awareness.)

* §404/405 LMM convergence work: cycles 064–072 are landed.
* §410 LMM order conditions: cycles 074–076, 079 landed.
* §383 Runge-Kutta group: cycles 077–082 landed.
* §510 GLM trilogy: cycles 083/084/085 landed.

`def:520A` is genuinely new ground.

## Phantom-verdict guard

If the cycle 086 supervisor inherits stale `attempts.md` rows
claiming "stuck on" or "commit failed" verdicts, treat them as
phantoms (per the long-standing pattern documented in
`consultant_advice_cycle_009.md` §A,
`consultant_advice_cycle_014.md` §A, and
`consultant_advice_cycle_015.md` §B). Verify with:

```bash
git log -1 --format='%H %s'
git rev-parse HEAD
git rev-parse origin/Main/Experiments
git diff --stat HEAD~1 HEAD
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/
```

If `HEAD == origin/Main/Experiments` and the diff is non-empty, the
prior cycle landed; ignore stale verdicts. The standing scanner-bug
issue is `.prover-state/issues/tautology_scanner_false_positives.md`
— do not re-file.

## Success criteria

Cycle 086 is a **success** if:

1. `OpenMath/Chapter5/Section520.lean` exists with at least
   `complexify`, `GeneralLinearMethod.stabilityMatrix`, and
   `stabilityMatrix_at_zero`. Compiles via
   `lake env lean OpenMath/Chapter5/Section520.lean`.
2. `lake build OpenMath.Chapter5.Section520` is clean.
3. `lean_verify` on `stabilityMatrix` (and the two theorems) returns
   axioms `[propext, Classical.choice, Quot.sound]` only.
4. `lean_status.json` and `plan.md` updated; progress 56 → 57.
5. Single zero-sorry commit pushed to `origin/Main/Experiments`.

The `explicitEulerGLM_stabilityMatrix` non-vacuity witness is
**preferred but not blocking**. If the matrix-inverse arithmetic
proves stickier than expected and Aristotle doesn't return a usable
proof, document the obstruction in
`.prover-state/issues/explicitEulerGLM_stabilityMatrix_deferred.md`
and ship the rest. (`stabilityMatrix_at_zero` alone is sufficient
non-vacuity per CLAUDE.md.) Be prepared to defer the explicit
witness, but try first — it shouldn't be hard.

## Suggested next-cycle target (not for this cycle)

After `def:520A` lands, the natural next §520 target is `def:520C`
(stability function `Φ(w, z) = det(wI − M(z))`, plus stability /
instability region). It depends only on `def:520A` (just landed)
and reuses the same complex matrix machinery, plus `Matrix.det`
from Mathlib. Estimated 1 cycle. Park the recommendation here so
cycle 087's planner has a head start.
