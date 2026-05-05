# Cycle 131 — Strategy

## TL;DR

**Primary**: formalise `def:551A` *Inherent Runge–Kutta stability* in
`OpenMath/Chapter5/Section520.lean`. Predicate + 1×1 trivial
non-vacuity witness via `explicitEulerGLM`. Pattern is the same as
cycle 130 (`def:542A`) and cycle 128 (`def:525A`): encode the textbook
conditions, prove a trivial-dimension witness, land axiom-clean.
Progress goes 67 → 68 / 175.

**Backup A** (only if the primary deliverable cannot land within
budget): substantive `implicitMidpointGLM_isRKStable` with
`R(z) = (1 + z/2)/(1 − z/2)` per cycle 130's "Suggested next approach"
item 3. Bumps the existing `def:542A` witness slot to a substantive
inhabitant; ~25 LOC using `Matrix.det_fin_one`. Does NOT bump entity
count, but is a useful strengthening if §550 infra blocks the
primary path.

There are **no sorry's in the codebase** and **no pending Aristotle
results**, so this cycle is a clean greenfield definition + witness
landing.

## A. Primary deliverable — `def:551A` Inherent Runge–Kutta stability

### Textbook statement (`extraction/formalization_data/entities/def_551A.json`)

> A general linear method `(A, U, B, V)` is "inherently Runge–Kutta
> stable" if `V` is of the form (551a) and the two matrices
>
>     `BA − XB`   and   `BU − XV + VX`
>
> are zero except for their first rows, where `X` is some matrix.

Equation (551a):
```
V = [[1, v],
     [0, V̇]]
```
with `ρ(V̇) = 0` (per the textbook `Context`).

Bookkeeping (also from the textbook context):
* `p = q`, `s = r = p + 1`, `A` diagonally implicit, `λ ≥ 0` on its
  diagonal.

### Encoding decision — what goes IN the predicate vs. left to context

The textbook's `Context` block lists side-conditions (`p = q`,
`s = r`, `A` diagonally implicit, `λ ≥ 0`, `ρ(V̇) = 0`) that the
*definition* itself does NOT mention — they describe the methods
the textbook is *interested in* when discussing IRK stability,
not which methods *are* IRK-stable. The definition (the LaTeX
`\begin{definition}...\end{definition}` block) names exactly two
conditions:

1. `V` has the form (551a) — i.e. `V[0][0] = 1`, `V[i][0] = 0` for
   `i > 0`, leaving `V[0][1..]` and `V[1..][1..]` free.
2. `∃ X, BA − XB` and `BU − XV + VX` are zero except for their
   first rows.

**Strategy: encode exactly these two conditions in `IsIRKStable`.
Nothing more.** Including `ρ(V̇) = 0` or `A` diagonally implicit
would be hypothesis smuggling — the textbook treats them as
*assumptions about which methods we study*, not as part of the
IRK-stable predicate. (Compare to `def:542A` cycle 130, which
similarly encoded only the factorisation, leaving `R` rationality
to downstream theorems.)

### Exact Lean shape (target signature)

Place between `IsRKStable` and the existing §521 block in
`OpenMath/Chapter5/Section520.lean` (justification: `def:551A`
imports `def:542A` directly and adds no fresh imports beyond what
Section520 already opens — `Matrix`, `Fin`, `Complex`, etc.).

```lean
/-- **Definition 551A (Inherent Runge–Kutta stability).**

A general linear method `(A, U, B, V)` is *inherently Runge–Kutta
stable* if:

1. The `V` block has the form `V[0][0] = 1`, `V[i][0] = 0` for
   `i ≠ 0` (i.e. its first column is the standard basis vector
   `e₀`).
2. There exists a matrix `X : Matrix (Fin r) (Fin r) ℝ` such that
   the matrices `B·A − X·B` and `B·U − X·V + V·X` are zero outside
   their first rows.

This is Butcher's eq (551b)/(551c) condition; see §551 p. 460.
Method-class side-conditions (`p = q`, `s = r = p + 1`, `A`
diagonally implicit, `ρ(V̇) = 0`) are CONTEXT for which methods
are studied — they are NOT part of this predicate. Compare
`def:542A` (cycle 130), which similarly encodes only the
factorisation. -/
def GeneralLinearMethod.IsIRKStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  -- V has the block form (551a): first column is e₀.
  (∀ i : Fin r, M.V i 0 = if i = 0 then 1 else 0) ∧
  ∃ X : Matrix (Fin r) (Fin r) ℝ,
    -- BA − XB has all entries 0 outside row 0.
    (∀ (i : Fin r) (j : Fin s), i ≠ 0 →
      (M.B * M.A - X * M.B) i j = 0) ∧
    -- BU − XV + VX has all entries 0 outside row 0.
    (∀ i j : Fin r, i ≠ 0 →
      (M.B * M.U - X * M.V + M.V * X) i j = 0)
```

Notes on the encoding choices:

* The "first column of V is e₀" form captures (551a) without needing
  to extract a sub-matrix `V̇`. We are saying `V[0][0] = 1` and
  `V[i][0] = 0` for `i > 0`. The `v` row-vector and `V̇` block remain
  free — exactly what the textbook says.
* "Zero except for first rows" → `i ≠ 0 → (·) i j = 0` for all `j`.
  This is the cleanest faithful translation; no sub-matrix
  extraction needed.
* The `r = 0` edge case: `Fin 0` is empty, so both clauses are
  vacuously true and `IsIRKStable` is trivially satisfied. Acceptable
  behaviour for a degenerate empty-matrix GLM (compare cycle 130's
  `def:542A` `r = 0` analysis).

### Non-vacuity witness — `explicitEulerGLM_isIRKStable`

`explicitEulerGLM` has `s = r = 1`. With only one row, "zero except
for first row" is vacuously true (only `i = 0` exists). The first
column of `V = !![1]` is `!![1]`, satisfying clause (1) trivially:
`V 0 0 = 1` and there are no `i ≠ 0` indices. So the witness is:

```lean
theorem explicitEulerGLM_isIRKStable :
    explicitEulerGLM.IsIRKStable := by
  refine ⟨?_, ?_⟩
  · intro i
    -- V[i][0] = 1 if i = 0 else 0; for r = 1 only i = 0 exists.
    fin_cases i
    simp [explicitEulerGLM]
  · -- Pick X = 0; both clauses are vacuous since i : Fin 1 forces i = 0.
    refine ⟨0, ?_, ?_⟩
    · intro i j hi
      exact absurd (Subsingleton.elim i 0) hi
    · intro i j hi
      exact absurd (Subsingleton.elim i 0) hi
```

Fallback closer if `Subsingleton.elim` doesn't fire cleanly:
`fin_cases i; exact absurd rfl hi`. Or extract `i.val = 0` via
`Fin.val_eq_zero_iff` then `omega`.

### Proof tactics — try in this order

1. `refine ⟨?_, ?_⟩` to split the conjunction.
2. Clause 1 (V's first column): `intro i; fin_cases i; simp
   [explicitEulerGLM]`. If `simp` doesn't close it, the goal will
   be `(!![1]) 0 0 = 1` which is `rfl` after `Matrix.cons_val_zero`.
3. Clause 2 (∃ X): `refine ⟨0, ?_, ?_⟩` then
   `intro i j hi; exact absurd (Subsingleton.elim i 0) hi`. If
   `Subsingleton.elim` doesn't typecheck on `Fin 1`, fall back to
   `fin_cases i; exact absurd rfl hi`.

## B. Placement and scope

Insert the new code in `OpenMath/Chapter5/Section520.lean` immediately
**after** `explicitEulerGLM_isRKStable` (cycle 130 deliverable, near
the bottom of the file). This colocates the two §54/§55 stability
predicates that share infrastructure. Do NOT create a new
`Section551.lean` for a single definition + 1-line witness — the
file overhead isn't worth it; we can split later if §55 grows.

Estimated total: ~50 LOC (predicate + docstring + witness).

## C. Required hygiene

1. **Update `extraction/formalization_data/lean_status.json`** for
   `def:551A`:
   ```json
   {
     "id": "def:551A",
     "status": "formalized",
     "lean_file": "OpenMath/Chapter5/Section520.lean",
     "lean_symbol": "OpenMath.Chapter5.Section510.GeneralLinearMethod.IsIRKStable",
     "cycle": 131,
     "axioms": ["propext", "Classical.choice", "Quot.sound"]
   }
   ```
   (Match the existing field shape used for `def:542A` cycle 130.)
2. **Update `plan.md`** §55 row for `def:551A`: change `[ ]` to `[x]`,
   add annotation `def:551A — OpenMath/Chapter5/Section520.lean`.
   Bump progress count `67 / 175` → `68 / 175`.
3. **Verify axiom-clean** after `lake build`:
   ```
   #print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.IsIRKStable
   #print axioms OpenMath.Chapter5.Section510.explicitEulerGLM_isIRKStable
   ```
   Both should return `[propext, Classical.choice, Quot.sound]` only.
   IMPORTANT: per cycle 072 lesson, run `lake build OpenMath.Chapter5.Section520`
   *before* `#print axioms` to refresh the `.olean` cache (otherwise
   stale-cache `sorryAx` false positives).
4. **Tautology scanner check**: after the edit, run
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   from project root. Expected: zero new hits beyond pre-cycle
   baseline. The `hi` binder name (without underscore) is fine.

## D. What NOT to do

* Do **NOT** include `ρ(V̇) = 0`, `p = q`, `s = r = p + 1`, `A`
  diagonally implicit, or `λ ≥ 0` in the `IsIRKStable` predicate.
  These are textbook *context* about which methods are studied,
  not part of the IRK-stability *predicate*. Putting them in would
  be hypothesis smuggling — exactly the failure mode flagged in
  the planner-faithfulness-spotcheck memory and the cycle 113/123
  `_hc_nn`/`_hc_le_one` analysis.
* Do **NOT** introduce `axiom`/`constant` declarations.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** create a new `OpenMath/Chapter5/Section551.lean` for
  this single definition — colocate in `Section520.lean` per §B.
* Do **NOT** attempt the substantive `implicitMidpointGLM_isIRKStable`
  witness this cycle. Trivial 1×1 explicit-Euler witness is
  sufficient for non-vacuity. A substantive witness would require
  computing `BA − XB`, `BU − XV + VX` for a 2×2 implicit-midpoint
  encoding (s = r = 2 to make the predicate non-vacuous on more
  than the row-vacuous level), which is multi-cycle scope.
* Do **NOT** define a `V_dot` projection or a `IsBlockOne v V_dot`
  helper structure for the V-form clause. The direct
  "first column is e₀" formulation is faithful, terse, and avoids
  building infrastructure that downstream theorems may not need.
  If `thm:551B` or `thm:553A` later needs `V̇`, build the projection
  *then* — not preemptively.
* Do **NOT** try to formalise `thm:550A` (Doubly companion matrices)
  this cycle. The dependency listed on `def:551A` is `llm_dependency`
  (weak); we do NOT need doubly companion matrices to STATE IRK
  stability. They become relevant for `thm:551B` / `thm:553A`
  characterisations.
* Do **NOT** poll Aristotle. There are no pending submissions and
  the cycle is a clean greenfield landing.
* Do **NOT** modify `scripts/autonomous_loop.py` or any loop
  infrastructure (per CLAUDE.md and the standing
  `tautology_scanner_false_positives.md` issue).

## E. Aristotle batch (NOT needed this cycle)

The witness is a 5-line trivial closure on a 1×1 method; the
predicate body has no `sorry`. Aristotle would have nothing
useful to attack. **Skip the batch this cycle.**

If the primary closure unexpectedly stalls (e.g. the witness's
matrix-entry simp doesn't fire), then submit a single-job batch
asking Aristotle to close `explicitEulerGLM_isIRKStable` — with
the predicate body and the GLM definition as context. Sleep 30
min; check once; proceed with manual closure either way per
CLAUDE.md.

## F. Backup deliverable (only if primary stalls past 90 min)

If the primary stalls — e.g. the `Subsingleton.elim` fallback ladder
all fails on `Fin 1`, or the matrix-arithmetic `simp` produces a
goal that doesn't reduce — pivot to:

**Backup A — substantive `implicitMidpointGLM_isRKStable`**

Add a *substantive* `implicitMidpointGLM_isRKStable` companion to
the existing trivial witness (cycle 130 already has the witness via
the explicit-Euler-shape factorisation; this backup adds the
implicit-midpoint witness with a non-trivial rational `R`).

* Mathematical recipe: `M(z) = V + zB(I−zA)⁻¹U`. With
  `A = !![1/2]`, `(I − z·A) = !![1 − z/2]`, so
  `(I − z·A)⁻¹ = !![1/(1 − z/2)]`. Then
  `M(z) = !![1] + z · !![1] · !![1/(1−z/2)] · !![1]
        = !![1 + z/(1−z/2)]
        = !![(1 − z/2 + z)/(1 − z/2)]
        = !![(1 + z/2)/(1 − z/2)]`.
  Hence `Φ(w, z) = w − (1 + z/2)/(1 − z/2)`, factoring as
  `w^0 · (w − R(z))` with `R(z) = (1 + z/2)/(1 − z/2)`.
* Lean tools: `Matrix.det_fin_one`, `Matrix.inv_def`, `field_simp` /
  `Complex.field_simp`. Watch the `1 − z/2 = 0` singularity — guard
  with `(hz : 1 - z/2 ≠ 0)` or work in the algebraic-completion form
  using polynomial-clearing `(1 − z/2) · M(z) = ...`. The
  factorisation in `IsRKStable` doesn't require explicit
  invertibility because it's a polynomial identity in `w` for fixed
  `z`; if `(1 − z/2)` vanishes choose `R(z) := 0` (the degenerate
  case). Estimated ~25 LOC.
* Updates: add a new theorem name `implicitMidpointGLM_isRKStable`
  (do NOT overwrite the existing `explicitEulerGLM_isRKStable`
  cycle 130 attribution). `lean_status.json` for `def:542A` may
  optionally gain a `secondary_witness` field, but the primary
  status row stays as cycle 130's.

This does NOT bump entity count (67/175 stays), but it strengthens
non-vacuity for `def:542A`.

If the primary AND backup A both stall past the cycle budget,
pivot to **Backup B**: write an issue file
`.prover-state/issues/cycle_131_def_551A_blockers.md` documenting
the stall point (specific tactic that didn't fire, specific term
that didn't unify) and propose the Aristotle batch for cycle 132.
A cycle with a structured issue file + minimal commit is acceptable
under CLAUDE.md ("a cycle with zero changes is unacceptable; at
minimum decompose a sorry or write an issue").

## G. Faithfulness checklist (run BEFORE commit)

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

* [ ] `def:551A` JSON quote pasted into the cycle 131 task results.
* [ ] Confirm `IsIRKStable`'s body matches the textbook's two
      conditions (V form + ∃ X with first-row-only nonzero
      residuals). Confirm we're NOT smuggling `ρ(V̇) = 0` /
      `A` diagonally implicit / `p = q` etc. into the predicate.
* [ ] **Definition smuggling check**: confirm the predicate is NOT
      defined as something tautologically true on the trivial
      witness alone. The 1×1 case being vacuous is fine —
      every dimension-`r ≥ 2` GLM is constrained by the predicate.
* [ ] **Tautology check**: `explicitEulerGLM_isIRKStable`'s
      conclusion `explicitEulerGLM.IsIRKStable` is NOT a hypothesis
      of the theorem (there are no hypotheses). Genuine work is
      done in the proof. ✓
* [ ] **Hypothesis strength check**: predicate has no hypotheses.
      Witness theorem has no hypotheses. ✓
* [ ] **Absent theorem check**: no `sorry`-promised content;
      both deliverables are fully proved. ✓
* [ ] **Axiom check**: `[propext, Classical.choice, Quot.sound]`
      only, after `lake build` cache refresh. ✓

## H. Commit message template

```
Cycle 131 — formalize def:551A Inherent Runge–Kutta stability (axiom-clean)

* New predicate `GeneralLinearMethod.IsIRKStable` in
  OpenMath/Chapter5/Section520.lean encoding Butcher §551:
  V's first column is e₀, plus ∃ X with BA-XB and BU-XV+VX
  zero outside their first rows.
* Non-vacuity: explicitEulerGLM (s=r=1) trivially satisfies.
* Faithfulness: predicate encodes ONLY the textbook definition's
  two conditions; method-class context (ρ(V̇)=0, p=q, A
  diagonally implicit) deliberately not smuggled in.
* lean_status.json + plan.md updated; progress 67 → 68 / 175.
```

## I. End-of-cycle bookkeeping

After commit, write `.prover-state/task_results/cycle_131.md`
with the standard sections (Worked on / Approach / Result /
Faithfulness check / Dead ends / Discovery / Suggested next).
For "Suggested next approach", point at one of:

* `def:530A` *non-degenerate* (§53 leaf, definition shape).
* `thm:541A` *DIMSIM types* (classification, may need lookup).
* `thm:535A` *underlying one-step method (GLM)* (theorem, §535).
* Substantive `implicitMidpointGLM_isIRKStable` strengthening
  (parallel to backup A).

The planner can pick based on availability of dependencies and
cycle-pacing.
