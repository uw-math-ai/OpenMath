# Cycle 133 Strategy

## State summary

* Branch tip: `022e140 Cycle 132 — register thm:142D (i⇔ii) partial via textbook-named alias (axiom-clean)`.
* No sorry's anywhere in `OpenMath/`.
* Progress: 69 / 175.
* No pending Aristotle results.
* Cycles 128–132 produced a chain of small **definitional** /
  **registration** deliverables (def:525A, def:542A, def:551A, thm:142D
  partial). The non-vacuity witnesses for `def:542A` and `def:551A` are
  **structurally vacuous on the row-1+ clauses** because they are
  instantiated at `r = 1`, so the `∀ i ≠ 0, …` quantifiers range over
  an empty index set.
* Cycle 132's "Suggested next approach" lists three concrete options;
  this strategy adopts option 1 (substantive r=2 IRK-stability witness)
  as Priority 1 because it directly closes the structural-vacuity gap
  introduced by cycles 130 and 131. Option 2 (`thm:551B`) is held as a
  stretch goal for the back of the cycle if Priority 1 lands early.

## Priority 1 — Substantive r=2 witness for `def:551A` (~80 LOC)

### What

Strengthen the non-vacuity of `GeneralLinearMethod.IsIRKStable`
(`OpenMath/Chapter5/Section520.lean:586`) by constructing a small
`s = 1, r = 2` GLM and proving it is IRK-stable. Unlike
`explicitEulerGLM_isIRKStable` (cycle 131), which has `r = 1` and so
satisfies `∀ i : Fin 1, i ≠ 0 → …` vacuously, the new witness has
`r = 2` and so the row-1 clauses become genuine universal statements
over `i = 1` that must be discharged by direct calculation.

### Where

Add the new GLM definition and witness theorem **immediately after**
`explicitEulerGLM_isIRKStable` at `Section520.lean:619` (i.e. before
the `/-! ### Theorem 520D …` heading at line 620). Keep the cycle 131
witness in place — the new substantive witness *complements* it; it
does not replace it.

### Construction (concrete)

Read `OpenMath/Chapter5/Section510.lean` first to confirm the field
list of `GeneralLinearMethod`. Then add:

```lean
/-- A degenerate `s = 1, r = 2` GLM used solely as a *substantive*
non-vacuity witness for `IsIRKStable` (cycle 133). The row-0 output
is forward-Euler-like; the row-1 output is a passively-decoupled
zero channel. The point of this method is NOT numerical interest;
it is to exhibit a `def:551A` witness in which the
`∀ i : Fin r, i ≠ 0 → …` clauses are non-vacuously discharged. -/
def padded2DEulerGLM : GeneralLinearMethod 1 2 where
  A := !![0]
  U := !![1, 0]
  B := !![1; 0]
  V := !![1, 0; 0, 0]
```

(If `GeneralLinearMethod` has additional structural fields beyond
`A, U, B, V` — e.g. `c : Fin s → ℝ` for abscissae — supply zero or
the canonical defaults. Mimic the pattern used by `explicitEulerGLM`
elsewhere in the file.)

```lean
/-- **Substantive** non-vacuity witness for `IsIRKStable`:
`padded2DEulerGLM` (s = 1, r = 2) is inherently Runge–Kutta stable
with `X = 0`. Unlike the cycle 131 witness `explicitEulerGLM`
(r = 1), the `∀ i ≠ 0` quantifiers in the residual clauses here
range over the *non-empty* index `i = 1`, so the conclusion follows
from direct entry-wise computation rather than vacuous instantiation. -/
theorem padded2DEulerGLM_isIRKStable :
    padded2DEulerGLM.IsIRKStable := by
  refine ⟨?_, 0, ?_, ?_⟩
  · -- (551a): V's first column equals e₀.
    intro i
    fin_cases i <;> simp [padded2DEulerGLM]
  · -- B*A − 0*B = B*A, with row 1 = 0 because B[1][0] = 0.
    intro i j hi
    fin_cases i
    · exact absurd rfl hi
    · fin_cases j
      simp [padded2DEulerGLM, Matrix.mul_apply, Fin.sum_univ_succ,
            Fin.sum_univ_zero]
  · -- B*U − 0*V + V*0 = B*U, with row 1 = [0, 0] because B[1][0] = 0.
    intro i j hi
    fin_cases i
    · exact absurd rfl hi
    · fin_cases j <;>
        simp [padded2DEulerGLM, Matrix.mul_apply, Fin.sum_univ_succ,
              Fin.sum_univ_zero]
```

### Why this is substantive (vs. cycle 131)

Under `Fin 2`, the clauses `∀ i : Fin 2, i ≠ 0 → P i` are NOT
vacuously true — they apply concretely at `i = 1`. The proof above
must therefore actually compute `(B * A) 1 0` and `(B * U) 1 j`
and verify they equal 0. This is a real (if small) calculation
on a non-empty index, contrasted with cycle 131 where `Fin 1`
makes `∀ i, i ≠ 0 → …` vacuously true via
`absurd (Subsingleton.elim i 0) hi`.

### Verification checklist

After landing the construction:

1. `lake env lean OpenMath/Chapter5/Section520.lean` must exit 0.
2. `lake build OpenMath.Chapter5.Section520` must exit 0 (so the
   `.olean` is up to date for downstream files and for the axiom check).
3. `#print axioms OpenMath.Chapter5.Section520.padded2DEulerGLM_isIRKStable`
   must return `[propext, Classical.choice, Quot.sound]` only.
4. `#print axioms OpenMath.Chapter5.Section520.explicitEulerGLM_isIRKStable`
   must STILL return the same axiom-clean set (no regression).
5. **No new `sorry`** introduced anywhere.

### Faithfulness analysis (do NOT skip)

The new witness must clear the pre-commit faithfulness checklist
in `CLAUDE.md`. For `padded2DEulerGLM`:

* It is a *new* `def`, but it is NOT a *named mathematical concept* —
  it is an instance/witness, analogous to the existing
  `explicitEulerGLM` and `implicitMidpointGLM`. Faithfulness check
  ("definition matches textbook") is therefore N/A; faithfulness check
  for *witnesses* reduces to "does this object actually satisfy the
  predicate, with the predicate unchanged?". Yes — the proof discharges
  `IsIRKStable` directly.

For `padded2DEulerGLM_isIRKStable`:

* Conclusion `padded2DEulerGLM.IsIRKStable`. No hypotheses. No
  tautology / identity / hypothesis-strength concerns — the proof is
  genuinely entry-wise computation.
* The cycle 131 witness `explicitEulerGLM_isIRKStable` is preserved
  verbatim. The new witness is additive evidence of non-vacuity.

The cycle 133 task results §"Faithfulness check" must explicitly
record:

> Entity ID: def:551A. Lean predicate `IsIRKStable` already captures
> textbook conditions (cycle 131); this cycle adds a second non-vacuity
> witness (`padded2DEulerGLM_isIRKStable`) where the row-1 quantifiers
> are non-vacuous. Captures: same predicate, no change. Justification
> for divergence: none — this is strengthening evidence, not a
> definition change.

### Approach guardrails (do NOT do these)

* **Do NOT modify the `def:551A` predicate** to "make it stronger".
  The textbook signature is fixed and was settled in cycle 131; the
  point of this cycle is to exhibit a more substantive *inhabitant*,
  not to change the predicate.
* **Do NOT construct a witness with `r = 1`** — that is exactly the
  vacuity case cycle 131 already covered.
* **Do NOT include the textbook §551 method-class context**
  (`p = q`, `s = r = p + 1`, `A` diagonally implicit, `λ ≥ 0`,
  `ρ(V̇) = 0`) inside the witness GLM. Those are scope conditions
  for *which* methods are studied, not part of the IRK-stability
  predicate. The cycle 131 docstring on the predicate is explicit
  about this — repeating the same scoping in the witness would be
  hypothesis smuggling on the witness side.
* **Do NOT reach for Aristotle.** The proof is two ~5-line direct
  computations; round-trip cost would dwarf the proof.

### If the proof is harder than expected

If `simp` plus `Matrix.mul_apply` does not close the row-1 clauses
in one step:

1. Try `decide` after fully concretising `padded2DEulerGLM` (the
   matrix entries are literal rationals, so decidability should
   reduce the goal).
2. Try `Fin.sum_univ_two` / `Fin.sum_univ_one` instead of
   `Fin.sum_univ_succ`.
3. As a fallback, prove the two row-1 clauses as separate `have`
   blocks using `Matrix.mul_apply` + direct numerical computation.

Do **not** generalise the GLM (e.g. parameterise `V[1][1] = λ`) to
"hide" the proof complexity — keep the witness fully concrete.

### Update `lean_status.json`?

`def:551A` is already `formalized` in `lean_status.json` (cycle 131).
Do NOT downgrade or modify the row — adding a second witness does
not change the formalization status. Optionally append a short note
in the `notes` field if the schema permits.

### Update `plan.md`?

Bump the `def:551A` row's status note to mention the substantive
witness, e.g.:

```
- [x] `def:551A` **Inherent Runge–Kutta stability** (§551) —
  OpenMath/Chapter5/Section520.lean (cycle 131 predicate +
  vacuous r=1 witness; cycle 133 substantive r=2 witness
  `padded2DEulerGLM_isIRKStable`)
```

The progress count stays at 69 / 175 (still 1 entity).

### Commit message template

```
Cycle 133 — strengthen def:551A non-vacuity via substantive r=2
witness padded2DEulerGLM_isIRKStable (axiom-clean)
```

## Priority 2 (stretch — only if Priority 1 lands with >25 min remaining)

Attempt `thm:551B` *Single Non Zero Eigenvalue Stability* by reading
its entity record at `extraction/formalization_data/entities/thm_551B.json`,
sketching whether the textbook proof requires the §550 doubly-companion-
matrix infrastructure, and either:

(a) **If the proof reduces to a short spectral argument on `V` alone**
    (e.g. `V` upper-triangular with single non-zero eigenvalue ⇒
    stable), proceed with a sorry-first scaffold then close.

(b) **If §550 infrastructure is required**, write a one-paragraph
    issue at `.prover-state/issues/thm_551B_blocked_on_550.md`
    documenting the dependency and stop. Do NOT introduce a partial
    scaffold for thm:551B in this cycle if (b) applies.

This priority is genuinely optional. It is fine — and expected — for
cycle 133 to land Priority 1 only.

## What NOT to attempt this cycle

* `thm:142D` clauses (iii) / (iv) — Mathlib still lacks Jordan
  canonical form and rescaled Schur. Per
  `.prover-state/issues/jordan_canonical_form_missing.md`, this is a
  3–5 cycle infrastructure investment and is not on the critical path.
* `def:381F` (P-equivalent) — blocked on the deferred `reducedMethod`
  construction (`.prover-state/issues/reduced_method_deferred.md`).
* `thm:356C`, `cor:356D`, `thm:357D` — blocked on the deferred
  AN-stability infrastructure (`.prover-state/issues/AN_stability_deferred.md`).
* `def:530A`, `thm:535A`, `thm:541A`, `def:451A` — each requires
  substantial new structural definitions and is unlikely to fit in a
  single cycle.
* **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer
  territory per `.prover-state/issues/tautology_scanner_false_positives.md`.
* **Do NOT introduce `axiom` or `constant`** anywhere.
* **Do NOT raise `maxHeartbeats`** above 200000 — the proof is small
  enough that the default bound is plentiful.
* **Do NOT use Aristotle for this cycle** — the deliverable is two
  ~5-line entry-wise computations; submission overhead exceeds proof
  cost.

## Cycle deliverable bar

* **Acceptable**: Priority 1 lands axiom-clean with `lean_status.json`
  + `plan.md` updated, faithfulness check completed, commit pushed.
  Progress stays 69 / 175.
* **Better**: Priority 1 + Priority 2(a) lands with `thm:551B`
  closed (advancing 69 → 70 / 175).
* **Acceptable fallback**: Priority 1 + Priority 2(b) (thm:551B
  blocker issue file written, no scaffold introduced). Progress
  stays 69 / 175 but the next cycle has a clear plan.
* **Unacceptable**: zero changes. Per `CLAUDE.md`, "a cycle with
  zero changes is unacceptable. At minimum, decompose a sorry or
  write an issue." Priority 1 is approximately 80 LOC including
  proof; this is a clean single-cycle deliverable.

## Pointers

* Cycle 131 implementation (mirror this style):
  `OpenMath/Chapter5/Section520.lean:586-619`.
* `GeneralLinearMethod` structure:
  `OpenMath/Chapter5/Section510.lean` (read this first to confirm
  the field list before writing `padded2DEulerGLM`).
* Existing concrete-GLM examples (for matrix-literal patterns):
  search `Section520.lean` and `Section510.lean` for
  `explicitEulerGLM` and `implicitMidpointGLM`.
* Faithfulness checklist: `CLAUDE.md` §"Pre-Commit Faithfulness
  Checklist".
