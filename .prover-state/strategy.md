# Cycle 028 Strategy

## Status snapshot

* Cycle 027 landed `def:370A` (symplectic Runge–Kutta methods) cleanly:
  `OpenMath/Chapter3/Section370.lean` with `symplecticityMatrix`,
  `IsSymplectic`, `implicitMidpoint`, and
  `implicitMidpoint_isSymplectic`. `lake build` clean, 0 sorries, 0
  tautology hits.
* No pending Aristotle results.
* No open sorries anywhere in `OpenMath/`.
* No active worker-level blocker. `picard_lindelof_bound_strengthening`
  and `jordan_canonical_form_missing` are §1/§142 backlog and remain
  non-blocking for current §3 work; `reduced_method_deferred` and
  `symmetry_group_equivalence` are also dormant. Do **not** touch them
  this cycle.

## Cycle-028 target — `def:357B` (algebraically stable)

Formalize `def:357B` as a single new file
`OpenMath/Chapter3/Section357.lean`.

Rationale (do not deviate without writing an issue):

1. Directly extends cycle 027's `symplecticityMatrix` infrastructure
   (the matrix `M = diag(b)A + A diag(b) − bbᵀ` is *literally* the
   same matrix in both definitions — `def:370A` asks `M = 0`,
   `def:357B` asks `b > 0` and `M` positive semidefinite).
2. Self-contained — entity JSON gives a clean matrix-level statement
   with no analytic dependencies. **Do NOT** be misled by the
   `def:357B → def:357A` LLM-claimed dependency edge: `def:357A` is a
   degenerately-extracted entity (its `statement_text` is just
   commentary, "Definition 357A was first introduced..."), and the
   actual mathematical relationship is *reverse*: algebraic stability
   is a *sufficient condition* for B/BN-stability (Burrage–Butcher).
   So `def:357B` does not logically depend on `def:357A` despite the
   JSON edge.
3. Concrete witness already exists: the implicit midpoint method has
   `M = 0` (cycle 027), so `M.PosSemidef` holds trivially via the
   zero-matrix PSD lemma. `b = (1)` is positive. So
   `implicitMidpoint_isAlgebraicallyStable` falls out in two lines.
4. Estimated cost: ≤ 1 cycle. Manageable in foreground without
   Aristotle.

### Textbook statement (quote verbatim in the file's docstring)

From `extraction/formalization_data/entities/def_357B.json`:

> A Runge–Kutta method `(A, b, c)` is 'algebraically stable' if
> `bᵢ > 0`, for `i = 1, 2, …, s`, and if the matrix `M`, given by
> `M = diag(b)A + A diag(b) − bbᵀ` (357d), is positive
> semi-definite.

### Required Lean shape

Place in a new file `OpenMath/Chapter3/Section357.lean`. Open
`OpenMath.Chapter3.Section370` so you can reuse `symplecticityMatrix`
**without** re-defining it.

```lean
import OpenMath.Chapter3.Section370
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OpenMath.Chapter3.Section357

open OpenMath.Chapter3.Section312
open OpenMath.Chapter3.Section370

/-- Butcher §357 Definition 357B — a Runge–Kutta method `(A, b, c)` is
*algebraically stable* iff every weight `bᵢ` is strictly positive and
the symplecticity matrix `M = diag(b)A + A diag(b) − bbᵀ` is positive
semidefinite. -/
def IsAlgebraicallyStable {s : ℕ} (R : RKTableau s) : Prop :=
  (∀ i, 0 < R.b i) ∧ (symplecticityMatrix R).PosSemidef
```

Note: `symplecticityMatrix` lives in `Section370`. **Reuse it** — do
not re-introduce a parallel definition. If unfolding is awkward,
factor out `symplecticityMatrix` into a fresh
`OpenMath/Chapter3/SymplecticityMatrix.lean` shared file *only if
necessary*. Default: keep it in `Section370` and import.

### Concrete witness

Add `implicitMidpoint_isAlgebraicallyStable` using cycle 027's
`implicitMidpoint`:

```lean
theorem implicitMidpoint_isAlgebraicallyStable :
    IsAlgebraicallyStable implicitMidpoint := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i; norm_num [implicitMidpoint]
  · -- symplecticityMatrix implicitMidpoint = 0, and 0 is PSD.
    rw [show symplecticityMatrix implicitMidpoint = 0 from
        implicitMidpoint_isSymplectic]
    exact Matrix.PosSemidef.zero
```

If `Matrix.PosSemidef.zero` is not the right Mathlib name, use
`lean_local_search "PosSemidef"` to find it. Likely candidates:
`Matrix.PosSemidef.zero`, `Matrix.posSemidef_zero`, or you may need
`(0 : Matrix _ _ ℝ).PosSemidef` constructed by hand from
`Matrix.PosSemidef.mk` with `IsHermitian.zero` and the trivial
quadratic-form bound. Use `lean_multi_attempt` to test the variants
before settling on one.

### Sub-goals to discharge

1. `symplecticityMatrix implicitMidpoint = 0` — already
   `implicitMidpoint_isSymplectic` (cycle 027). Just rewrite.
2. `(0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef` — should be a
   one-liner; if Mathlib lacks the named lemma, prove inline:
   ```lean
   refine ⟨Matrix.IsHermitian.zero, fun x => ?_⟩
   simp
   ```
3. `0 < (1 : ℝ)` for the `b i > 0` field — `norm_num` or `one_pos`.

## Execution plan (concrete, do these in order)

1. **Verify Mathlib has `Matrix.PosSemidef`** at the expected path.
   Run `lean_local_search "PosSemidef"` and
   `lean_loogle "Matrix.PosSemidef"`. The expected import is
   `Mathlib.LinearAlgebra.Matrix.PosDef`. If `PosSemidef` is in a
   different file in this Mathlib pin, adjust the import.
2. **Write the file with sorry-first scaffolding:**
   * `IsAlgebraicallyStable` definition.
   * `implicitMidpoint_isAlgebraicallyStable` with `sorry` for both
     conjuncts.
   * `lake env lean OpenMath/Chapter3/Section357.lean` to confirm it
     compiles.
3. **Close the positivity conjunct** with `fin_cases` + `norm_num`.
4. **Close the PSD conjunct** by rewriting via
   `implicitMidpoint_isSymplectic` to reduce to "0 is PSD". Try the
   named lemma path first; if missing, construct the witness inline.
5. **Add to `OpenMath/Chapter3.lean`** an `import
   OpenMath.Chapter3.Section357` line (alphabetically after
   `Section355` / `Section370` per existing convention).
6. **Update `extraction/formalization_data/lean_status.json`** for
   `def:357B`:
   * `lean_file`: `OpenMath/Chapter3/Section357.lean`
   * `lean_symbol`:
     `OpenMath.Chapter3.Section357.IsAlgebraicallyStable`
   * `formalization_status`: `formalized`
7. **Update `plan.md`**:
   * Flip the `def:357B` row from `[ ]` to `[x]` and append
     `` — `OpenMath/Chapter3/Section357.lean` ``.
   * Bump progress counter from `28 / 175` to `29 / 175`.
8. **Pre-commit faithfulness check** — run the CLAUDE.md checklist
   for `IsAlgebraicallyStable`. Expected conclusions:
   * Lean type matches textbook: positivity conjunction with the
     PSD condition on the explicit matrix `M`. ✓
   * No definition smuggling — `IsAlgebraicallyStable` is a
     `Prop` predicate, not a structure with derived fields. ✓
   * No tautology check needed (definition, not theorem). ✓
   * For `implicitMidpoint_isAlgebraicallyStable`: hypothesis-free,
     not vacuous (real PSD verification through cycle 027's
     `_isSymplectic` lemma), proof is not `exact h_…`. ✓
   * Document the LLM-claimed `def:357B → def:357A` edge as **not
     a real mathematical dependency** in the file's docstring (1–2
     line note: "Butcher's text presents 357B as a sufficient
     condition for the BN-stability concept introduced as 357A; the
     LLM-extracted dependency edge is reversed in the project's
     graph. Algebraic stability is a self-contained matrix
     condition.").
9. **Tautology scanner check**:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   should still return zero hits.
10. **Sorry count** must remain 0 across `OpenMath/`.
11. **Write `.prover-state/task_results/cycle_028.md`** per the
    CLAUDE.md template.
12. **Commit** with message:
    `Formalize def:357B — algebraically stable Runge–Kutta methods`.

## Aristotle policy for this cycle

**Do not submit to Aristotle.** Estimated end-to-end work is well
under 30 minutes; submitting a 30-minute Aristotle queue would
dominate the cycle. Reserve Aristotle for cycles whose proofs
genuinely look like multi-step open obligations.

## What NOT to do (explicit list)

* **Do NOT** formalize `def:357A` (B-stability) this cycle. Its
  extracted statement is degenerate ("Definition 357A was first
  introduced..."), and a faithful formalization requires reading the
  surrounding §357 prose for the actual contractivity / one-sided
  Lipschitz / dissipativity setup. That is a multi-cycle
  infrastructure investment. If the worker concludes after writing
  `def:357B` that `def:357A` blocks downstream §357 work, file an
  issue at
  `.prover-state/issues/b_stability_357A_extraction_gap.md`
  describing the gap and the textbook prose location, **but do not
  attempt to formalize 357A itself this cycle**.
* **Do NOT** re-define `symplecticityMatrix`. Reuse `Section370`'s
  `symplecticityMatrix` directly via
  `open OpenMath.Chapter3.Section370`.
* **Do NOT** introduce any `axiom` or `constant`.
* **Do NOT** raise `maxHeartbeats`.
* **Do NOT** edit `scripts/autonomous_loop.py` or any other infra
  file. Tautology-scanner false-positive concerns are tracked in
  `.prover-state/issues/tautology_scanner_false_positives.md` for the
  loop maintainer; the worker should not touch them.
* **Do NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/` (both are regenerated;
  see `extraction/CLAUDE.md`). The only `extraction/` file the worker
  may touch is `extraction/formalization_data/lean_status.json`.
* **Do NOT** start `thm:372A` (order conditions for symplectic
  methods) this cycle. It needs Φ-functional / order-condition
  infrastructure that hasn't been built and would not finish in one
  cycle.
* **Do NOT** revisit `def:357A` / `def:356A` / `def:356B` etc.
  They are non-blocking for `def:357B`.
* **Do NOT** rename `h_<word>` style hypotheses unless the scanner
  actually flags them. Cycle 027 already ships clean.
* **Do NOT** start a worktree, refactor `RKTableau`, or build new
  shared helper files unless `Matrix.PosSemidef` infrastructure
  truly forces it. The default plan keeps everything in
  `Section357.lean` + reuse of `Section370`.

## Tools to use

* `lean_local_search "PosSemidef"` — find the right Mathlib lemma
  names.
* `lean_loogle "Matrix.PosSemidef"` — pattern search for PSD lemmas.
* `lean_multi_attempt` at the `(0 : Matrix _ _ ℝ).PosSemidef` goal
  to test candidate closers in one call:
  `["exact Matrix.PosSemidef.zero", "exact Matrix.posSemidef_zero",
    "refine ⟨Matrix.IsHermitian.zero, fun x => ?_⟩; simp"]`.
* `lake env lean OpenMath/Chapter3/Section357.lean` for incremental
  verification.
* `lake build` only at the very end.

## Faithfulness reminder

The defining matrix `M` is **the same** as in cycle 027's
`symplecticityMatrix`. Reuse, do not parallel-define. The textbook
calls equation (357d) the same `M` it called (370a). The Lean code
should reflect that identity by sharing the term, not by recomputing
it. This both avoids drift and lets
`implicitMidpoint_isAlgebraicallyStable` discharge the PSD goal via
cycle 027's `implicitMidpoint_isSymplectic` rewrite.
