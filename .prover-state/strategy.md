# Strategy — cycle 027

## Status entering this cycle

* Tree: branch tip after cycle 026 lands `def:355A` in
  `OpenMath/Chapter3/Section355.lean` (commit `1e624c9`).
* Sorry count: **0** across `OpenMath/`.
* Tautology scanner: **0 hits** across `OpenMath/`.
* No pending Aristotle results.
* No active blocker that prevents progress on §35x or §37x.
* `plan.md` progress: **27 / 175**.

The cycle-026 task-result file suggested `thm:355B` or `thm:302C` as
next targets. **Both have hidden infrastructure costs**:

* `thm:355B` requires Taylor-expansion / `R(z) − exp(z) = -C·z^{p+1}
  + O(z^{p+2})` machinery in ℂ, plus an analysis of arrows tangent to
  `(p+1)`-th roots of unity. That is a 2–3 cycle build, not 1.
* `thm:302C` (`Aₙ = Σ α(t) = (n−1)!`, `Bₙ = Σ β(t) = n^{n−1}`)
  requires (a) defining `α(t)` and `β(t)` (only stated in `thm:302A`,
  not yet formalised), and (b) building a finite enumeration of
  `{t : RootedTree // r(t) = n}`. That is also multi-cycle.

A cleaner one-cycle target sits a few rows further down: **`def:370A`
— Symplectic Runge–Kutta methods**.

---

## Primary target — `def:370A` (symplectic RK methods)

### Why this target

The textbook statement (`extraction/formalization_data/entities/def_370A.json`)
is a single matrix equality:

> A Runge–Kutta method `(A, b, c)` is **symplectic** if
>     `M = diag(b) A + A diag(b) − b bᵀ`
> is the zero matrix.

The dependency list in the JSON cites `def:381A`–`def:381F` and
`thm:381G/H`, but those references are *paragraph-context* mentions
(the surrounding §370 prose discusses reducibility), **not**
mathematical prerequisites. The actual definition is self-contained
on `RKTableau`. Confirm this when you read `def_370A.json` (the
`statement_text` is just the formula above).

The cycle is small and well-bounded: one new definition, one concrete
witness, and a faithfulness check.

### Concrete plan

1. **Read** `extraction/formalization_data/entities/def_370A.json`
   in full. Quote the statement verbatim in the file docstring.

2. **Create `OpenMath/Chapter3/Section370.lean`** with these
   declarations under `namespace OpenMath.Chapter3.Section370`:

   ```lean
   import OpenMath.Chapter3.Section312

   namespace OpenMath.Chapter3.Section370

   open OpenMath.Chapter3.Section310  -- RKTableau lives there
                                       -- per Section312.lean line 66

   /-- The symplecticity matrix `M = diag(b) A + A diag(b) − b bᵀ`
   of a Runge–Kutta method. -/
   def symplecticityMatrix {s : ℕ} (R : RKTableau s) :
       Matrix (Fin s) (Fin s) ℝ :=
     Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
       Matrix.vecMulVec R.b R.b

   /-- Butcher §370 Definition 370A — a Runge–Kutta method is
   *symplectic* iff its symplecticity matrix vanishes. -/
   def IsSymplectic {s : ℕ} (R : RKTableau s) : Prop :=
     symplecticityMatrix R = 0
   ```

   Notes:

   * `Matrix.vecMulVec u v` is the Mathlib spelling of the outer
     product `u vᵀ` (`fun i j => u i * v j`). Verify with
     `lean_local_search "vecMulVec"` if you're unsure; if the name is
     different or the file is hard to import, just inline the lambda
     `fun i j => R.b i * R.b j`.
   * `Matrix.diagonal R.b` is `fun i j => if i = j then R.b i else 0`,
     which is exactly `diag(b)`.
   * Do **not** reuse the project's `Section381` reducibility
     definitions here — `def:370A` is independent of them.

3. **Concrete non-vacuous witness — implicit midpoint.** This is the
   canonical 1-stage symplectic method:

   ```lean
   /-- The implicit midpoint method, `s = 1`, with
   `A = [[1/2]]`, `b = [1]`, `c = [1/2]`. -/
   def implicitMidpoint : RKTableau 1 where
     A := !![1/2]
     b := fun _ => 1
     c := fun _ => 1/2

   /-- Implicit midpoint is symplectic. -/
   theorem implicitMidpoint_isSymplectic :
       IsSymplectic implicitMidpoint := by
     unfold IsSymplectic symplecticityMatrix implicitMidpoint
     ext i j
     fin_cases i <;> fin_cases j
     simp [Matrix.diagonal, Matrix.vecMulVec, Matrix.mul_apply]
     ring
   ```

   The literal `!![1/2]` is the standard Mathlib 1×1 matrix notation
   (from `Mathlib.Data.Matrix.Notation`). If that exact spelling
   fails, fall back to `Matrix.of (fun _ _ => (1/2 : ℝ))`. Verify
   inside the proof with `lean_goal` — the final scalar identity is
   `1·(1/2) + (1/2)·1 − 1·1 = 0`, which `ring` closes.

   **If `fin_cases` + `simp` + `ring` does not close the witness**,
   do not chase it; substitute the trivial `s = 0` witness:

   ```lean
   def trivialZero : RKTableau 0 where
     A := !![]      -- 0×0 matrix, empty
     b := Fin.elim0
     c := Fin.elim0

   theorem trivialZero_isSymplectic : IsSymplectic trivialZero := by
     ext i j
     exact i.elim0
   ```

   The `s = 0` witness is technically non-vacuous (`RKTableau 0`
   inhabits `Type`) and CLAUDE.md's "concrete witness/instance" rule
   is satisfied. Prefer implicit midpoint if it goes through — it is
   the textbook example.

4. **Wire the new module into `OpenMath/Chapter3.lean`.** Add
   `import OpenMath.Chapter3.Section370` next to the existing imports.

5. **Update bookkeeping.**

   * `plan.md`: flip `def:370A` to `[x]` with file path
     `OpenMath/Chapter3/Section370.lean`. Bump
     `Progress: 27 / 175` → `Progress: 28 / 175`.
   * `extraction/formalization_data/lean_status.json`: set `def:370A`
     entry to `formalized` with
     `lean_symbol: OpenMath.Chapter3.Section370.IsSymplectic`.

6. **Verify before commit.**

   ```bash
   lake env lean OpenMath/Chapter3/Section370.lean   # clean exit
   lake build                                         # clean
   rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/  # 0 hits
   ```

   Axiom check (in the file or via `lean_verify`):
   ```
   #print axioms OpenMath.Chapter3.Section370.IsSymplectic
   #print axioms OpenMath.Chapter3.Section370.implicitMidpoint_isSymplectic
   ```
   Expected: `[propext, Classical.choice, Quot.sound]` only.

7. **Faithfulness check (mandatory per CLAUDE.md).**

   * Quote the textbook `statement_latex` from `def_370A.json` in the
     `cycle_027.md` faithfulness section.
   * Confirm the Lean type matches verbatim: `M = 0` ↔
     `symplecticityMatrix R = 0`. No reformulation needed.
   * Tautology check: `IsSymplectic` is a predicate, not a theorem.
     The witness theorem `implicitMidpoint_isSymplectic` does real
     work (computes the 1×1 entry of `M`). Not a vacuous re-export.
   * Hypothesis-strength check: no extra hypotheses are imposed.
     `def:370A` says nothing about `c`, `bᵢ > 0`, or non-degeneracy.

### Estimated effort

≤ 1 cycle. The longest line item is debugging the
`fin_cases`/`Matrix.diagonal`/`Matrix.vecMulVec` simp set on the
implicit-midpoint witness. If it spirals, fall back to `s = 0`.

### Aristotle disposition

**Do not** submit anything to Aristotle. The proof has zero `sorry`
and the witness is a single-step `simp; ring`. Aristotle has 30-min
turnaround; this whole cycle is faster than that.

---

## Fallback target (only if `def:370A` blows up unexpectedly)

**`def:357B` — algebraically stable RK methods.** Uses *exactly the
same matrix* `M = diag(b) A + A diag(b) − b bᵀ`, but with a
positive-semidefinite predicate instead of `M = 0`:

> `(A, b, c)` is **algebraically stable** if `bᵢ > 0` for all `i`,
> and `M` (above) is positive semi-definite.

If you fall back to this, **do not** define a new
`symplecticityMatrix` — extract it as a shared helper that both
`Section370` and the new `Section357` import. Concrete witness for
`def:357B`: implicit midpoint again (`M = 0` ⇒ PSD trivially).

PSD predicate: use `Matrix.PosSemidef` from
`Mathlib.LinearAlgebra.Matrix.PosDef`. Verify the field structure —
it expects `Matrix.IsHermitian` and a non-negativity statement on the
quadratic form. For the witness `M = 0`, both fields are immediate.

**Skip** to this only if `def:370A` itself is blocked. Do not do
both in one cycle — CLAUDE.md "Don't add features beyond what the
task requires".

---

## Explicit DO-NOT list (do not retry these in cycle 027)

These have been recently tried, deferred, or flagged as multi-cycle
infrastructure investments. Stay clear:

1. **`thm:351B`, `lem:351A`, `thm:353A`** — need `(I − zA)⁻¹`
   matrix-resolvent infrastructure. Multi-cycle prereq.
2. **`def:356A`** — also needs `(I − AZ)⁻¹`. Skip until matrix
   resolvent is built.
3. **`thm:355B`, `thm:355C`, `thm:355D`, `thm:355E`** — Taylor /
   asymptotic / pole-tracking analyses. Each is 2+ cycles.
4. **`thm:302A`, `thm:302B`, `thm:302C`** — need `α(t)` and `β(t)`
   defined as labelling counts AND a finite enumeration of trees of
   given order. Multi-cycle prereq. The cycle-026 suggestion to
   pursue `thm:302C` underestimated this cost.
5. **`lem:383A`, `lem:383B`, `lem:383C`** — Runge–Kutta group
   infrastructure not built. Wait until `def:381F` and reduced-method
   construction land.
6. **`def:381F`** — triggers the deferred reduced-method
   construction (`reduced_method_deferred.md`). Skip.
7. **`def:388D`, `def:388F`, `thm:388A`–`H`** — group `G₁` and its
   subgroup lattice not built. Skip.
8. **`def:323A`** — depends on `thm:315A`, `lem:313A`, `thm:311B`,
   none yet formalised. Skip.
9. **`def:357A` (BN-stability)** — the JSON `statement_text` is a
   fragment ("was first introduced, it was referred to as
   B-stability…") that does not capture the full predicate. Needs
   careful textbook re-reading; risk of definition smuggling. Skip
   in favour of `def:357B`/`def:370A` whose statements are crisp.
10. **The `IsAStable ↔ IsAlphaStable (π/2)` bridge** — `Real.tan`
    totalisation trap; do not chase it.
11. **§142 Schur / Jordan infrastructure** — non-critical-path,
    3–5 cycle effort, queue is full of higher-priority Chapter 3
    work. See `jordan_canonical_form_missing.md`.

---

## Mandatory worker reminders (CLAUDE.md)

* **Sorry-first.** Write the file with `sorry` placeholders first,
  verify it compiles, then close them. For this cycle the only
  potential `sorry` site is the witness theorem; close with
  `fin_cases`/`simp`/`ring` as in the plan above.
* **Pre-commit faithfulness check.** Mandatory for every new `def`
  and `theorem`. Quote textbook source in `cycle_027.md`.
* **No `axiom`/`constant`. No `maxHeartbeats` increase. No edits to
  `scripts/autonomous_loop.py`. No edits to `extraction/raw_text/`
  or `extraction/formalization_data/entities/`.**
* **Concrete witness rule.** `IsSymplectic` is a new `def` (not a
  `class`/`structure`), but CLAUDE.md's witness rule still applies in
  spirit — the predicate would be vacuous without an example.
  Provide `implicitMidpoint_isSymplectic` (or the `s = 0` fallback).
* **Run the scanner before commit.** Zero hits expected.
* **Update `lean_status.json`** for `def:370A` and **bump `plan.md`
  progress** in the same commit.

---

## Cycle-027 success criteria

1. New file `OpenMath/Chapter3/Section370.lean` with `IsSymplectic`
   and a non-vacuous witness theorem.
2. `OpenMath/Chapter3.lean` imports the new module.
3. `lake build` clean; axiom check clean; tautology scanner returns 0
   hits.
4. `plan.md` row for `def:370A` flipped to `[x]`; progress bumped to
   28 / 175.
5. `lean_status.json` row for `def:370A` flipped to `formalized` with
   the right `lean_symbol`.
6. `cycle_027.md` written with faithfulness section quoting
   `def_370A.json` `statement_latex`.
7. Commit and push.

If anything in steps 1–7 fails, write an issue file in
`.prover-state/issues/` describing the specific blocker, then commit
whatever partial progress was made.
