# Strategy — cycle 128

## Context recap

Cycle 127 closed `lem:515C` as a thin public wrapper over the existing
helper, completing **§515 at 100%** (4/4: 515A/B/C/D all axiom-clean).
There is **no pending Aristotle work**, **no open `sorry`s** in the
tree, and **no in-progress theorem**. We need to pick a fresh target.

## Target — `def:525A` (G-symplectic methods)

**Primary deliverable**: formalize `def:525A` "G-symplectic methods"
(Butcher §525, p. 429) in a new file `OpenMath/Chapter5/Section525.lean`,
plus a non-vacuity witness.

### Why this target (not `def:530A`, not `thm:535A`, not `thm:550A`)

* `def:530A` (non-degenerate starting method) requires a *new datatype*
  for "starting method = sequence of generalized Runge–Kutta methods"
  including the equation-(530a) RK structure. That's an
  infrastructure cycle, not a definition cycle. Defer.
* `thm:535A` (underlying one-step method GLM) consumes §530 order
  theory which doesn't exist yet. Defer.
* `thm:550A` (doubly companion matrices) needs a new datatype. Defer.
* `def:551A` (Inherent RK stability) transitively depends on `def:542A`,
  `thm:550A`, `cor:550C` — all unformalized. Defer.
* `def:525A` is **pure matrix algebra on the existing
  `GeneralLinearMethod` structure** (Section510.lean:63). Three
  equations on `(A, U, B, V)` plus existence of auxiliary matrices
  `G` (PSD symmetric) and `D` (diagonal). The transitive-deps list
  in `entities/def_525A.json` cites §530 entries — but those are
  LLM-identified false dependencies (the literal definition does
  NOT reference any §530 concept). Verify by re-reading the
  `statement_text` field before proceeding.

### Textbook content (verbatim from `entities/def_525A.json`)

> A general linear method `(A, U, B, V)` is G-symplectic if there
> exists a positive semi-definite symmetric `r × r` matrix `G` and an
> `s × s` diagonal matrix `D` such that
>   `Vᵀ G V = G`     (525a)
>   `D U = Bᵀ G V`   (525b)
>   `D A + Aᵀ D = Bᵀ G B`   (525c)

### Step 1 — read inputs (MANDATORY before coding)

1. Open `extraction/formalization_data/entities/def_525A.json`.
   Confirm:
   * `kind = "definition"`,
   * the three equations as quoted above,
   * **the literal statement does not mention "starting method",
     "order", or any §530 concept**. (The `transitive_dependencies`
     list is misleading here; the LLM heuristically attached §530
     entries that the definition itself does not invoke.)
2. Open `OpenMath/Chapter5/Section510.lean` lines 63–148. Confirm
   `GeneralLinearMethod s r` has fields `A : Matrix (Fin s) (Fin s) ℝ`,
   `U : Matrix (Fin s) (Fin r) ℝ`, `B : Matrix (Fin r) (Fin s) ℝ`,
   `V : Matrix (Fin r) (Fin r) ℝ`. Confirm `explicitEulerGLM`
   (line 144) exists with `A = !![0], U = !![1], B = !![1], V = !![1]`.

### Step 2 — search Mathlib before defining

Per CLAUDE.md "Before creating any new definition, use Lean LSP search
tools to check whether an equivalent Mathlib definition already exists":

* `lean_local_search "Symplectic"` — confirm there is no Mathlib
  predicate matching G-symplectic GLMs. (Mathlib has
  `SymplecticGroup` and `Matrix.IsSymplectic`, but those are about
  preserving an antisymmetric bilinear form on `K^{2n}`, NOT this
  notion.)
* `lean_local_search "PosSemidef"` — confirm
  `Matrix.PosSemidef` exists (it does, in
  `Mathlib.LinearAlgebra.Matrix.PosDef`) and use it for the `G` PSD
  + symmetric condition. (Mathlib's `PosSemidef` already bundles
  `IsHermitian` over ℝ ⇒ symmetric.)
* `lean_local_search "Matrix.IsDiag"` — `Matrix.IsDiag` is the
  Mathlib predicate for diagonal matrices; use it.

### Step 3 — write the predicate

In a new file `OpenMath/Chapter5/Section525.lean`:

```lean
import OpenMath.Chapter5.Section510

namespace OpenMath.Chapter5.Section510

namespace GeneralLinearMethod

variable {s r : ℕ}

/-- Butcher §525 def:525A — A general linear method `(A, U, B, V)` is
**G-symplectic** if there exist a PSD symmetric `r × r` matrix `G` and
a diagonal `s × s` matrix `D` satisfying

* (525a) `Vᵀ G V = G`,
* (525b) `D U = Bᵀ G V`,
* (525c) `D A + Aᵀ D = Bᵀ G B`. -/
def IsGSymplectic (M : GeneralLinearMethod s r) : Prop :=
  ∃ (G : Matrix (Fin r) (Fin r) ℝ) (D : Matrix (Fin s) (Fin s) ℝ),
    G.PosSemidef ∧ D.IsDiag ∧
    M.V.transpose * G * M.V = G ∧
    D * M.U = M.B.transpose * G * M.V ∧
    D * M.A + M.A.transpose * D = M.B.transpose * G * M.B
```

Verify shapes:
* `B : Matrix (Fin r) (Fin s) ℝ` ⇒ `Bᵀ : Matrix (Fin s) (Fin r) ℝ`.
* `Bᵀ * G : Matrix (Fin s) (Fin r) ℝ`,
  `Bᵀ * G * V : Matrix (Fin s) (Fin r) ℝ`.
* `D * U : Matrix (Fin s) (Fin r) ℝ`. Shapes match for (525b). ✓
* `D * A + Aᵀ * D : Matrix (Fin s) (Fin s) ℝ`;
  `Bᵀ * G * B : Matrix (Fin s) (Fin s) ℝ`. ✓
* `Vᵀ * G * V, G : Matrix (Fin r) (Fin r) ℝ`. ✓

### Step 4 — non-vacuity witness (MANDATORY per CLAUDE.md)

Add to the same file:

```lean
/-- Non-vacuity witness for `IsGSymplectic`: `explicitEulerGLM` is
trivially G-symplectic with `G = 0, D = 0`. (This is a vacuous-style
witness — Butcher's intended non-trivial example is the 2×2 method
of equation (525d), which is deferred to a future cycle because of
its `√3` arithmetic.) -/
theorem explicitEulerGLM_isGSymplectic :
    explicitEulerGLM.IsGSymplectic := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 is PosSemidef
    exact Matrix.PosSemidef.zero
  · -- 0 is diagonal
    intro i j _
    rfl  -- 0 i j = 0 by defn of zero matrix
  · -- Vᵀ * 0 * V = 0
    simp
  · -- D * U = Bᵀ * 0 * V
    simp
  · -- 0 * A + Aᵀ * 0 = Bᵀ * 0 * B
    simp
```

If `Matrix.PosSemidef.zero` doesn't exist with that exact name:
* `lean_local_search "PosSemidef" + "zero"`,
* `lean_loogle "Matrix.PosSemidef 0"`,
* fallback: prove inline via `⟨isHermitian_zero, by intro x; simp⟩`
  (since `PosSemidef M = IsHermitian M ∧ ∀ x, 0 ≤ x ⬝ M *ᵥ x`).

If `Matrix.IsDiag` is defined as `∀ i j, i ≠ j → M i j = 0`, then
`intro i j _; rfl` works because `(0 : Matrix _ _ ℝ) i j = 0`. If
the shape differs, search with `lean_hover_info` on `Matrix.IsDiag`
and adjust.

### Step 5 — Aristotle batch (recommended, parallel; only ONE job)

The witness should close manually in <30 minutes. **However**, since
this cycle is short and Aristotle is free compute, submit ONE job
once the file compiles with the witness as `sorry`. This gives a
backup if the `Matrix.PosSemidef.zero` / `Matrix.IsDiag` naming
proves fiddly.

* Job 1: prove `explicitEulerGLM_isGSymplectic`. Standalone — feed
  the file content (no extra context needed) since it imports only
  `OpenMath.Chapter5.Section510`.

DO NOT submit the predicate definition itself — Aristotle proves
theorems, not declarations. Sleep ≥30 min before checking, per
CLAUDE.md. Do NOT poll twice. If Aristotle returns a cleaner proof
than the manual `simp` chain, use it; otherwise keep the manual
proof.

### Step 6 — pre-commit faithfulness checklist (CLAUDE.md §"Pre-Commit")

For the new `def IsGSymplectic`:

* [ ] Quote the textbook statement (from
      `entities/def_525A.json`'s `statement_text`) in the docstring.
* [ ] Confirm the three matrix equations match the textbook
      letter-for-letter: `Vᵀ G V = G`, `D U = Bᵀ G V`,
      `D A + Aᵀ D = Bᵀ G B`. NO transposed indices, NO swapped
      `B/V`, NO sign errors.
* [ ] **Definition smuggling check**: the predicate quantifies
      existentially over `G` and `D`; we are NOT defining
      G-symplectic via a *characterization* (e.g. via the stability
      function being unitary) and then claiming the textbook
      definition follows. The Lean predicate IS the textbook
      definition.
* [ ] PSD condition: `G.PosSemidef` in Mathlib bundles
      `IsHermitian` (which over ℝ means symmetric) plus the
      non-negative quadratic-form condition. This matches Butcher's
      "positive semi-definite symmetric" exactly.

For `explicitEulerGLM_isGSymplectic`:

* [ ] **Tautology check**: the conclusion `IsGSymplectic` is the
      goal; no hypothesis matches the conclusion. ✓
* [ ] **Non-vacuity disclaimer**: the witness `(G, D) = (0, 0)` is
      a degenerate (trivial) witness — every GLM trivially
      satisfies the predicate with `G = 0, D = 0`. The witness
      *establishes inhabitability* of the predicate but does NOT
      exhibit a substantively G-symplectic method. This is
      acceptable for non-vacuity per CLAUDE.md, but document the
      caveat in the witness docstring and propose Butcher's eq
      (525d) explicit 2×2 method as future work (Step 8 stretch
      goal).

### Step 7 — bookkeeping

* Update `extraction/formalization_data/lean_status.json`: set
  `def:525A` to `formalized`, `lean_file =
  "OpenMath/Chapter5/Section525.lean"`, `lean_symbol =
  "OpenMath.Chapter5.Section510.GeneralLinearMethod.IsGSymplectic"`,
  bump cycle reference to 128.
* Update `plan.md`: change `def:525A` row from `[ ]` to `[x]`
  with cycle-128 commentary.
* Verify single-file build: `lake env lean
  OpenMath/Chapter5/Section525.lean` exits 0.
* Verify axiom-cleanness: `lake build
  OpenMath.Chapter5.Section525` (so the `.olean` is fresh — per
  cycle 072's note, `lake env lean` does NOT update the cache),
  then `#print axioms
  OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitEulerGLM_isGSymplectic`
  must return `[propext, Classical.choice, Quot.sound]` ONLY.
* Tautology scanner: run
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
  and confirm no NEW hits in `Section525.lean`. (The pre-existing
  `Section514.lean:601 — exact h_norm_obligation` carry-over is
  expected and not a regression.)

### Step 8 — commit

Commit message format (matches recent §515 cycles):

```
Cycle 128 — formalize def:525A G-symplectic methods (axiom-clean)
```

Files touched:
* `OpenMath/Chapter5/Section525.lean` (new, ~50 LOC).
* `extraction/formalization_data/lean_status.json` (one row).
* `plan.md` (one row, plus bumping the progress counter from 65 to
  66 entities done).

## What NOT to do this cycle

* **Do NOT target `def:530A`** "non-degenerate starting method" — it
  requires a new datatype for "starting method as sequence of
  generalized RK methods" plus the eq-(530a) generalized-RK
  structure, which is an infrastructure cycle, not a definition
  cycle. The `entities/def_530A.json` `dependencies = []` is
  misleading — the *content* depends on the §530a generalized RK
  framework, which we don't have.
* **Do NOT target `thm:535A`** — it transitively depends on §530
  order theory (`def:530B`, `def:530C`), which we don't have.
* **Do NOT target `thm:550A`** — it requires a new "doubly
  companion matrix" datatype and is best deferred until after
  §525/§530 lay the type-theoretic groundwork.
* **Do NOT introduce a new structure** for the textbook's eq (525d)
  explicit 2×2 witness this cycle. The `√3`-arithmetic check is
  doable but eats the cycle's budget. Use the `(G, D) = (0, 0)`
  trivial witness for non-vacuity and document the (525d) witness
  as future work.
* **Do NOT raise `maxHeartbeats`** above 200000 (CLAUDE.md hard
  rule). The witness proof is `simp`-tier and should close
  trivially; if it doesn't, decompose rather than bumping
  heartbeats.
* **Do NOT submit the `IsGSymplectic` predicate definition to
  Aristotle** — Aristotle proves theorems, not types. Only the
  witness proof goes to Aristotle.
* **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer
  territory per `tautology_scanner_false_positives.md`.
* **Do NOT modify any §515 file** (Section515.lean is closed at
  axiom-clean and any edit risks regression). The only file
  modifications this cycle are the new `Section525.lean`,
  `lean_status.json`, and `plan.md`.
* **Do NOT use Mathlib's `SymplecticGroup` or
  `Matrix.IsSymplectic`** — those are about preserving an
  antisymmetric bilinear form on `K^{2n}` and are NOT the
  textbook's G-symplectic concept. Verify the Mathlib
  `IsSymplectic` definition before considering reuse; the names
  collide but the concepts do not.
* **Do NOT** follow the cycle 127 worker's "trim §520
  unused-`simp` warnings" suggestion — it is hygiene-only and
  should not absorb cycle time when there's a substantive
  deliverable available.
* **Do NOT** worker-edit `scripts/autonomous_loop.py` even if the
  scanner false-positive issue is mentioned (the standing
  workaround — drop the underscore in any new `h_<name>` binders
  in `Section525.lean` — applies if any new closer triggers it,
  but the `simp`-tier witness shouldn't introduce any).

## Backup plan — if the witness `simp` chain fails

If `simp` cannot discharge the matrix equations on `explicitEulerGLM`
with `G = 0, D = 0`:

1. Try `decide` (since matrices are concrete `Fin 1 × Fin 1`).
2. Try entrywise `ext; fin_cases; simp [explicitEulerGLM]` —
   pattern from `explicitEulerGLM_isPreconsistent` (Section510.lean:152).
3. Try `Matrix.mul_zero, Matrix.zero_mul, add_zero` simp lemmas
   explicitly in the `simp only`.
4. If still stuck, the issue is naming — `Matrix.PosSemidef.zero`
   may be absent. Inline:
   ```lean
   refine ⟨isHermitian_zero, ?_⟩
   intro x
   simp [Matrix.zero_mulVec, dotProduct_zero]
   ```
5. For `Matrix.IsDiag` of `0`: search `lean_local_search "IsDiag"`
   and unfold; the definition is `∀ i j, i ≠ j → M i j = 0` and
   `(0 : Matrix _ _ ℝ) i j = 0` by definition.

If the witness genuinely cannot close in one cycle (extremely
unlikely given the matrices are zero), file
`.prover-state/issues/def_525A_witness_blocker.md` with the
specific Mathlib API gap and pivot the cycle to **Plan B**.

## Plan B — if `def:525A` proves intractable: `def:541A` (DIMSIM types)

Read `entities/def_541A.json`. DIMSIM (Diagonally Implicit Multistage
Integration Methods) types are pure shape constraints on the GLM
matrices: `A` lower triangular with constant diagonal, plus stage-
order conditions. This is similar in flavour to `def:525A` (matrix
predicates on existing GLM infrastructure). Apply the same six-step
recipe.

## Cycle deliverable bar

* **Minimum** (per CLAUDE.md "A cycle with zero changes is
  unacceptable"): the predicate definition with the textbook
  docstring committed, even if the witness is left as `sorry` with
  a blocker issue.
* **Target**: predicate + axiom-clean witness + status updates +
  commit. Should land in ~1 hour of worker time.
* **Stretch goal**: additionally state (without proving) the
  textbook's (525d) explicit 2×2 example as

  ```lean
  /-- Butcher §525 eq (525d) — the explicit 2×2 G-symplectic
  example presented in Butcher (2006). The proof of
  `IsGSymplectic` is deferred to a future cycle (the witness
  matrices `G = diag(1, 1 + 2√3/3), D = diag(1/2, 1/2)` involve
  `√3` arithmetic that does not fit this cycle). -/
  noncomputable def example525d : GeneralLinearMethod 2 2 where
    A := !![ (3 + Real.sqrt 3) / 6, 0;
             -Real.sqrt 3, (3 + Real.sqrt 3) / 6 ]
    U := !![ 1, -(3 + 2 * Real.sqrt 3) / 3;
             1, (3 + 2 * Real.sqrt 3) / 3 ]
    B := !![ 1/2, 1/2;
             1/2, -1/2 ]
    V := !![ 1, 0;
             0, -1 ]
  ```

  Do NOT prove `example525d.IsGSymplectic` this cycle — just
  record the definition with a docstring noting it as future
  work. This sets up a faithful witness for a follow-up cycle.
  Skip the stretch goal entirely if it pushes the cycle past
  the 1-hour mark; the target deliverable is what counts.
