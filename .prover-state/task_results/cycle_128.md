# Cycle 128 Results

## Worked on
`def:525A` — G-symplectic general linear methods (Butcher §525, p. 429).
New file `OpenMath/Chapter5/Section525.lean` introducing the
predicate `GeneralLinearMethod.IsGSymplectic` together with a
non-vacuity witness `explicitEulerGLM_isGSymplectic`.

## Approach
Followed the strategy's six-step recipe verbatim:

1. Read `entities/def_525A.json` to confirm the three-equation
   textbook statement: `Vᵀ G V = G` (525a), `D U = Bᵀ G V` (525b),
   `D A + Aᵀ D = Bᵀ G B` (525c). The `transitive_dependencies`
   list cites §530 entries, but the literal statement does NOT
   reference any §530 concept — so this is a pure-matrix-algebra
   target on the existing `GeneralLinearMethod` infrastructure.
2. Re-read `OpenMath/Chapter5/Section510.lean` to confirm the
   shape conventions (`A : Matrix (Fin s) (Fin s) ℝ`,
   `U : Matrix (Fin s) (Fin r) ℝ`, `B : Matrix (Fin r) (Fin s) ℝ`,
   `V : Matrix (Fin r) (Fin r) ℝ`) and the `explicitEulerGLM`
   non-vacuity-witness pattern.
3. Searched Mathlib via `lean_loogle` for `Matrix.PosSemidef 0`
   and `Matrix.IsDiag`. Confirmed `Matrix.PosSemidef.zero` and
   `Matrix.isDiag_zero` both exist in Mathlib (modules
   `LinearAlgebra.Matrix.PosDef` and `LinearAlgebra.Matrix.IsDiag`).
4. Defined `IsGSymplectic` as an existential over `(G, D)`
   bundling `G.PosSemidef`, `D.IsDiag`, and the three matrix
   equations. PSD over `ℝ` already implies symmetry through the
   `IsHermitian` component of `Matrix.PosSemidef`, so no separate
   symmetry hypothesis is needed.
5. Witness: `explicitEulerGLM_isGSymplectic` instantiates
   `G = 0, D = 0`, so all three equations collapse to `0 = 0`
   and close by `simp`. No Aristotle submission was needed —
   the manual proof closed in one line per condition.
6. Pre-commit checks: faithfulness, tautology, identity,
   hypothesis-strength all green; ran `lake env lean
   OpenMath/Chapter5/Section525.lean` (clean), `lake build
   OpenMath.Chapter5.Section525` (built 2784 jobs successfully),
   and verified axioms via `#print axioms` (only the standard
   `propext`, `Classical.choice`, `Quot.sound`).

## Result
SUCCESS — `def:525A` is formalized and axiom-clean. New
deliverables:

* `def IsGSymplectic` capturing (525a)–(525c) verbatim.
* `theorem explicitEulerGLM_isGSymplectic` providing
  inhabitation, axioms = `{propext, Classical.choice, Quot.sound}`.
* `extraction/formalization_data/lean_status.json` row updated.
* `plan.md` row flipped to `[x]`; progress counter 65 → 66.

The Butcher (525d) explicit 2×2 example (with `√3` arithmetic)
is documented as future work in the `IsGSymplectic` and witness
docstrings.

## Faithfulness check

For `def IsGSymplectic`:

- Entity ID: `def:525A`. Textbook statement (quoted from
  `entities/def_525A.json` `statement_text`):
  > A general linear method (A, U, B, V) is G-symplectic if
  > there exists a positive semi-definite symmetric r × r matrix
  > G and an s × s diagonal matrix D such that
  > G = Vᵀ G V, (525a)
  > D U = Bᵀ G V, (525b)
  > D A + Aᵀ D = Bᵀ G B. (525c)
- Lean statement captures: **same content**.
  * `G : Matrix (Fin r) (Fin r) ℝ` with `G.PosSemidef` matches
    "positive semi-definite symmetric `r × r` matrix" exactly.
    Over `ℝ`, `Matrix.PosSemidef` bundles
    `IsHermitian ↔ symmetric` plus the non-negative
    quadratic-form condition.
  * `D : Matrix (Fin s) (Fin s) ℝ` with `D.IsDiag` matches
    "`s × s` diagonal matrix" exactly. `Matrix.IsDiag` is
    Mathlib's predicate `∀ i j, i ≠ j → M i j = 0`.
  * `M.V.transpose * G * M.V = G` matches (525a) exactly
    (Lean's left-to-right matrix product associates as
    `(Vᵀ * G) * V`, and matrix multiplication is associative,
    so this is the textbook's `Vᵀ G V`).
  * `D * M.U = M.B.transpose * G * M.V` matches (525b)
    exactly.
  * `D * M.A + M.A.transpose * D = M.B.transpose * G * M.B`
    matches (525c) exactly.
- Definition smuggling check: the Lean predicate IS the
  textbook definition. No characterization-via-derived-property
  is being smuggled in. ✓

For `theorem explicitEulerGLM_isGSymplectic`:

- The conclusion is `explicitEulerGLM.IsGSymplectic`. No
  hypothesis matches (the theorem is parameter-free). ✓
- Identity check: the proof is a `refine` plus three `simp`s,
  doing real algebraic work (showing the matrix equations
  with `G = D = 0` collapse to `0 = 0`). Not a vacuous
  re-export. ✓
- Hypothesis strength: no hypotheses. The witness
  `(G, D) = (0, 0)` is a degenerate but valid existential
  inhabitant; this is documented in the docstring with a
  pointer to Butcher's intended non-trivial (525d) example
  as future work.

## Dead ends
None. The strategy's "Backup plan" branches (alternate
`Matrix.PosSemidef.zero` / `Matrix.IsDiag` namings) were not
needed — both Mathlib symbols exist with the predicted names
(verified via `lean_loogle`).

## Discovery
* `Matrix.PosSemidef` over `ℝ` already implies symmetry
  through its `IsHermitian` component, so the textbook's
  "positive semi-definite **symmetric**" can be encoded with
  a single bundled predicate.
* `Matrix.PosSemidef.zero` and `Matrix.isDiag_zero` are both
  named in the canonical Mathlib idiom (zero satisfies the
  predicate, no instance needed).
* For trivial-witness theorems on `(s, r) = (1, 1)` GLMs with
  `G = D = 0`, plain `simp` discharges all three matrix
  equations — `decide` / `fin_cases` / explicit unfolding
  not needed.

## Suggested next approach
With `def:525A` formalized, natural next targets in §5
declarative-only-tier (no `sorry`s, no new datatypes):

1. **`def:541A` DIMSIM types** — pure shape constraints on the
   `(A, U, B, V)` matrices. Same pattern as `def:525A`
   (predicate on existing `GeneralLinearMethod`). The
   strategy's Plan B for cycle 128 already scopes this.
2. **`def:525A` non-trivial witness via Butcher (525d)** — the
   explicit 2×2 method with `√3` arithmetic. Defines
   `noncomputable def example525d : GeneralLinearMethod 2 2`
   and proves `example525d.IsGSymplectic` with
   `G = diag(1, 1 + 2√3/3), D = diag(1/2, 1/2)`. Real
   `√3`-arithmetic check; ~30–60 LOC, single cycle.
3. **§530 starting-method infrastructure** — necessary
   prerequisite before attempting `def:530A`/`def:530B`/
   `def:530C`/`thm:534A`. Single-cycle datatype design
   (sequence of generalized-RK methods).

The planner should pick from this menu. Option 2 (Butcher
(525d) substantive witness) is the most compelling
follow-up because it strengthens the non-vacuity guarantee
for the predicate just introduced — currently every GLM
trivially inhabits `IsGSymplectic`, which is technically
faithful but loses the textbook's substantive content.
