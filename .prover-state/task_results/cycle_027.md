# Cycle 027 Results

## Worked on
`def:370A` — symplectic Runge–Kutta methods. New file
`OpenMath/Chapter3/Section370.lean` introducing:

* `symplecticityMatrix : RKTableau s → Matrix (Fin s) (Fin s) ℝ`
* `IsSymplectic : RKTableau s → Prop`
* `implicitMidpoint : RKTableau 1` (concrete witness)
* `implicitMidpoint_isSymplectic : IsSymplectic implicitMidpoint`

## Approach
1. Read `extraction/formalization_data/entities/def_370A.json` to
   confirm the textbook statement is the single matrix equality
   `M = diag(b)A + A diag(b) − bbᵀ = 0`.
2. Verified `Matrix.vecMulVec` lives in `Mathlib.Data.Matrix.Mul` via
   loogle (`Matrix.vecMulVec_apply : (Matrix.vecMulVec w v) i j = w i * v j`).
3. Wrote `symplecticityMatrix` as the literal Mathlib expression
   `Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
    Matrix.vecMulVec R.b R.b` and `IsSymplectic R := symplecticityMatrix R = 0`.
4. Built the `s = 1` implicit midpoint witness with `Matrix.of` (the
   `!![1/2]` notation requires `Mathlib.Data.Matrix.Notation`, which is
   not in this project's built oleans — fell back to `Matrix.of` per
   the strategy's guidance).
5. Closed the witness with `unfold; ext; fin_cases i; fin_cases j;
   simp [Matrix.diagonal, Matrix.vecMulVec, Matrix.mul_apply]; ring`.
6. Marked `implicitMidpoint` `noncomputable` because `RKTableau`'s
   `1/2 : ℝ` is noncomputable (`Real.instDivInvMonoid`).
7. Added `import OpenMath.Chapter3.Section370` to
   `OpenMath/Chapter3.lean`. Bumped `plan.md` progress 27 → 28 and
   flipped the `def:370A` row to `[x]`. Updated `lean_status.json`
   `def:370A` to `formalized` with symbol
   `OpenMath.Chapter3.Section370.IsSymplectic`.
8. `lake build`: clean (2832 jobs). Tautology scanner
   (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`): 0 hits across
   `OpenMath/`. Sorry count: 0.

## Result
SUCCESS — `def:370A` formalized end-to-end in a single cycle. No
Aristotle submission needed; the only proof obligation was the 1×1
witness identity `1·(1/2) + (1/2)·1 − 1·1 = 0`, closed locally.

## Faithfulness check
For each new `def`/`theorem` introduced this cycle:

### `symplecticityMatrix`

* Entity `def:370A`. Quoted `statement_latex`:
  > A Runge--Kutta method $(A, b, c)$ is symplectic if
  > \[ M = \operatorname{diag}(b)A + A \operatorname{diag}(b) - bb^{\top} \]
  > is the zero matrix.
* Lean expression (literal):
  `Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
   Matrix.vecMulVec R.b R.b`.
* Lean statement captures: **same content**. `Matrix.vecMulVec b b` is
  the outer product `b bᵀ` by definition
  (`(Matrix.vecMulVec b b) i j = b i * b j` — this is exactly Butcher's
  `bᵢ bⱼ` from equation (370a)). `Matrix.diagonal b` is the diagonal
  matrix with `b` on the diagonal — exactly `diag(b)`. Multiplication
  of matrices and matrix subtraction are the standard Mathlib
  operations. No reformulation, no extra hypotheses.

### `IsSymplectic`

* Entity `def:370A` (same).
* Lean: `IsSymplectic R := symplecticityMatrix R = 0`.
* Lean statement captures: **same content**. The textbook says "M is
  the zero matrix"; the Lean version says `M = 0`. These are
  syntactically equal up to Mathlib's `Zero (Matrix _ _ ℝ)` instance,
  which is the entry-wise zero matrix.
* Tautology check: not applicable — `IsSymplectic` is a `def`, not a
  theorem. No hypotheses.

### `implicitMidpoint`

* Auxiliary witness, not a textbook entity. The implicit midpoint
  method `(A = [[1/2]], b = [1], c = [1/2])` is a textbook example
  (Butcher §340 ff., common throughout Chapter 3).
* No faithfulness issue — it is a single concrete tableau.

### `implicitMidpoint_isSymplectic`

* Theorem stating the witness satisfies the predicate.
* Tautology check: conclusion is `symplecticityMatrix implicitMidpoint
  = 0`, no hypotheses → cannot tautologise.
* Identity check: proof is not `exact h_…` / `id` — it does real
  computation (`fin_cases`, `simp` unfolding the matrix expression,
  `ring` closing `2⁻¹ + 2⁻¹ - 1 = 0`).
* Hypothesis-strength check: no hypotheses. The entire claim is
  decidable `1×1` arithmetic.

### Definition-smuggling check
`IsSymplectic` is not a `class`/`structure`. It is a `def := <equality>`
predicate; there is no field that is supposed to be a consequence.

### Hypothesis-strength check
`def:370A` imposes nothing on `c`, no positivity on `bᵢ`, no invertibility
or non-degeneracy. The Lean `IsSymplectic` likewise only constrains the
quadratic relationship between `A` and `b`. No spurious hypotheses
introduced.

## Dead ends
* `import Mathlib.Data.Matrix.Notation` failed to load: the `.olean` is
  not present in this project's built Mathlib (`ls .lake/.../Matrix/`
  shows 16 oleans, no `Notation.olean`). Switched to
  `Matrix.of (fun _ _ => (1/2 : ℝ))` per the strategy's fallback
  instructions — clean compile.
* First witness attempt was `def implicitMidpoint`, but `Real`
  division forces `noncomputable`. Adding the marker fixed it; no
  proof rework needed.
* First witness proof ended with `simp [...]` only, leaving the goal
  `2⁻¹ + 2⁻¹ - 1 = 0`. Adding `ring` closed it.

## Discovery
* `Mathlib.Data.Matrix.Notation` is **not** built in this project.
  Future witnesses that want `!![…]` syntax should either request it
  in a build update or use `Matrix.of (fun i j => …)` instead.
* `Matrix.vecMulVec u v` is the canonical Mathlib spelling of `u vᵀ`.
  Future symplecticity / algebraic-stability work (§357, §370, §372)
  can reuse it directly.
* The `symplecticityMatrix` definition can be lifted to a shared
  helper if `def:357B` (algebraic stability) is taken on next — the
  same matrix `M` appears with a positive-semidefinite predicate
  instead of `M = 0`.

## Suggested next approach
* **`def:357B` — algebraic stability.** Reuses
  `symplecticityMatrix` verbatim. Predicate is `bᵢ > 0 ∧
  (symplecticityMatrix R).PosSemidef`. Implicit midpoint is again the
  obvious witness (PSD trivial since `M = 0`). Estimated cost: ≤ 1
  cycle once `Matrix.PosSemidef` instance details are checked. Plan
  should refactor `symplecticityMatrix` to a shared file (e.g.
  `OpenMath/Chapter3/SymplecticityMatrix.lean` or just keep it in
  `Section370` and have `Section357` import).
* **`thm:372A` — order conditions for symplectic methods.** Direct
  consumer of `def:370A`; per the JSON `dependents` list, `thm:372A`
  is the only theorem that uses `def:370A`. Stating it requires Φ
  (already in `Section312`) and a notion of "order condition", so it
  may need partial decomposition. Worth scoping in the next planner
  cycle.
* **Avoid** the deferred targets in the cycle-027 strategy DO-NOT
  list (matrix resolvent, `α(t)/β(t)`, RK group infrastructure,
  Jordan canonical form, BN-stability fragment). All remain
  multi-cycle prereq investments.
