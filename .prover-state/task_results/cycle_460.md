# Cycle 460 Results

## Worked on

Opened a new tracked file `OpenMath/QuadraticLyapunov.lean` with the
abstract quadratic Lyapunov scaffold (per cycle-460 strategy). This is
prerequisite infrastructure for closing the BDF4–BDF6 global-error
theorems uniformly via the discrete Lyapunov equation
`Aᵀ P A − P = −Q`, replacing the per-method weighted-ℓ¹ approach that
was ruled out for BDF4 by `bdf4_lyapunov_gap.md`.

## Approach

Sorry-first scaffold with seven declarations:

1. `QuadraticLyapunov.QFPosDef` — `Pᵀ = P ∧ ∀ v ≠ 0, 0 < v ⬝ᵥ P.mulVec v`.
   Quadratic-form-flavored alternative to `Matrix.PosDef`, avoiding
   the `star`/`IsHermitian` complications of the Mathlib version on
   real-valued vectors.
2. `QuadraticLyapunov.QFPosSemidef` — `Qᵀ = Q ∧ ∀ v, 0 ≤ v ⬝ᵥ Q.mulVec v`.
3. `QuadraticLyapunov.IsLyapunovPair A P Q` — structure bundling
   `QFPosDef P`, `QFPosSemidef Q`, and `Aᵀ * P * A - P = -Q`.
4. `QuadraticLyapunov.lyapNorm P x := √(x ⬝ᵥ P.mulVec x)` (notation).
5. `QuadraticLyapunov.lyapNorm_sq_smul` — homogeneity in `c`.
6. `QuadraticLyapunov.lyapNorm_sq_step` — discrete Lyapunov identity:
   `(A x) ⬝ᵥ P (A x) = x ⬝ᵥ P x − x ⬝ᵥ Q x`. Closed by transposing the
   inner `mulVec` to `vecMul` via `vecMul_transpose`, associating
   matrix multiplication via `vecMul_vecMul`, and substituting
   `Aᵀ P A = P − Q`.
7. `QuadraticLyapunov.lyapNorm_sq_step_le` — drop the PSD `Q` term.
   One-line `linarith` from (6) and `QFPosSemidef`.
8. `QuadraticLyapunov.lyapNorm_sq_step_le_of_contractive` —
   `(A x) ⬝ᵥ P (A x) ≤ (1 − ε)(x ⬝ᵥ P x)` under
   `∀ v, ε · (v ⬝ᵥ P v) ≤ v ⬝ᵥ Q v`. One-line `linarith` from (6).
9. `QuadraticLyapunov.lyapNorm_eqv` — equivalence of the `P`-quadratic
   form with `∑ x_i²` on `Fin n → ℝ`, via constants `0 < c₀ ≤ c₁`.

## Result

PARTIAL SUCCESS — file compiles with **one** remaining sorry on
`lyapNorm_eqv` (declaration 7 in the strategy listing). All six other
declarations are fully closed.

Verified by:
```
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/QuadraticLyapunov.lean
```
which prints only the expected `declaration uses 'sorry'` warning on
`lyapNorm_eqv`.

The strategy explicitly allows leaving `lyapNorm_eqv` as the
"acceptable alternative" since the cleanest paths to it
(spectral-theorem decomposition of `P` as `Pᵀ = P` symmetric positive
definite, or compactness of the Euclidean unit sphere in `Fin n → ℝ`
combined with continuity of `x ↦ x ⬝ᵥ P x`) require nontrivial
Mathlib infrastructure that would have crowded a single cycle.

## Mathlib API reused

- `Matrix.dotProduct`, `Matrix.mulVec` for the quadratic-form
  expressions (`v ⬝ᵥ P.mulVec v`).
- `Matrix.mulVec_smul`, `dotProduct_smul`, `smul_dotProduct` for the
  homogeneity lemma.
- `Matrix.mulVec_mulVec`, `Matrix.dotProduct_mulVec`,
  `Matrix.vecMul_transpose`, `Matrix.vecMul_vecMul`,
  `Matrix.mul_assoc` to turn
  `(A x) ⬝ᵥ P.mulVec (A x)` into `x ⬝ᵥ (Aᵀ * P * A).mulVec x`.
- `Matrix.sub_mulVec`, `dotProduct_sub` to distribute `A x ⬝ (P-Q) x`.

We did **not** use `Matrix.PosDef` directly — instead the file packages
positive (semi)definiteness via the quadratic-form predicates
`QFPosDef`/`QFPosSemidef`. This decouples downstream BDF4–BDF6 work
from the `star`/`IsHermitian` machinery and keeps the file standalone,
matching the strategy's "package the quadratic-form versions directly"
fallback.

## Aristotle plan

The strategy's batch of five targets reduced to **one** non-trivial
target after manual closure of the four algebraic lemmas:

- Submitted `lyapnorm_eqv.lean` (project ID
  `a32132c6-1e02-4e2e-a3c3-1b8c9db2e3dd`) as a focused job pointing
  Aristotle at `Matrix.PosDef`, `Matrix.PosDef.eigenvalues_pos`,
  `Matrix.IsHermitian.spectral_theorem`, and the compactness-of-unit-
  sphere route.

Aristotle was still in `QUEUED` (never started) after the 30-minute
wait. Per strategy, the sorry stays for the BDF4 follow-up cycle to
either inherit it or close it before consuming `lyapNorm_eqv`.

## Sorrys remaining

- `OpenMath/QuadraticLyapunov.lean:lyapNorm_eqv` — equivalence of the
  `P`-quadratic form with the Euclidean form, single sorry.

## Discovery

- `Matrix.dotProduct_mulVec` + `Matrix.vecMul_transpose` +
  `Matrix.vecMul_vecMul` is the right combination to push a matrix
  factor across the dot product symbolically, without ever touching
  index-level `Finset.sum` formulas. This pattern will likely recur
  when computing the `P` matrix for BDF4 from `Aᵀ P A − P = −I`.
- Mathlib's `Matrix.PosDef` requires `IsHermitian` and `star x ⬝ᵥ ...`,
  which is awkward for real-valued vectors. The quadratic-form
  predicates `QFPosDef`/`QFPosSemidef` are the cleaner public API for
  downstream LMM Lyapunov work.

## Suggested next approach (BDF4 follow-up cycle)

1. Solve the discrete Lyapunov equation `Aᵀ P A − P = −I` for BDF4's
   4×4 companion matrix
   `A = [[0,1,0,0],[0,0,1,0],[0,0,0,1],[-3/25, 16/25, -36/25, 48/25]]`.
   The unknown is a 4×4 symmetric matrix `P` with 10 unknowns; the
   equation gives 16 scalar equations of which 10 are independent
   (after symmetrization), so `P` is uniquely determined and rational.
2. Verify `P ≻ 0` numerically (smallest eigenvalue strictly positive);
   in Lean, prove `QFPosDef P` either by a direct `v ⬝ᵥ P v` SOS
   certificate or via a Schur-complement decomposition.
3. Find an `ε > 0` and prove `∀ v, ε · (v ⬝ᵥ P v) ≤ v ⬝ᵥ I v = ‖v‖²`
   (i.e., `P ⪯ ε⁻¹ · I`); take `ε = 1/λ_max(P)`.
4. Apply `QuadraticLyapunov.lyapNorm_sq_step_le_of_contractive` to
   the BDF4 4-window error vector to get the contractive step bound,
   then close with discrete Grönwall + initial bound + extraction of
   the per-component error.
5. Once `lyapNorm_eqv` lands (this cycle's sorry), the conversion
   between `‖e_n‖_P` and the textbook max-norm becomes a straight
   sandwich.

## Dead ends

- Initial attempt at `lyapNorm_sq_step` tried `rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`
  expecting both `P.mulVec (A.mulVec x)` and `(Aᵀ * P * A).mulVec x` to
  fold; only the first folds because the second is already in product
  form on the RHS. Fix: drop the second `rw` and instead push the
  outer `A.mulVec` using `vecMul_transpose` followed by `vecMul_vecMul`
  and `← dotProduct_mulVec`.
- `ring` does not work on `Matrix` equalities of the form
  `Aᵀ * P * A = (Aᵀ * P * A - P) + P` because `Matrix n n ℝ` is a
  noncommutative ring; `abel` is the right tactic since the identity
  is purely additive.
- `Matrix.dotProduct_smul` and `Matrix.dotProduct_sub` are at the
  root namespace (no `Matrix.` prefix) — the dotProduct lemmas live
  outside `Matrix` namespace in `Mathlib.Data.Matrix.Mul`.

## Acceptance criteria status

- ✅ New file `OpenMath/QuadraticLyapunov.lean` compiles.
- ✅ All seven declarations present.
- ⚠️  One sorry remains, on `lyapNorm_eqv`. Allowed per strategy
  (acceptable alternative noted in declaration 7). Marked `[~]` in
  `plan.md`.
- ✅ `plan.md` updated with the new "Generic Lyapunov Infrastructure"
  subsection of Chapter 1 §1.2.
