import Mathlib

/-!
# Generic quadratic Lyapunov scaffold

Abstract infrastructure for quadratic discrete Lyapunov analysis used by
BDF4–BDF6 global error bounds. Given a square real matrix `A`, a positive
definite symmetric `P`, and a positive semidefinite symmetric `Q` with

    Aᵀ * P * A - P = -Q,

the quadratic form `lyapNorm² P x := x ⬝ᵥ P.mulVec x` satisfies

    (A x) ⬝ᵥ P (A x) = x ⬝ᵥ P x - x ⬝ᵥ Q x ≤ x ⬝ᵥ P x,

and if `Q ≥ ε · P` (in the quadratic-form sense) then

    (A x) ⬝ᵥ P (A x) ≤ (1 - ε) · (x ⬝ᵥ P x),

which is the contractive step bound used downstream by a discrete Grönwall
argument. We also state the equivalence of the `P`-quadratic form with the
Euclidean norm.

This file is **standalone** so it can be reused by BDF4, BDF5, BDF6, and
future LMM Lyapunov work without entangling per-method state.
-/

namespace QuadraticLyapunov

open Matrix

variable {n : ℕ}

/-- Quadratic-form positive definiteness: `P` is symmetric and `v ⬝ᵥ P v > 0`
for all `v ≠ 0`. -/
def QFPosDef (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Pᵀ = P ∧ ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ P.mulVec v

/-- Quadratic-form positive semidefiniteness: `Q` is symmetric and
`v ⬝ᵥ Q v ≥ 0` for all `v`. -/
def QFPosSemidef (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Qᵀ = Q ∧ ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ Q.mulVec v

/-- `(A, P, Q)` is a Lyapunov triple: the discrete Lyapunov equation
`Aᵀ P A - P = -Q` holds with `P ≻ 0` and `Q ⪰ 0`. -/
structure IsLyapunovPair (A P Q : Matrix (Fin n) (Fin n) ℝ) : Prop where
  posDef : QFPosDef P
  posSemidef : QFPosSemidef Q
  eq : Aᵀ * P * A - P = -Q

/-- The Lyapunov norm `‖x‖_P = √(x ⬝ᵥ P x)`. -/
noncomputable def lyapNorm (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ P.mulVec x)

/-- Homogeneity of the `P`-quadratic form: scaling by `c` scales the form by `c²`. -/
lemma lyapNorm_sq_smul (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    (c • x) ⬝ᵥ P.mulVec (c • x) = c ^ 2 * (x ⬝ᵥ P.mulVec x) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp [smul_eq_mul]
  ring

/-- Discrete Lyapunov identity: under `Aᵀ P A - P = -Q`,
`(A x) ⬝ᵥ P (A x) = x ⬝ᵥ P x - x ⬝ᵥ Q x`. -/
lemma lyapNorm_sq_step {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (h : IsLyapunovPair A P Q) (x : Fin n → ℝ) :
    A.mulVec x ⬝ᵥ P.mulVec (A.mulVec x)
      = x ⬝ᵥ P.mulVec x - x ⬝ᵥ Q.mulVec x := by
  -- Step 1: rewrite LHS as `x ⬝ᵥ (Aᵀ * P * A).mulVec x`.
  have lhs_eq : A.mulVec x ⬝ᵥ P.mulVec (A.mulVec x)
      = x ⬝ᵥ (Aᵀ * P * A).mulVec x := by
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    rw [show A.mulVec x = Matrix.vecMul x Aᵀ from (Matrix.vecMul_transpose A x).symm]
    rw [Matrix.vecMul_vecMul]
    rw [← Matrix.dotProduct_mulVec]
    rw [Matrix.mul_assoc]
  -- Step 2: substitute Aᵀ * P * A = P - Q.
  have hAPA : Aᵀ * P * A = P - Q := by
    have heq := h.eq
    have hsplit : Aᵀ * P * A = (Aᵀ * P * A - P) + P := by abel
    rw [hsplit, heq]; abel
  rw [lhs_eq, hAPA, Matrix.sub_mulVec, dotProduct_sub]

/-- Step bound: `(A x) ⬝ᵥ P (A x) ≤ x ⬝ᵥ P x` for any Lyapunov pair. -/
lemma lyapNorm_sq_step_le {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (h : IsLyapunovPair A P Q) (x : Fin n → ℝ) :
    A.mulVec x ⬝ᵥ P.mulVec (A.mulVec x) ≤ x ⬝ᵥ P.mulVec x := by
  have h1 := lyapNorm_sq_step h x
  have h2 := h.posSemidef.2 x
  linarith

/-- Contractive step bound: if additionally `Q ⪰ ε · P` (in the
quadratic-form sense), then `(A x) ⬝ᵥ P (A x) ≤ (1 - ε) · (x ⬝ᵥ P x)`. -/
lemma lyapNorm_sq_step_le_of_contractive
    {A P Q : Matrix (Fin n) (Fin n) ℝ} (h : IsLyapunovPair A P Q)
    {ε : ℝ}
    (hcontr : ∀ v : Fin n → ℝ, ε * (v ⬝ᵥ P.mulVec v) ≤ v ⬝ᵥ Q.mulVec v)
    (x : Fin n → ℝ) :
    A.mulVec x ⬝ᵥ P.mulVec (A.mulVec x) ≤ (1 - ε) * (x ⬝ᵥ P.mulVec x) := by
  have h1 := lyapNorm_sq_step h x
  have h2 := hcontr x
  linarith

/-- Equivalence of the `P`-quadratic form with the Euclidean norm: there
exist constants `0 < c₀ ≤ c₁` such that `c₀ ‖x‖² ≤ x ⬝ᵥ P x ≤ c₁ ‖x‖²` for
all `x`. (Standard finite-dimensional fact: by spectral decomposition,
`c₀` and `c₁` may be taken to be the minimum and maximum eigenvalues
of `P`.) -/
lemma lyapNorm_eqv {P : Matrix (Fin n) (Fin n) ℝ} (hP : QFPosDef P) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧
      ∀ x : Fin n → ℝ,
        c₀ * (∑ i, (x i) ^ 2) ≤ x ⬝ᵥ P.mulVec x ∧
        x ⬝ᵥ P.mulVec x ≤ c₁ * (∑ i, (x i) ^ 2) := by
  sorry

end QuadraticLyapunov
