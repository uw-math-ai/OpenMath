import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Block
import OpenMath.Chapter5.Section510

/-!
# Butcher §523 — Non-linear stability (Theorem 523A)

This file formalizes the **algebraic stability identity** of Butcher §523
(Theorem 523A, p. 427).

## Textbook statement (quoted verbatim from `entities/thm_523A.json`)

> Let `Y` denote the vector of stage values, `F` the vector of stage
> derivatives and `y^[n−1]`, `y^[n]` the input and output respectively
> from a single step of a general linear method `(A, U, B, V)`. Assume
> that `M` is a positive semi-definite `(s + r) × (s + r)` matrix, where
> ```
> M = ⎡⎣ DA + Aᵀ D − Bᵀ G B     D U − Bᵀ G V    ⎤⎦
>     ⎣  Uᵀ D − Vᵀ G B          G − Vᵀ G V       ⎦,                 (523b)
> ```
> with `G` a positive semi-definite `r × r` matrix and `D` a positive
> semi-definite diagonal `s × s` matrix. Then
> ```
> ‖y^[n]‖²_G = ‖y^[n−1]‖²_G + 2⟨hF, Y⟩_D − ‖hF ⊕ y^[n−1]‖²_M.
> ```

## Faithfulness divergences

The **identity** stated below does **NOT** require `M` or `G` to be
positive semi-definite, nor `D` to be PSD (those hypotheses only enter
for the inequality corollary `thm:523B`). It does require `D` to be
**symmetric** (`Matrix.IsSymm`), which is automatically satisfied by
the textbook's PSD-diagonal `D` but is genuinely necessary for the
identity itself: the cross-terms `α ⬝ᵥ (DA *ᵥ α) - α ⬝ᵥ (Aᵀ D *ᵥ α)`
and `α ⬝ᵥ (DU *ᵥ y_prev) - y_prev ⬝ᵥ (Uᵀ D *ᵥ α)` collapse only when
`Dᵀ = D`. So this is a **strict generalisation** along `D` (we relax
from diagonal PSD to merely symmetric) and along `M`, `G` (we drop the
PSD hypotheses, which are needed only for `thm:523B`).

Additionally, we **decouple** the algebraic identity from
`IsGLMSolution`: the textbook frames `(Y, F, y_prev, y_next)` as
arising from a single step of the method, but the identity is a pure
algebraic statement about any four vectors related by the two step
equations. We take the step equations as explicit hypotheses
`hStage` and `hOut` rather than threading the existential
`IsGLMSolution` structure.

## Index conventions

We follow `OpenMath.Chapter5.Section510`'s GLM tableau convention:
- `A : Matrix (Fin s) (Fin s) ℝ` — internal-stage interaction;
- `U : Matrix (Fin s) (Fin r) ℝ` — input → internal stages;
- `B : Matrix (Fin r) (Fin s) ℝ` — internal stages → output;
- `V : Matrix (Fin r) (Fin r) ℝ` — input → output.

The composite `(s + r) × (s + r)` matrix `M` is built via
`Matrix.fromBlocks` over `Fin s ⊕ Fin r`.
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators

variable {s r : ℕ}

/-- The Butcher §523 algebraic-stability block matrix `M(D, G)` for a
general linear method `(A, U, B, V)`. Equation (523b):
```
M = ⎡ DA + Aᵀ D − Bᵀ G B     D U − Bᵀ G V ⎤
    ⎣  Uᵀ D − Vᵀ G B          G − Vᵀ G V  ⎦.
```
The textbook restricts `D` to PSD diagonal and `G` to PSD; we make no
such restriction at the definition level — those restrictions belong
to downstream theorems (e.g. `thm:523B`, the inequality corollary). -/
noncomputable def GeneralLinearMethod.algebraicStabilityMatrix
    (M : GeneralLinearMethod s r) (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin s ⊕ Fin r) (Fin s ⊕ Fin r) ℝ :=
  Matrix.fromBlocks
    (D * M.A + M.A.transpose * D - M.B.transpose * G * M.B)
    (D * M.U - M.B.transpose * G * M.V)
    (M.U.transpose * D - M.V.transpose * G * M.B)
    (G - M.V.transpose * G * M.V)

/-- **Theorem 523A** (Butcher §523, p. 427) — *Non-linear stability
identity for general linear methods.*

Let `Y` be the vector of stage values, `F` the vector of stage
derivatives, `y_prev` and `y_next` the input and output of a single
GLM step. The textbook step equations are
```
Y i      = h · ∑_j A_{ij} · F j  + ∑_j U_{ij} · y_prev j   (hStage)
y_next i = h · ∑_j B_{ij} · F j  + ∑_j V_{ij} · y_prev j   (hOut)
```
which we take as explicit hypotheses (decoupling from `IsGLMSolution`,
which existentially quantifies `Y`).

If `D` is symmetric, then the **algebraic identity**
```
‖y_next‖²_G  =  ‖y_prev‖²_G  +  2 ⟨hF, Y⟩_D  −  ‖hF ⊕ y_prev‖²_M
```
holds, where `‖·‖²_G` denotes `x ↦ x ⬝ᵥ (G *ᵥ x)`, `⟨·,·⟩_D` denotes
`(x, y) ↦ x ⬝ᵥ (D *ᵥ y)`, and `M := algebraicStabilityMatrix D G`.

**Faithfulness note**: the textbook assumes `M`, `G` PSD and `D` PSD
diagonal. The identity above holds whenever `D` is symmetric (strict
generalisation of PSD diagonal); the PSD hypotheses on `M` and `G`
enter only for the inequality corollary `thm:523B`. -/
theorem GeneralLinearMethod.algebraicStability_identity
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j) :
    y_next ⬝ᵥ (G *ᵥ y_next)
      = y_prev ⬝ᵥ (G *ᵥ y_prev)
        + 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
  -- Introduce the abbreviation α := hF.
  set α : Fin s → ℝ := fun i => h * F i with hα_def
  -- Step 1: rewrite Y and y_next in matrix-vector form.
  have hY : Y = M.A *ᵥ α + M.U *ᵥ y_prev := by
    funext i
    rw [hStage i]
    show _ = (M.A *ᵥ α) i + (M.U *ᵥ y_prev) i
    have h1 : (M.A *ᵥ α) i = h * ∑ j, M.A i j * F j := by
      simp only [Matrix.mulVec, dotProduct, hα_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    rfl
  have hyn : y_next = M.B *ᵥ α + M.V *ᵥ y_prev := by
    funext i
    rw [hOut i]
    show _ = (M.B *ᵥ α) i + (M.V *ᵥ y_prev) i
    have h1 : (M.B *ᵥ α) i = h * ∑ j, M.B i j * F j := by
      simp only [Matrix.mulVec, dotProduct, hα_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    rfl
  -- Step 2: expand the M-quadratic form.
  have hM_quad :
      (Sum.elim α y_prev)
        ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ Sum.elim α y_prev)
      = α ⬝ᵥ ((D * M.A) *ᵥ α)
        + α ⬝ᵥ ((M.A.transpose * D) *ᵥ α)
        - α ⬝ᵥ ((M.B.transpose * G * M.B) *ᵥ α)
        + α ⬝ᵥ ((D * M.U) *ᵥ y_prev)
        - α ⬝ᵥ ((M.B.transpose * G * M.V) *ᵥ y_prev)
        + y_prev ⬝ᵥ ((M.U.transpose * D) *ᵥ α)
        - y_prev ⬝ᵥ ((M.V.transpose * G * M.B) *ᵥ α)
        + y_prev ⬝ᵥ (G *ᵥ y_prev)
        - y_prev ⬝ᵥ ((M.V.transpose * G * M.V) *ᵥ y_prev) := by
    unfold GeneralLinearMethod.algebraicStabilityMatrix
    rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [sumElim_dotProduct_sumElim]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec,
               dotProduct_add, dotProduct_sub]
    ring
  -- Step 3: expand y_next ⬝ᵥ G y_next.
  -- Adjoint identity: (M₁ *ᵥ x) ⬝ᵥ (M₂ *ᵥ y) = x ⬝ᵥ ((M₁ᵀ * M₂) *ᵥ y).
  have lift : ∀ {s₁ s₂ s₃ : ℕ}
      (M₁ : Matrix (Fin s₁) (Fin s₂) ℝ) (M₂ : Matrix (Fin s₁) (Fin s₃) ℝ)
      (x : Fin s₂ → ℝ) (y : Fin s₃ → ℝ),
      (M₁ *ᵥ x) ⬝ᵥ (M₂ *ᵥ y) = x ⬝ᵥ ((M₁.transpose * M₂) *ᵥ y) := by
    intro s₁ s₂ s₃ M₁ M₂ x y
    rw [dotProduct_mulVec, Matrix.vecMul_mulVec, ← dotProduct_mulVec]
  have hLHS :
      (M.B *ᵥ α + M.V *ᵥ y_prev) ⬝ᵥ (G *ᵥ (M.B *ᵥ α + M.V *ᵥ y_prev))
      = α ⬝ᵥ ((M.B.transpose * G * M.B) *ᵥ α)
        + α ⬝ᵥ ((M.B.transpose * G * M.V) *ᵥ y_prev)
        + y_prev ⬝ᵥ ((M.V.transpose * G * M.B) *ᵥ α)
        + y_prev ⬝ᵥ ((M.V.transpose * G * M.V) *ᵥ y_prev) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    -- Collapse `G *ᵥ M.B *ᵥ α` to `(G * M.B) *ᵥ α` etc.
    simp only [Matrix.mulVec_mulVec]
    rw [lift M.B (G * M.B) α α, lift M.B (G * M.V) α y_prev,
        lift M.V (G * M.B) y_prev α, lift M.V (G * M.V) y_prev y_prev]
    -- Reassociate matrix products: B.transpose * (G * M.B) → B.transpose * G * M.B
    simp only [← Matrix.mul_assoc]
    ring
  -- Step 4: expand 2 * (α ⬝ᵥ (D *ᵥ Y)).
  have hCross : 2 * (α ⬝ᵥ (D *ᵥ Y))
      = 2 * (α ⬝ᵥ ((D * M.A) *ᵥ α)) + 2 * (α ⬝ᵥ ((D * M.U) *ᵥ y_prev)) := by
    rw [hY, Matrix.mulVec_add, dotProduct_add,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    ring
  -- Step 5: collapse the two D-symmetric cross-term identities.
  -- (5a) α ⬝ᵥ (AᵀD *ᵥ α) = α ⬝ᵥ (DA *ᵥ α). Uses Dᵀ = D.
  have hSymm1 : α ⬝ᵥ ((M.A.transpose * D) *ᵥ α) = α ⬝ᵥ ((D * M.A) *ᵥ α) := by
    -- AᵀD = (DA)ᵀ (using Dᵀ = D)
    have step1 : M.A.transpose * D = (D * M.A).transpose := by
      rw [Matrix.transpose_mul, hD]
    rw [step1, Matrix.mulVec_transpose]
    -- Now LHS = α ⬝ᵥ (α ᵥ* (D * M.A))
    -- Use dotProduct_comm + dotProduct_mulVec (rev) to close
    rw [show α ⬝ᵥ (α ᵥ* (D * M.A)) = (α ᵥ* (D * M.A)) ⬝ᵥ α from
          dotProduct_comm _ _]
    rw [← dotProduct_mulVec]
  -- (5b) y_prev ⬝ᵥ (UᵀD *ᵥ α) = α ⬝ᵥ (DU *ᵥ y_prev). Uses Dᵀ = D.
  have hSymm2 :
      y_prev ⬝ᵥ ((M.U.transpose * D) *ᵥ α) = α ⬝ᵥ ((D * M.U) *ᵥ y_prev) := by
    have step1 : M.U.transpose * D = (D * M.U).transpose := by
      rw [Matrix.transpose_mul, hD]
    rw [step1, Matrix.mulVec_transpose]
    -- Now LHS = y_prev ⬝ᵥ (α ᵥ* (D * M.U))
    rw [show y_prev ⬝ᵥ (α ᵥ* (D * M.U)) = (α ᵥ* (D * M.U)) ⬝ᵥ y_prev from
          dotProduct_comm _ _]
    rw [← dotProduct_mulVec]
  -- Step 6: combine.
  rw [hyn, hLHS, hY] at *
  rw [hM_quad, hCross, hSymm1, hSymm2]
  ring

/-! ### Non-vacuity witness at `explicitEulerGLM`

The following `example` confirms that the identity `algebraicStability_identity`
elaborates at the concrete `(s, r) = (1, 1)` GLM `explicitEulerGLM`
(`A = 0, U = 1, B = 1, V = 1`). Any `1 × 1` matrix is automatically
symmetric (a single entry), so `Matrix.isSymm_diagonal` discharges the
`D.IsSymm` hypothesis whenever we choose `D` as a diagonal matrix. The
identity then reads
`y_next ⬝ᵥ (G y_next) = y_prev ⬝ᵥ (G y_prev) + 2 (hF) ⬝ᵥ (D Y) − (hF ⊕ y_prev) ⬝ᵥ M (hF ⊕ y_prev)`
at the concrete dimensions `s = r = 1`. -/

example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hStage : ∀ i, Y i =
      h * (∑ j, explicitEulerGLM.A i j * F j) + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i =
      h * (∑ j, explicitEulerGLM.B i j * F j) + ∑ j, explicitEulerGLM.V i j * y_prev j) :
    let D : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => d)
    let G : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => g)
    y_next ⬝ᵥ (G *ᵥ y_next)
      = y_prev ⬝ᵥ (G *ᵥ y_prev)
        + 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (explicitEulerGLM.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) :=
  explicitEulerGLM.algebraicStability_identity _ _ (Matrix.isSymm_diagonal _)
    h F Y y_prev y_next hStage hOut

/-- *Algebraic-stability residual form (§523 corollary of
`algebraicStability_identity`).* Under the same hypotheses as
`algebraicStability_identity` (symmetric `D` and the GLM step
equations `hStage`, `hOut`), the difference `‖y_next‖²_G − ‖y_prev‖²_G`
factors as `2⟨hF, Y⟩_D − ‖hF ⊕ y_prev‖²_M`.

This is the textbook stepping-stone between `thm:523A`'s identity
(an equation of three terms) and `thm:523B`'s inequality. No sign
hypotheses are needed: it is a pure algebraic rearrangement. -/
theorem GeneralLinearMethod.algebraicStability_residual
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j) :
    y_next ⬝ᵥ (G *ᵥ y_next) - y_prev ⬝ᵥ (G *ᵥ y_prev)
      = 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
  have hId := M.algebraicStability_identity D G hD h F Y y_prev y_next hStage hOut
  linarith

/-! ### Non-vacuity witness for `algebraicStability_residual`

Mirroring the identity's non-vacuity example: at `(s, r) = (1, 1)`
on `explicitEulerGLM` with `D = diagonal d`, `G = diagonal g`,
`Matrix.isSymm_diagonal` discharges `D.IsSymm`. -/

example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hStage : ∀ i, Y i =
      h * (∑ j, explicitEulerGLM.A i j * F j) + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i =
      h * (∑ j, explicitEulerGLM.B i j * F j) + ∑ j, explicitEulerGLM.V i j * y_prev j) :
    y_next ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_next)
      - y_prev ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_prev)
      = 2 * ((fun i => h * F i) ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => d) *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (explicitEulerGLM.algebraicStabilityMatrix
                  (Matrix.diagonal (fun _ : Fin 1 => d))
                  (Matrix.diagonal (fun _ : Fin 1 => g)) *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) :=
  explicitEulerGLM.algebraicStability_residual _ _
    (Matrix.isSymm_diagonal _) h F Y y_prev y_next hStage hOut

/-- **Theorem 523B** (Butcher §523, p. 428) — *Non-linear stability
of a general linear method.*

If the algebraic-stability block matrix `M(D, G)` is positive
semi-definite, `D` is symmetric, and the step is *dissipative*
(`⟨hF, Y⟩_D ≤ 0`), then `‖y_next‖²_G ≤ ‖y_prev‖²_G`.

**Faithfulness note**: Butcher's textbook statement reads "if `M` is
PSD, then `‖y^[n]‖²_G ≤ ‖y^[n−1]‖²_G`". The dissipativity hypothesis
`⟨hF, Y⟩_D ≤ 0` is implicit in Butcher's §357/§523 framing — the
underlying ODE must be monotone/dissipative for non-linear stability
to make sense (same convention as B-stability and algebraic stability
in §357). We surface this hypothesis explicitly. The hypothesis on
`D` is symmetry (rather than the textbook's "PSD diagonal"), inherited
from `algebraicStability_identity` (which only needs `Dᵀ = D`); this
is a strict generalisation. -/
theorem GeneralLinearMethod.algebraicStability_inequality
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (hM_psd : (M.algebraicStabilityMatrix D G).PosSemidef)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j)
    (hDiss : (fun i => h * F i) ⬝ᵥ (D *ᵥ Y) ≤ 0) :
    y_next ⬝ᵥ (G *ᵥ y_next) ≤ y_prev ⬝ᵥ (G *ᵥ y_prev) := by
  -- Cycle 241's identity rewrites `‖y_next‖²_G` as a sum/difference of
  -- three real quantities. Two of them have known signs from the
  -- hypotheses, and the third is precisely `‖y_prev‖²_G`.
  have hId := M.algebraicStability_identity D G hD h F Y y_prev y_next hStage hOut
  -- PSD ⇒ M-quadratic form non-negative. `star x = x` for real `x`
  -- collapses via `simpa` (ℝ has `TrivialStar`).
  have hMq :
      0 ≤ (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
    simpa using hM_psd.dotProduct_mulVec_nonneg
      (Sum.elim (fun i => h * F i) y_prev)
  linarith

/-! ### Non-vacuity witness at `explicitEulerGLM` for the inequality

We mirror cycle 241's pattern: take `hPSD`, `hStage`, `hOut`, and
`hDiss` as hypotheses rather than constructing concrete witnesses.
The example confirms `algebraicStability_inequality` types at
`(s, r) = (1, 1)` with `D = diagonal d`, `G = diagonal g`. -/

example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hPSD : (explicitEulerGLM.algebraicStabilityMatrix
              (Matrix.diagonal (fun _ : Fin 1 => d))
              (Matrix.diagonal (fun _ : Fin 1 => g))).PosSemidef)
    (hStage : ∀ i, Y i =
      h * (∑ j, explicitEulerGLM.A i j * F j) + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i =
      h * (∑ j, explicitEulerGLM.B i j * F j) + ∑ j, explicitEulerGLM.V i j * y_prev j)
    (hDiss : (fun i => h * F i) ⬝ᵥ
             (Matrix.diagonal (fun _ : Fin 1 => d) *ᵥ Y) ≤ 0) :
    y_next ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_next)
      ≤ y_prev ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_prev) :=
  explicitEulerGLM.algebraicStability_inequality _ _
    (Matrix.isSymm_diagonal _) hPSD h F Y y_prev y_next hStage hOut hDiss

/-- *Algebraic-stability strict-contraction form (§523 strengthening of
`algebraicStability_inequality`).* Under the PSD hypothesis on the
algebraic-stability matrix `M(D, G)`, symmetric `D`, and a strict
dissipativity bound
`2⟨hF, Y⟩_D ≤ −(c − 1) · ‖hF ⊕ y_prev‖²_M` for some `c ≥ 1`, the GLM
step is contracting with explicit residual
`(c − 1) · ‖hF ⊕ y_prev‖²_M`:
```
‖y_next‖²_G  +  (c − 1) · ‖hF ⊕ y_prev‖²_M  ≤  ‖y_prev‖²_G.
```
At `c = 1` this recovers `algebraicStability_inequality` (with the
dissipativity bound `2⟨hF, Y⟩_D ≤ 0`, which is `⟨hF, Y⟩_D ≤ 0` times
2). The proof is a one-shot `linarith` from
`algebraicStability_residual` plus the PSD non-negativity of the
M-quadratic form.

**Faithfulness note**: this is NOT a textbook entity — it is a
strict-contraction strengthening of Butcher's `thm:523B` useful for
quantitative applications. Documented as infrastructure, not as a
new entity row. -/
theorem GeneralLinearMethod.algebraicStability_contracting
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hD : D.IsSymm)
    (hM_psd : (M.algebraicStabilityMatrix D G).PosSemidef)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j)
    (c : ℝ) (_hc : 1 ≤ c)
    (hContract : 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
                  ≤ -(c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
                    ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                          Sum.elim (fun i => h * F i) y_prev))) :
    y_next ⬝ᵥ (G *ᵥ y_next)
      + (c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
          ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                Sum.elim (fun i => h * F i) y_prev))
      ≤ y_prev ⬝ᵥ (G *ᵥ y_prev) := by
  have hRes := M.algebraicStability_residual D G hD h F Y y_prev y_next hStage hOut
  have hMq :
      0 ≤ (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ
                  Sum.elim (fun i => h * F i) y_prev) := by
    simpa using hM_psd.dotProduct_mulVec_nonneg
      (Sum.elim (fun i => h * F i) y_prev)
  linarith

/-! ### Non-vacuity witness for `algebraicStability_contracting`

Mirroring the inequality's non-vacuity example: at `(s, r) = (1, 1)`
on `explicitEulerGLM` with `D = diagonal d`, `G = diagonal g`,
`Matrix.isSymm_diagonal` discharges `D.IsSymm`. The PSD hypothesis,
the step equations, the contraction parameter `c ≥ 1`, and the
contraction bound are taken as parameters. -/

example (d g h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hPSD : (explicitEulerGLM.algebraicStabilityMatrix
              (Matrix.diagonal (fun _ : Fin 1 => d))
              (Matrix.diagonal (fun _ : Fin 1 => g))).PosSemidef)
    (hStage : ∀ i, Y i =
      h * (∑ j, explicitEulerGLM.A i j * F j) + ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i =
      h * (∑ j, explicitEulerGLM.B i j * F j) + ∑ j, explicitEulerGLM.V i j * y_prev j)
    (c : ℝ) (hc : 1 ≤ c)
    (hContract : 2 * ((fun i => h * F i) ⬝ᵥ
                       (Matrix.diagonal (fun _ : Fin 1 => d) *ᵥ Y))
                  ≤ -(c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
                    ⬝ᵥ (explicitEulerGLM.algebraicStabilityMatrix
                          (Matrix.diagonal (fun _ : Fin 1 => d))
                          (Matrix.diagonal (fun _ : Fin 1 => g)) *ᵥ
                          Sum.elim (fun i => h * F i) y_prev))) :
    y_next ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_next)
      + (c - 1) * ((Sum.elim (fun i => h * F i) y_prev)
          ⬝ᵥ (explicitEulerGLM.algebraicStabilityMatrix
                (Matrix.diagonal (fun _ : Fin 1 => d))
                (Matrix.diagonal (fun _ : Fin 1 => g)) *ᵥ
                Sum.elim (fun i => h * F i) y_prev))
      ≤ y_prev ⬝ᵥ (Matrix.diagonal (fun _ : Fin 1 => g) *ᵥ y_prev) :=
  explicitEulerGLM.algebraicStability_contracting _ _
    (Matrix.isSymm_diagonal _) hPSD h F Y y_prev y_next hStage hOut c hc hContract

end OpenMath.Chapter5.Section510
