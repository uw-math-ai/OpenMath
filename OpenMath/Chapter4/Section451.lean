import Mathlib
import OpenMath.Chapter4.Section404

/-!
# Butcher §451 — G-stability for linear multistep / one-leg methods

This file formalises Butcher Definition 451A (p. 363):

> A one-leg method `[α, β]` is `G-stable' if `M` given by (451e) is
> positive semi-definite.

with the matrix `M` from equation (451e):

  `M = α βᵀ + β αᵀ − [G 0; 0 0] + [0 0; 0 G]`

where the `(k+1)`-vectors `α, β` are
`α = (1, −α₁, −α₂, …, −α_k)`, `β = (β₀, β₁, …, β_k)` (per §451's
display on p. 363) and the two block matrices embed the chosen
`k × k` symmetric positive-definite `G` into the top-left and
bottom-right blocks of a `(k+1) × (k+1)` matrix respectively.

## Reference

* Butcher, *Numerical Methods for Ordinary Differential Equations*,
  3rd ed., §451 "The concept of G-stability", pp. 361–363, Definition
  451A and equation (451e).
* `extraction/formalization_data/entities/def_451A.json`

## Convention bridge to `LinearMultistepMethod`

Our `LinearMultistepMethod` (Section404) uses the leading-coefficient
normalisation `α 0 = -1`. The textbook §451 uses the convention where
the α-vector for the matrix construction has leading entry `1` and
subsequent entries `-α_i`. The bridge is `alphaVec i = -M.α i` —
unwrapping `M.α 0 = -1` gives `alphaVec 0 = 1`, and for `i ≥ 1` the
textbook entries `-α_i` match `-M.α i` since our `M.α i.succ = α_i`
(textbook).

## Non-vacuity

We provide BDF2 as the textbook's worked example (Butcher §451,
p. 363) with its explicit `G = ((10/9, -4/9), (-4/9, 2/9))` witness.
-/

open scoped NNReal Topology

namespace OpenMath.Chapter4.Section404

/-! ## §451 vector and matrix infrastructure

The vector- and matrix-valued helpers attached to `LinearMultistepMethod`
live in `Section404`'s namespace so we can use the dot-notation
`M.alphaVec`, `M.gMatrix`, etc. -/

/-- Textbook §451 α-vector. Written in (451e) as
`(1, -α₁, -α₂, …, -α_k)`. Since our `LinearMultistepMethod` records
`α 0 = -1` and `α i.succ = α_i` (textbook), the textbook α-vector is
the entrywise negation `i ↦ -M.α i`. -/
def LinearMultistepMethod.alphaVec {k : ℕ} (M : LinearMultistepMethod k) :
    Fin (k + 1) → ℝ := fun i => -M.α i

/-- Textbook §451 β-vector: `(β₀, β₁, …, β_k)`. Matches `M.β` directly. -/
def LinearMultistepMethod.betaVec {k : ℕ} (M : LinearMultistepMethod k) :
    Fin (k + 1) → ℝ := M.β

/-- Embed a `Fin k × Fin k` matrix `G` into the top-left `k × k` block of a
`Fin (k+1) × Fin (k+1)` matrix; zero on the last row and last column. -/
def gTopLeft {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : i.val < k ∧ j.val < k then
      G ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else 0

/-- Embed a `Fin k × Fin k` matrix `G` into the bottom-right `k × k` block of
a `Fin (k+1) × Fin (k+1)` matrix; zero on the first row and first column. -/
def gBottomRight {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : 0 < i.val ∧ 0 < j.val then
      G ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    else 0

/-- Butcher (451e). For an LMM `M` and an auxiliary `k × k` matrix `G`,

  `M.gMatrix G = α βᵀ + β αᵀ - [G 0; 0 0] + [0 0; 0 G]`. -/
def LinearMultistepMethod.gMatrix {k : ℕ}
    (M : LinearMultistepMethod k)
    (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.vecMulVec M.alphaVec M.betaVec
    + Matrix.vecMulVec M.betaVec M.alphaVec
    - gTopLeft G
    + gBottomRight G

/-- Butcher Definition 451A. A linear multistep method (treated as a one-leg
method) is *G-stable* if there exists a symmetric positive-definite `k × k`
matrix `G` such that the matrix `M.gMatrix G` from (451e) is positive
semi-definite.

The textbook says "A one-leg method `[α, β]` is G-stable if `M` given by
(451e) is positive semi-definite", parameterised by an unstated symmetric
positive-definite `G`. The standard reading — and the only one consistent
with the BDF2 example on the same page (where `G` is *exhibited*) — is
that G-stability is the existence of such a `G`. -/
def LinearMultistepMethod.IsGStable {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∃ G : Matrix (Fin k) (Fin k) ℝ, G.IsSymm ∧ G.PosDef ∧
    (M.gMatrix G).PosSemidef

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section451

open OpenMath.Chapter4.Section404 (LinearMultistepMethod)
open Matrix

/-! ## Non-vacuity — BDF2 (Butcher §451, p. 363)

BDF2 in textbook (400b) form is
`y_n = (4/3) y_{n-1} - (1/3) y_{n-2} + (2/3) h f(x_n, y_n)`.
In our `LinearMultistepMethod` convention with `α 0 = -1`, this is
`α 0 = -1, α 1 = 4/3, α 2 = -1/3`, `β 0 = 2/3, β 1 = β 2 = 0`.

The textbook gives the witness `G = ((10/9, -4/9), (-4/9, 2/9))` and
asserts the resulting `M(G)` is positive semi-definite. Direct
calculation shows
`M(G) = (2/9) · u · uᵀ` where `u = (1, -2, 1)`,
so `M(G)` is rank-1 PSD. -/

/-- BDF2 as a 2-step linear multistep method. Coefficient values from
Butcher §451, p. 363:
* `α(z) = 1 - (4/3)z + (1/3)z²` ⇒ `α 1 = 4/3, α 2 = -1/3`,
* `β(z) = 2/3` ⇒ `β 0 = 2/3, β 1 = β 2 = 0`. -/
noncomputable def bdf2LMM : LinearMultistepMethod 2 where
  α := fun i =>
    match i with
    | ⟨0, _⟩ => -1
    | ⟨1, _⟩ => 4 / 3
    | ⟨2, _⟩ => -1 / 3
  β := fun i =>
    match i with
    | ⟨0, _⟩ => 2 / 3
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
  α_zero := rfl

/-- The textbook witness `G = ((10/9, -4/9), (-4/9, 2/9))` from
Butcher §451, p. 363. -/
noncomputable def bdf2GWitness : Matrix (Fin 2) (Fin 2) ℝ :=
  !![10 / 9, -4 / 9; -4 / 9, 2 / 9]

/-- Auxiliary "rank-1 generator" vector `u = (1, -2, 1) : Fin 3 → ℝ`.
The matrix `bdf2LMM.gMatrix bdf2GWitness` equals `(2/9) · u · uᵀ`,
which exhibits it as a rank-1 positive semi-definite matrix. -/
def bdf2RankOneVec : Fin 3 → ℝ :=
  fun i => match i with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => -2
    | ⟨2, _⟩ => 1

/-- The textbook `G` for BDF2 is symmetric. -/
theorem bdf2GWitness_isSymm : bdf2GWitness.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The textbook `G` for BDF2 is positive definite. By direct computation,
the quadratic form is `(10/9) x₀² - (8/9) x₀ x₁ + (2/9) x₁²`, which is
strictly positive for nonzero `x` (leading minor `10/9 > 0` and
determinant `4/81 > 0`). -/
theorem bdf2GWitness_posDef : bdf2GWitness.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [bdf2GWitness]
  · intro x hx
    have h0 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      ext i
      fin_cases i <;> simp [h.1, h.2]
    have hxs : (star x : Fin 2 → ℝ) = x := by
      funext i; exact star_trivial _
    rw [hxs]
    have key : x ⬝ᵥ (bdf2GWitness *ᵥ x) =
        (10 / 9) * (x 0) ^ 2 - (8 / 9) * (x 0) * (x 1) + (2 / 9) * (x 1) ^ 2 := by
      simp [bdf2GWitness, dotProduct, Fin.sum_univ_two, Matrix.mulVec]
      ring
    rw [key]
    rcases h0 with hx0 | hx1
    · nlinarith [sq_nonneg (5 * (x 0) - 2 * (x 1)), sq_nonneg (x 1), sq_nonneg (x 0),
        mul_self_pos.mpr hx0]
    · nlinarith [sq_nonneg (5 * (x 0) - 2 * (x 1)), sq_nonneg (x 1), sq_nonneg (x 0),
        mul_self_pos.mpr hx1]

/-- The matrix `bdf2LMM.gMatrix bdf2GWitness` equals `(2/9) · u · uᵀ`
where `u = (1, -2, 1)` is `bdf2RankOneVec`. Direct entry-wise
calculation:
* `α-vec = (1, -4/3, 1/3)`, `β-vec = (2/3, 0, 0)`.
* `α βᵀ + β αᵀ = [4/3, -8/9, 2/9; -8/9, 0, 0; 2/9, 0, 0]`.
* Subtract `[G 0; 0 0]` and add `[0 0; 0 G]` (with the textbook
  `G`) to land at `(2/9) · (1,-2,1) · (1,-2,1)ᵀ`. -/
theorem bdf2_gMatrix_eq_smul_vecMulVec :
    bdf2LMM.gMatrix bdf2GWitness =
      (2 / 9 : ℝ) • Matrix.vecMulVec bdf2RankOneVec bdf2RankOneVec := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdf2LMM, bdf2GWitness, bdf2RankOneVec,
      OpenMath.Chapter4.Section404.LinearMultistepMethod.gMatrix,
      OpenMath.Chapter4.Section404.LinearMultistepMethod.alphaVec,
      OpenMath.Chapter4.Section404.LinearMultistepMethod.betaVec,
      OpenMath.Chapter4.Section404.gTopLeft,
      OpenMath.Chapter4.Section404.gBottomRight,
      Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply] <;> norm_num

/-- The matrix `bdf2LMM.gMatrix bdf2GWitness` is positive semi-definite.
Proof: by `bdf2_gMatrix_eq_smul_vecMulVec` it is a non-negative scalar
multiple of `vecMulVec u u = u uᵀ`, which is PSD by
`Matrix.posSemidef_vecMulVec_self_star` (specialised to ℝ where
`star = id`). -/
theorem bdf2_gMatrix_posSemidef :
    (bdf2LMM.gMatrix bdf2GWitness).PosSemidef := by
  rw [bdf2_gMatrix_eq_smul_vecMulVec]
  refine Matrix.PosSemidef.smul ?_ (by norm_num : (0 : ℝ) ≤ 2 / 9)
  -- For real numbers, `star v = v`, so `vecMulVec v (star v) = vecMulVec v v`.
  have hstar : (star bdf2RankOneVec : Fin 3 → ℝ) = bdf2RankOneVec := by
    funext i; exact star_trivial _
  have := Matrix.posSemidef_vecMulVec_self_star (R := ℝ) bdf2RankOneVec
  simpa [hstar] using this

/-- BDF2 is G-stable (Butcher §451, p. 363, worked example). -/
theorem bdf2LMM_isGStable : bdf2LMM.IsGStable :=
  ⟨bdf2GWitness, bdf2GWitness_isSymm, bdf2GWitness_posDef,
    bdf2_gMatrix_posSemidef⟩

end OpenMath.Chapter4.Section451
