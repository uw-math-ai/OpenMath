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
`Fin (k+1) × Fin (k+1)` matrix; zero on the last row and last column.

Polymorphic in the scalar ring `R` (only `[Zero R]` is needed), so the
same definition is reusable when the §454 proof lifts the matrix to ℂ. -/
def gTopLeft {R : Type*} [Zero R] {k : ℕ} (G : Matrix (Fin k) (Fin k) R) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun i j =>
    if h : i.val < k ∧ j.val < k then
      G ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else 0

/-- Embed a `Fin k × Fin k` matrix `G` into the bottom-right `k × k` block of
a `Fin (k+1) × Fin (k+1)` matrix; zero on the first row and first column.

Polymorphic in the scalar ring `R` (only `[Zero R]` is needed). -/
def gBottomRight {R : Type*} [Zero R] {k : ℕ} (G : Matrix (Fin k) (Fin k) R) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
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

/-! ## Dahlquist (zero-)stability for BDF2 (cycle 346)

We ship `bdf2LMM.IsStable` directly from the homogeneous recurrence in
`OpenMath/Chapter4/Section404.lean`. BDF2's homogeneous recurrence
unfolds to `Y (m+2) = (4/3) · Y (m+1) - (1/3) · Y m`, whose
characteristic polynomial has roots `z = 1` and `z = 1/3` (both real,
both in the closed unit disc, root `1` simple). Closed-form solutions
are `Y_n = A + B · (1/3)^n` with
`A := (3·Y 1 - Y 0)/2` and `B := (3·(Y 0 - Y 1))/2`, derived from
matching `Y_0`, `Y_1`. Boundedness follows from
`|Y_n| ≤ |A| + |B|·(1/3)^n ≤ |A| + |B|`. -/

/-- BDF2's homogeneous-recurrence solutions decompose as
`Y_n = A + B · (1/3)^n` where
`A := (3 · Y 1 - Y 0) / 2` and `B := (3 · (Y 0 - Y 1)) / 2`.

Proved by strong induction on `n`; base cases at `n = 0, 1` are
direct arithmetic, and the inductive step at `n + 2` uses the
homogeneous recurrence `Y (n+2) = (4/3) · Y (n+1) - (1/3) · Y n`
plus the IH at `n + 1` and `n`. -/
private theorem bdf2_solution_decomp (Y : ℕ → ℝ)
    (hY : bdf2LMM.IsHomogeneousSolution Y) :
    ∀ n, Y n = (3 * Y 1 - Y 0) / 2
              + (3 * (Y 0 - Y 1)) / 2 * (1 / 3 : ℝ) ^ n := by
  -- Recurrence in clean form: `Y (m+2) = (4/3)·Y (m+1) + (-1/3)·Y m`.
  have hrec : ∀ m, Y (m + 2) = (4 / 3 : ℝ) * Y (m + 1) + (-1 / 3) * Y m := by
    intro m
    have h := hY m
    simp [bdf2LMM, Fin.sum_univ_two] at h
    linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp; ring
    | 1, _ => simp; ring
    | n + 2, ih =>
      rw [hrec n, ih (n + 1) (by omega), ih n (by omega)]
      ring

/-- **BDF2 is Dahlquist-stable** (Butcher §403, p. 341).

Every solution of BDF2's homogeneous recurrence is bounded: the
explicit decomposition (`bdf2_solution_decomp`) yields
`|Y_n| ≤ |A| + |B|`. -/
theorem bdf2LMM_isStable : bdf2LMM.IsStable := by
  intro Y hY
  refine ⟨|((3 * Y 1 - Y 0) / 2)| + |((3 * (Y 0 - Y 1)) / 2)|,
          fun n => ?_⟩
  rw [bdf2_solution_decomp Y hY n]
  have h_one_third_nonneg : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h_one_third_le_one : (1 / 3 : ℝ) ≤ 1 := by norm_num
  calc |((3 * Y 1 - Y 0) / 2) + ((3 * (Y 0 - Y 1)) / 2) * (1 / 3 : ℝ) ^ n|
      ≤ |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2) * (1 / 3 : ℝ) ^ n| := abs_add_le _ _
    _ = |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| * |(1 / 3 : ℝ) ^ n| := by rw [abs_mul]
    _ ≤ |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| * 1 := by
          gcongr
          rw [abs_pow, abs_of_nonneg h_one_third_nonneg]
          exact pow_le_one₀ h_one_third_nonneg h_one_third_le_one
    _ = |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| := by ring

/-! ## Consistency for BDF2 (cycle 349)

Ships `bdf2LMM.IsConsistent` as a **Phase D′.2.0 precursor** for the
cycle 348 scoping doc
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md` §5.

`IsConsistent` (Butcher §404, p. 339, def:404B) is the conjunction of
(404a) preconsistency and (404b) the order-1 consistency equation
`Σ_{i:Fin k} ((i:ℕ)+1) · α i.succ = Σ_{i:Fin (k+1)} β i`.

For BDF2 (`α₁ = 4/3, α₂ = -1/3, β₀ = 2/3, β₁ = β₂ = 0`):
* (404a): `α₁ + α₂ = 4/3 - 1/3 = 1` ✓
* (404b): LHS `= 1·(4/3) + 2·(-1/3) = 2/3`, RHS `= 2/3 + 0 + 0 = 2/3` ✓

We prove both conjuncts inline rather than reusing
`Section441.bdf2LMM_isPreconsistent` because Section441 imports
Section451 (cycle 346's stability ship), so the reverse import would
be circular. -/

/-- **BDF2 is consistent** (Butcher §404, p. 339).

Phase D′.2.0 precursor (cycle 349) — closes the `[MISSING]` entry in
the cycle 348 scoping doc §5 alongside `bdf2LMM_isStable` (cycle 346)
and `Section441.bdf2LMM_isPreconsistent` (cycle 175). -/
theorem bdf2LMM_isConsistent : bdf2LMM.IsConsistent := by
  refine ⟨?_, ?_⟩
  · -- (404a): Σ α i.succ = 1, i.e. α 1 + α 2 = 1
    simp [LinearMultistepMethod.IsPreconsistent, bdf2LMM, Fin.sum_univ_two]
    norm_num
  · -- (404b): Σ ((i:ℕ)+1) · α i.succ = Σ β i
    unfold LinearMultistepMethod.SatisfiesEq404b
    simp [bdf2LMM, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num

end OpenMath.Chapter4.Section451
