import Mathlib
import OpenMath.Chapter4.Section410
import OpenMath.Chapter4.Section451
import OpenMath.Chapter4.Section454Aux

/-!
# Butcher §454 — A-stability for LMMs (Theorem 454A scaffolding)

This file opens Butcher §454 "Concluding remarks on G-stability"
(Butcher 2008, p. 387) by formalising:

* `LinearMultistepMethod.IsAStable` — the A-stability predicate for
  LMMs in the boundary-locus form Butcher's §454 proof actually
  uses, `‖w‖ < 1 ∧ β(w) ≠ 0 ⇒ Re(α(w)/β(w)) > 0`.
* `aeval_αPoly_eq`, `aeval_βPoly_eq` — bridge lemmas connecting the
  §410 polynomial form `αPoly`/`βPoly` and the §451 vector form
  `M.alphaVec`/`M.betaVec`. These will be reused in cycle 167's
  proof of Theorem 454A.
* `explicitEulerLMM_not_isAStable` — refutability witness; explicit
  Euler is *not* A-stable (negative non-vacuity).

## Status

Butcher's Theorem 454A — "a G-stable LMM is A-stable" — is **not
yet formalised**; see `.prover-state/issues/thm_454A_stage_2_3_stall.md`
for the planned cycle 167 path: prove `algebraic_identity_454A`
(the §451e quadratic form identity) and the complex-lift PSD/PD
helpers, then derive `gStable_isAStable` from them.

This cycle ships the predicate + refutability witness so that future
cycles have well-typed targets to aim at.

## Reference

* Butcher, *Numerical Methods for Ordinary Differential Equations*,
  3rd ed., §454 "Concluding remarks on G-stability", p. 387, Theorem
  454A and its proof.
* `extraction/formalization_data/entities/thm_454A.json`

## Faithfulness note

`IsAStable` here is the **boundary-locus form** of A-stability, i.e.
the criterion Butcher *uses* in the proof of Theorem 454A. The
equivalent characterisation "the stability region contains the
closed left half-plane" is a non-trivial maximum-modulus / boundary-
locus statement; we do not prove the equivalence in this file.
-/

open scoped NNReal Topology ComplexOrder
open Polynomial Matrix Complex

namespace OpenMath.Chapter4.Section404

/-- **Butcher §454 A-stability for LMMs (boundary-locus criterion).**

A linear multistep method `[α, β]` is *A-stable* iff for every
complex `w` with `‖w‖ < 1` such that `β(w) ≠ 0`, the value
`α(w) / β(w)` lies in the open right half-plane (positive real
part).

This is the form Butcher uses in his §454 proof of Theorem 454A
(Butcher 2008, p. 387): "We use the criterion that if `|w| < 1`,
then `z = α(w)/β(w)` is in the right half-plane."

The equivalent characterisation "the stability region contains the
closed left half-plane" follows by maximum-modulus / boundary-locus
arguments (Butcher §351 / Hairer-Wanner II.4); we do not formalise
this equivalence in this file. -/
def LinearMultistepMethod.IsAStable {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∀ w : ℂ, ‖w‖ < 1 →
    Polynomial.aeval w (OpenMath.Chapter4.Section410.βPoly M) ≠ 0 →
    0 < (Polynomial.aeval w (OpenMath.Chapter4.Section410.αPoly M) /
          Polynomial.aeval w (OpenMath.Chapter4.Section410.βPoly M)).re

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section454

open OpenMath.Chapter4.Section404
open OpenMath.Chapter4.Section410

/-! ## Vandermonde test vectors

For a complex `w` and step count `k`, the §454 proof uses two
Vandermonde-like vectors:
* `vanW : Fin (k+1) → ℂ`, `vanW i = wⁱ` — the test vector for the
  `(k+1) × (k+1)` matrix `M(G)`.
* `vanW₁ : Fin k → ℂ`, `vanW₁ i = wⁱ` — the test vector for the
  inner block `G`. -/

/-- Vandermonde test vector `W = (1, w, w², …, wᵏ) : Fin (k+1) → ℂ`. -/
def vanW {k : ℕ} (w : ℂ) : Fin (k + 1) → ℂ := fun i => w ^ i.val

/-- Inner Vandermonde test vector `W₁ = (1, w, w², …, wᵏ⁻¹) : Fin k → ℂ`. -/
def vanW₁ {k : ℕ} (w : ℂ) : Fin k → ℂ := fun i => w ^ i.val

@[simp] theorem vanW_apply {k : ℕ} (w : ℂ) (i : Fin (k + 1)) :
    vanW (k := k) w i = w ^ i.val := rfl

@[simp] theorem vanW₁_apply {k : ℕ} (w : ℂ) (i : Fin k) :
    vanW₁ (k := k) w i = w ^ i.val := rfl

/-! ## Bridge: §410 polynomial form ↔ §451 vector form

Both `αPoly` and `βPoly` evaluate at a complex `w` to a sum
`Σ (vec j) wʲ`, where `vec` is the §451 alpha/beta-vector lifted to
ℂ. We package these as helper lemmas to bridge the §410
polynomial form and the §451 vector/matrix form. These will be
reused by cycle 167's `algebraic_identity_454A`. -/

private theorem aeval_C_mul_X_pow_real (c : ℝ) (m : ℕ) (w : ℂ) :
    Polynomial.aeval w (Polynomial.C c * Polynomial.X ^ m) = (c : ℂ) * w ^ m := by
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  congr 1

/-- `aeval w (αPoly M) = Σ alphaVec j · wʲ`. The §410 α-polynomial
evaluated at `w` equals the dot product of `M.alphaVec` (lifted to
ℂ) and `vanW w`. -/
theorem aeval_αPoly_eq {k : ℕ} (M : LinearMultistepMethod k) (w : ℂ) :
    Polynomial.aeval w (αPoly M) =
      ∑ i : Fin (k + 1), (M.alphaVec i : ℂ) * w ^ i.val := by
  unfold αPoly LinearMultistepMethod.alphaVec
  rw [map_sub, map_one, map_sum, Fin.sum_univ_succ]
  have h0 : M.α 0 = -1 := M.α_zero
  have hα0 : ((-M.α 0 : ℝ) : ℂ) = 1 := by rw [h0]; push_cast; ring
  have h00 : ((0 : Fin (k + 1)) : ℕ) = 0 := rfl
  rw [h00, pow_zero, mul_one, hα0]
  rw [show (1 : ℂ) - ∑ i : Fin k, Polynomial.aeval w
      (Polynomial.C (M.α i.succ) * Polynomial.X ^ (↑i + 1)) =
      1 + (- ∑ i : Fin k, Polynomial.aeval w
        (Polynomial.C (M.α i.succ) * Polynomial.X ^ (↑i + 1))) from by ring]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_C_mul_X_pow_real]
  have hsv : (i.succ : ℕ) = (i.val + 1) := rfl
  rw [hsv]
  push_cast
  ring

/-- `aeval w (βPoly M) = Σ betaVec j · wʲ`. -/
theorem aeval_βPoly_eq {k : ℕ} (M : LinearMultistepMethod k) (w : ℂ) :
    Polynomial.aeval w (βPoly M) =
      ∑ i : Fin (k + 1), (M.betaVec i : ℂ) * w ^ i.val := by
  unfold βPoly LinearMultistepMethod.betaVec
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact aeval_C_mul_X_pow_real _ _ _

/-! ## Quadratic-form factorisation of `gTopLeft` and `gBottomRight`

The §454 proof of Theorem 454A computes
`star W ⬝ᵥ (gTopLeft G *ᵥ W)` and
`star W ⬝ᵥ (gBottomRight G *ᵥ W)` separately and identifies them
with quadratic forms on a truncated/shifted Vandermonde vector.
Cycle 166's monolithic proof of the §451e identity stalled Lean
elaboration because both block embeddings unfolded simultaneously
under nested dependent if-then-else. We factor the two
computations as standalone named theorems with their own boundary-
case sub-lemmas (each ≤ 5 lines) so Lean elaborates each piece
independently. -/

private theorem gTopLeft_apply_castSucc {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    gTopLeft G i.castSucc j.castSucc = G i j := by
  unfold gTopLeft
  rw [Matrix.of_apply, dif_pos ⟨i.is_lt, j.is_lt⟩]
  rfl

private theorem gTopLeft_apply_last_row {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (j : Fin (k + 1)) :
    gTopLeft G (Fin.last k) j = 0 := by
  unfold gTopLeft
  rw [Matrix.of_apply, dif_neg]
  exact fun h => absurd h.1 (by simp [Fin.val_last])

private theorem gTopLeft_apply_last_col {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (i : Fin (k + 1)) :
    gTopLeft G i (Fin.last k) = 0 := by
  unfold gTopLeft
  rw [Matrix.of_apply, dif_neg]
  exact fun h => absurd h.2 (by simp [Fin.val_last])

private theorem gTopLeft_mulVec_castSucc {R : Type*} [NonAssocSemiring R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) (i : Fin k) :
    (gTopLeft G *ᵥ W) i.castSucc =
      (G *ᵥ (fun j : Fin k => W j.castSucc)) i := by
  show (∑ j, gTopLeft G i.castSucc j * W j) =
       ∑ j, G i j * W j.castSucc
  rw [Fin.sum_univ_castSucc]
  rw [gTopLeft_apply_last_col, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gTopLeft_apply_castSucc]

private theorem gTopLeft_mulVec_last {R : Type*} [NonAssocSemiring R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    (gTopLeft G *ᵥ W) (Fin.last k) = 0 := by
  show (∑ j, gTopLeft G (Fin.last k) j * W j) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [gTopLeft_apply_last_row, zero_mul]

/-- **Quadratic-form factorisation for `gTopLeft G`.**
The quadratic form `star W ⬝ᵥ (gTopLeft G *ᵥ W)` on the
`(k+1)`-vector `W` collapses to the quadratic form of `G` on the
truncated `k`-vector `(W ∘ Fin.castSucc)`. -/
theorem gTopLeft_quadForm_eq {R : Type*} [CommRing R] [StarRing R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    star W ⬝ᵥ (gTopLeft G *ᵥ W) =
      star (fun i : Fin k => W i.castSucc) ⬝ᵥ
        (G *ᵥ (fun i : Fin k => W i.castSucc)) := by
  show (∑ i, star (W i) * (gTopLeft G *ᵥ W) i) =
       ∑ i : Fin k, star (W i.castSucc) *
         (G *ᵥ (fun j : Fin k => W j.castSucc)) i
  rw [Fin.sum_univ_castSucc]
  rw [gTopLeft_mulVec_last, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gTopLeft_mulVec_castSucc]

private theorem gBottomRight_apply_succ {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    gBottomRight G i.succ j.succ = G i j := by
  unfold gBottomRight
  rw [Matrix.of_apply,
    dif_pos (⟨by simp [Fin.val_succ], by simp [Fin.val_succ]⟩ :
              0 < i.succ.val ∧ 0 < j.succ.val)]
  congr 1

private theorem gBottomRight_apply_zero_row {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (j : Fin (k + 1)) :
    gBottomRight G 0 j = 0 := by
  unfold gBottomRight
  rw [Matrix.of_apply, dif_neg]
  exact fun h => absurd h.1 (by simp)

private theorem gBottomRight_apply_zero_col {R : Type*} [Zero R] {k : ℕ}
    (G : Matrix (Fin k) (Fin k) R) (i : Fin (k + 1)) :
    gBottomRight G i 0 = 0 := by
  unfold gBottomRight
  rw [Matrix.of_apply, dif_neg]
  exact fun h => absurd h.2 (by simp)

private theorem gBottomRight_mulVec_succ {R : Type*} [NonAssocSemiring R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) (i : Fin k) :
    (gBottomRight G *ᵥ W) i.succ =
      (G *ᵥ (fun j : Fin k => W j.succ)) i := by
  show (∑ j, gBottomRight G i.succ j * W j) =
       ∑ j, G i j * W j.succ
  rw [Fin.sum_univ_succ]
  rw [gBottomRight_apply_zero_col, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gBottomRight_apply_succ]

private theorem gBottomRight_mulVec_zero {R : Type*} [NonAssocSemiring R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    (gBottomRight G *ᵥ W) 0 = 0 := by
  show (∑ j, gBottomRight G 0 j * W j) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [gBottomRight_apply_zero_row, zero_mul]

/-- **Quadratic-form factorisation for `gBottomRight G`.**
The quadratic form `star W ⬝ᵥ (gBottomRight G *ᵥ W)` collapses to
the quadratic form of `G` on the shifted `k`-vector
`(W ∘ Fin.succ)`. -/
theorem gBottomRight_quadForm_eq {R : Type*} [CommRing R] [StarRing R]
    {k : ℕ} (G : Matrix (Fin k) (Fin k) R) (W : Fin (k + 1) → R) :
    star W ⬝ᵥ (gBottomRight G *ᵥ W) =
      star (fun i : Fin k => W i.succ) ⬝ᵥ
        (G *ᵥ (fun i : Fin k => W i.succ)) := by
  show (∑ i, star (W i) * (gBottomRight G *ᵥ W) i) =
       ∑ i : Fin k, star (W i.succ) *
         (G *ᵥ (fun j : Fin k => W j.succ)) i
  rw [Fin.sum_univ_succ]
  rw [gBottomRight_mulVec_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gBottomRight_mulVec_succ]

/-! ## §454 algebraic identity — `algebraic_identity_454A`

The §454 proof of Theorem 454A computes
`star W ⬝ᵥ ((M.gMatrix G).map (algebraMap ℝ ℂ) *ᵥ W)` for `W = vanW w`
over ℂ and identifies it with `α(w) β̄(w) + ᾱ(w) β(w)`
plus a remainder involving `(1 - ‖w‖²)` and the inner-block
quadratic form on `vanW₁`. This is the textbook formula on p. 387
that bridges the matrix definition of G-stability to A-stability.

Per cycle 167's named-decomposition playbook, we factor the proof
into ≤10-line `private` named pieces (1.A through 1.E) that the
public theorem `algebraic_identity_454A` (1.F) assembles via
single-line `rw`s. -/

/-! ### 1.A. Map commutation lemmas -/

private theorem gTopLeft_map_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {k : ℕ} (G : Matrix (Fin k) (Fin k) R) :
    (gTopLeft G).map φ = gTopLeft (G.map φ) := by
  ext i j
  unfold gTopLeft
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
  split_ifs with h
  · rw [Matrix.map_apply]
  · exact φ.map_zero

private theorem gBottomRight_map_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {k : ℕ} (G : Matrix (Fin k) (Fin k) R) :
    (gBottomRight G).map φ = gBottomRight (G.map φ) := by
  ext i j
  unfold gBottomRight
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
  split_ifs with h
  · rw [Matrix.map_apply]
  · exact φ.map_zero

private theorem vecMulVec_map_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {n m : ℕ} (a : Fin n → R) (b : Fin m → R) :
    (Matrix.vecMulVec a b).map φ =
      Matrix.vecMulVec (fun i => φ (a i)) (fun j => φ (b j)) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.map_apply, φ.map_mul]

private theorem gMatrix_map_eq {k : ℕ} (M : LinearMultistepMethod k)
    (G : Matrix (Fin k) (Fin k) ℝ) :
    (M.gMatrix G).map (algebraMap ℝ ℂ) =
      Matrix.vecMulVec (fun i => (M.alphaVec i : ℂ)) (fun j => (M.betaVec j : ℂ))
      + Matrix.vecMulVec (fun i => (M.betaVec i : ℂ)) (fun j => (M.alphaVec j : ℂ))
      - gTopLeft (G.map (algebraMap ℝ ℂ))
      + gBottomRight (G.map (algebraMap ℝ ℂ)) := by
  unfold LinearMultistepMethod.gMatrix
  rw [Matrix.map_add _ (map_add _),
      Matrix.map_sub _ (map_sub _),
      Matrix.map_add _ (map_add _),
      vecMulVec_map_eq, vecMulVec_map_eq, gTopLeft_map_eq, gBottomRight_map_eq]
  rfl

/-! ### 1.B. vecMulVec quadratic-form lift -/

private theorem vecMulVec_dotProduct_lift {n : ℕ}
    (a b : Fin n → ℝ) (W : Fin n → ℂ) :
    star W ⬝ᵥ
      (Matrix.vecMulVec (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) *ᵥ W) =
    (star W ⬝ᵥ (fun i => (a i : ℂ))) * ((fun j => (b j : ℂ)) ⬝ᵥ W) := by
  show (∑ i, star (W i) * ∑ j, (a i : ℂ) * (b j : ℂ) * W j) =
       (∑ i, star (W i) * (a i : ℂ)) * (∑ j, (b j : ℂ) * W j)
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### 1.C. aeval-via-dotProduct identities -/

private theorem aeval_αPoly_as_dotProduct {k : ℕ}
    (M : LinearMultistepMethod k) (w : ℂ) :
    (fun i : Fin (k + 1) => (M.alphaVec i : ℂ)) ⬝ᵥ vanW (k := k) w =
      Polynomial.aeval w (αPoly M) := by
  rw [aeval_αPoly_eq]
  rfl

private theorem aeval_βPoly_as_dotProduct {k : ℕ}
    (M : LinearMultistepMethod k) (w : ℂ) :
    (fun i : Fin (k + 1) => (M.betaVec i : ℂ)) ⬝ᵥ vanW (k := k) w =
      Polynomial.aeval w (βPoly M) := by
  rw [aeval_βPoly_eq]
  rfl

private theorem star_vanW_dotProduct_alpha {k : ℕ}
    (M : LinearMultistepMethod k) (w : ℂ) :
    star (vanW (k := k) w) ⬝ᵥ (fun i : Fin (k + 1) => (M.alphaVec i : ℂ)) =
      star (Polynomial.aeval w (αPoly M)) := by
  rw [aeval_αPoly_eq, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show star (vanW w i) * (M.alphaVec i : ℂ) = star ((M.alphaVec i : ℂ) * w ^ i.val)
  rw [vanW_apply, StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]

private theorem star_vanW_dotProduct_beta {k : ℕ}
    (M : LinearMultistepMethod k) (w : ℂ) :
    star (vanW (k := k) w) ⬝ᵥ (fun i : Fin (k + 1) => (M.betaVec i : ℂ)) =
      star (Polynomial.aeval w (βPoly M)) := by
  rw [aeval_βPoly_eq, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show star (vanW w i) * (M.betaVec i : ℂ) = star ((M.betaVec i : ℂ) * w ^ i.val)
  rw [vanW_apply, StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]

/-! ### 1.D. Vandermonde shift identities -/

private theorem vanW_castSucc_eq_vanW₁ {k : ℕ} (w : ℂ) :
    (fun i : Fin k => vanW (k := k) w i.castSucc) = vanW₁ (k := k) w := by
  funext i; rfl

private theorem vanW_succ_eq_smul_vanW₁ {k : ℕ} (w : ℂ) :
    (fun i : Fin k => vanW (k := k) w i.succ) = w • vanW₁ (k := k) w := by
  funext i
  show w ^ (i.val + 1) = w * w ^ i.val
  rw [pow_succ, mul_comm]

/-! ### 1.E. smul-quadratic-form / normSq collapse -/

private theorem star_smul_dotProduct_smul {k : ℕ}
    (G : Matrix (Fin k) (Fin k) ℂ) (W : Fin k → ℂ) (z : ℂ) :
    star (z • W) ⬝ᵥ (G *ᵥ (z • W)) =
      (star z * z) * (star W ⬝ᵥ (G *ᵥ W)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul]
  ring

private theorem star_w_mul_w_eq_normSq_complex (w : ℂ) :
    (star w) * w = ((‖w‖^2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj, ← Complex.normSq_eq_norm_sq]

/-! ### 1.F. The §454 algebraic identity (Theorem 454A's algebraic core) -/

/-- **§454 algebraic identity (`algebraic_identity_454A`).** For any LMM `M`,
auxiliary `k × k` real matrix `G`, and complex `w`,

  `W^* · M(G) · W = α(w)* · β(w) + β(w)* · α(w)
                    - (1 - ‖w‖²) · W₁^* · G · W₁`

where `W = (1, w, …, wᵏ)`, `W₁ = (1, w, …, wᵏ⁻¹)`, `M(G)` is the §451e
quadratic-form matrix, and `α, β` are the §410 polynomials.

This is the textbook identity from Butcher §454, p. 387: in the proof of
Theorem 454A, Butcher rearranges `α(w)β̄(w) + ᾱ(w)β(w) = W^* M W + (1 -
|w|²) ∑_{j,l} g_{jl} wʲ⁻¹ w̄ˡ⁻¹`. -/
theorem algebraic_identity_454A {k : ℕ}
    (M : LinearMultistepMethod k)
    (G : Matrix (Fin k) (Fin k) ℝ) (w : ℂ) :
    star (vanW (k := k) w) ⬝ᵥ
      ((M.gMatrix G).map (algebraMap ℝ ℂ) *ᵥ vanW (k := k) w) =
    star (Polynomial.aeval w (αPoly M)) * Polynomial.aeval w (βPoly M)
      + star (Polynomial.aeval w (βPoly M)) * Polynomial.aeval w (αPoly M)
      - (1 - ((‖w‖^2 : ℝ) : ℂ)) *
          (star (vanW₁ (k := k) w) ⬝ᵥ
            (G.map (algebraMap ℝ ℂ) *ᵥ vanW₁ (k := k) w)) := by
  rw [gMatrix_map_eq]
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_add]
  rw [vecMulVec_dotProduct_lift, vecMulVec_dotProduct_lift]
  rw [star_vanW_dotProduct_alpha, star_vanW_dotProduct_beta,
      aeval_βPoly_as_dotProduct, aeval_αPoly_as_dotProduct]
  rw [gTopLeft_quadForm_eq, gBottomRight_quadForm_eq]
  rw [vanW_castSucc_eq_vanW₁, vanW_succ_eq_smul_vanW₁]
  rw [star_smul_dotProduct_smul, star_w_mul_w_eq_normSq_complex]
  ring

/-! ## Refutability — explicit Euler is NOT A-stable -/

/-- **Non-vacuity (negative).** Explicit Euler is not A-stable.

We exhibit `w := -9/10 + 0i`. Then:
* `‖w‖ = 9/10 < 1` ✓
* `αPoly = 1 - X` (cycle 074, `αPoly_explicitEuler`), so
  `α(w) = 1 - (-9/10) = 19/10`.
* `βPoly = X` (cycle 074, `βPoly_explicitEuler`), so
  `β(w) = -9/10 ≠ 0` ✓.
* `α(w) / β(w) = (19/10) / (-9/10) = -19/9` has `Re = -19/9 < 0`.

Hence `IsAStable` would imply `0 < -19/9`, a contradiction.

This validates that the predicate is actually refutable (not
trivially true), and serves as a sanity check that the predicate
is non-vacuous in *both* directions: BDF2 should be A-stable
(future cycle, via Theorem 454A); explicit Euler is not. -/
theorem explicitEulerLMM_not_isAStable :
    ¬ explicitEulerLMM.IsAStable := by
  intro hA
  set w : ℂ := ((-9 / 10 : ℝ) : ℂ) with hw_def
  have hw_norm : ‖w‖ < 1 := by
    rw [hw_def, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hβw : Polynomial.aeval w (βPoly explicitEulerLMM) ≠ 0 := by
    rw [βPoly_explicitEuler, Polynomial.aeval_X, hw_def]
    intro h
    have := congrArg Complex.re h
    simp at this
  have hpos := hA w hw_norm hβw
  rw [αPoly_explicitEuler, βPoly_explicitEuler,
      Polynomial.aeval_X] at hpos
  have hα : Polynomial.aeval w ((1 : Polynomial ℝ) - Polynomial.X) =
      ((19 / 10 : ℝ) : ℂ) := by
    rw [map_sub, map_one, Polynomial.aeval_X, hw_def]
    push_cast
    ring
  rw [hα] at hpos
  have heq : (((19 / 10 : ℝ) : ℂ) / w).re = -19 / 9 := by
    rw [hw_def]
    have : (((19 / 10 : ℝ) : ℂ) / ((-9 / 10 : ℝ) : ℂ)) =
        (((-19 / 9 : ℝ) : ℂ)) := by
      push_cast
      field_simp
    rw [this, Complex.ofReal_re]
  rw [heq] at hpos
  norm_num at hpos

end OpenMath.Chapter4.Section454

namespace OpenMath.Chapter4.Section404

open OpenMath.Chapter4.Section454
open OpenMath.Chapter4.Section410
open OpenMath.Chapter4.Section454Aux

/-! ## §454 Theorem 454A — a G-stable LMM is A-stable

The proof composes the algebraic identity (`algebraic_identity_454A`)
with the complex-lift PSD/PD helpers from `Section454Aux`. We
decompose into seven private named pieces (Steps 4–8 below + two
glue lemmas), each ≤ ~25 LOC, per cycle 168's named-decomposition
playbook. -/

/-- **Step 4.** The LHS of the §454 identity has non-negative real
part, by PSD-ness of `M.gMatrix G` (lifted to ℂ via `algebraMap ℝ ℂ`)
and `Section454Aux.complexLift_re_dotProduct_nonneg_of_real_posSemidef`. -/
private theorem gMatrix_quadForm_re_nonneg
    {k : ℕ} {M : LinearMultistepMethod k} {G : Matrix (Fin k) (Fin k) ℝ}
    (hPSD : (M.gMatrix G).PosSemidef) (w : ℂ) :
    0 ≤ (star (vanW (k := k) w) ⬝ᵥ
          ((M.gMatrix G).map (algebraMap ℝ ℂ) *ᵥ vanW (k := k) w)).re :=
  (complexLift_re_dotProduct_nonneg_of_real_posSemidef hPSD _).1

/-- **Step 5.** The inner-block quadratic form of `G` on `vanW₁ w`
has strictly positive real part, by PD-ness of `G` and the
non-vanishing witness `vanW₁ w 0 = 1`. Requires `0 < k` so that
`Fin k` is inhabited. -/
private theorem G_quadForm_W₁_re_pos
    {k : ℕ} {G : Matrix (Fin k) (Fin k) ℝ} (hPD : G.PosDef) {w : ℂ}
    (hk : 0 < k) :
    0 < (star (vanW₁ (k := k) w) ⬝ᵥ
          (G.map (algebraMap ℝ ℂ) *ᵥ vanW₁ (k := k) w)).re := by
  refine complexLift_re_dotProduct_pos_of_real_posDef hPD ?_
  intro hzero
  have h0 : vanW₁ (k := k) w ⟨0, hk⟩ = 1 := by
    show w ^ (0 : ℕ) = 1
    exact pow_zero w
  have h0' : vanW₁ (k := k) w ⟨0, hk⟩ = 0 := by
    rw [hzero]; rfl
  rw [h0'] at h0
  exact one_ne_zero h0.symm

/-- **Step 6.** `1 - ‖w‖²` is strictly positive when `‖w‖ < 1`,
extracted as the real part of the complex coercion `(1 : ℂ) -
((‖w‖² : ℝ) : ℂ)`. -/
private theorem one_sub_normSq_re_pos {w : ℂ} (hw : ‖w‖ < 1) :
    (0 : ℝ) < ((1 : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖w‖, hw, hw_nn]

/-- **Step 8.** From `0 < (star α · β).re` and `β ≠ 0`, conclude
`0 < (α / β).re`. The complex-arithmetic finisher. -/
private theorem alpha_div_beta_re_pos_of_star_alpha_beta_re_pos
    {α β : ℂ} (hβ : β ≠ 0) (h : 0 < (star α * β).re) :
    0 < (α / β).re := by
  rw [Complex.div_re]
  have hstar : (star α * β).re = α.re * β.re + α.im * β.im := by
    show ((starRingEnd ℂ) α * β).re = α.re * β.re + α.im * β.im
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hstar] at h
  have hnsq : 0 < Complex.normSq β := Complex.normSq_pos.mpr hβ
  have h_eq :
      α.re * β.re / Complex.normSq β + α.im * β.im / Complex.normSq β
        = (α.re * β.re + α.im * β.im) / Complex.normSq β := by
    rw [← add_div]
  rw [h_eq]
  exact div_pos h hnsq

/-- **Glue lemma.** The two cross terms in `α(w)β̄(w) + ᾱ(w)β(w)`
have equal real parts, since each is the conjugate of the other. -/
private theorem star_beta_alpha_re_eq_star_alpha_beta_re (α β : ℂ) :
    (star β * α).re = (star α * β).re := by
  show ((starRingEnd ℂ) β * α).re = ((starRingEnd ℂ) α * β).re
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.conj_re, Complex.conj_im]
  ring

/-- **Glue lemma.** Multiplying the complex coercion of a real number
by another complex number, the real part factors as `c.re * z.re`
because the imaginary part of the coercion is zero. -/
private theorem mul_re_of_real_complex (r : ℝ) (z : ℂ) :
    (((1 : ℂ) - ((r : ℝ) : ℂ)) * z).re =
      ((1 : ℂ) - ((r : ℝ) : ℂ)).re * z.re := by
  rw [Complex.mul_re]
  have him : ((1 : ℂ) - ((r : ℝ) : ℂ)).im = 0 := by
    rw [Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero]
  rw [him, zero_mul, sub_zero]

/-- **Step 7.** From G-stability of `M`, `‖w‖ < 1`, and `0 < k`,
the real part of `star (α(w)) · β(w)` is strictly positive. This is
the analytic core of Theorem 454A.

Take `.re` of `algebraic_identity_454A`. The LHS is `≥ 0` by Step 4,
the cross-term sum collapses to `2 · Re(star α · β)`, and the
remainder term is `(1 - ‖w‖²) · (W₁* G W₁).re`, both factors
strictly positive (Steps 5 and 6). Linear arithmetic finishes. -/
private theorem star_alpha_beta_re_pos
    {k : ℕ} {M : LinearMultistepMethod k} (hG : M.IsGStable)
    {w : ℂ} (hw : ‖w‖ < 1) (hk : 0 < k) :
    0 < (star (Polynomial.aeval w (αPoly M)) *
          Polynomial.aeval w (βPoly M)).re := by
  obtain ⟨G, _, hPD, hPSD⟩ := hG
  have hid := algebraic_identity_454A M G w
  have hLHS_nn := gMatrix_quadForm_re_nonneg hPSD w
  have hW₁_pos := G_quadForm_W₁_re_pos hPD (w := w) hk
  have hOnemNorm := one_sub_normSq_re_pos hw
  have hsymm := star_beta_alpha_re_eq_star_alpha_beta_re
    (Polynomial.aeval w (αPoly M)) (Polynomial.aeval w (βPoly M))
  have hid_re := congrArg Complex.re hid
  rw [Complex.sub_re, Complex.add_re, mul_re_of_real_complex, hsymm] at hid_re
  nlinarith [hLHS_nn, hOnemNorm, hW₁_pos,
             mul_pos hOnemNorm hW₁_pos]

/-- **Butcher Theorem 454A — a G-stable LMM is A-stable**
(§454, p. 387).

We use the boundary-locus form of A-stability (the `IsAStable`
predicate): `∀ w, ‖w‖ < 1 ∧ β(w) ≠ 0 ⇒ Re(α(w)/β(w)) > 0`.

**Faithfulness divergence.** The textbook statement does not list a
hypothesis `0 < k`, but Butcher implicitly assumes `k ≥ 1` throughout
§451–§454 (an LMM with `k = 0` is degenerate). We add the precondition
explicitly. -/
theorem LinearMultistepMethod.gStable_isAStable {k : ℕ}
    (M : LinearMultistepMethod k) (hk : 0 < k) (hG : M.IsGStable) :
    M.IsAStable := by
  intro w hw_norm hβw
  have hpos := star_alpha_beta_re_pos hG hw_norm hk
  exact alpha_div_beta_re_pos_of_star_alpha_beta_re_pos hβw hpos

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section454

open OpenMath.Chapter4.Section451

/-- **BDF2 is A-stable.** Direct corollary of cycle 165's
`bdf2LMM_isGStable` and Theorem 454A (`gStable_isAStable`). -/
theorem bdf2LMM_isAStable : bdf2LMM.IsAStable :=
  bdf2LMM.gStable_isAStable (by norm_num) bdf2LMM_isGStable

end OpenMath.Chapter4.Section454
