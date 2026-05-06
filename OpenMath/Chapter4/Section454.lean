import Mathlib
import OpenMath.Chapter4.Section410
import OpenMath.Chapter4.Section451

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
