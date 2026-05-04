import OpenMath.LMMAsGLM
import OpenMath.LMMAsGLM.Stability
import OpenMath.Helpers.BlockAdjugate
import OpenMath.LMMAsGLM.StabilityCharpoly
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Butcher §521 — Step C.14 + D/E/F/G/H/I/J/K eval-ladder

This module continues `OpenMath/LMMAsGLM/StabilityCharpoly.lean` with
the textbook-form headline
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual`
and the evaluation ladder culminating in
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly` (Step K.1,
cycle 736).

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §521.
-/

open Finset Real

namespace LMM

variable {s : ℕ}

/-- §521 Step C.14 — General `s`-step LMM headline in textbook form.
`D · charpoly = X^s · stabilityPolyPoly + X^s · C(z) · correction
                  − residual`, obtained by feeding the cycle 696
bridge `activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction`
into the cycle 690 active-form headline
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`. The
correction sum vanishes coefficient-by-coefficient when
`β(castSucc l) = β_last · α(castSucc l)` (in particular under BDF),
recovering the cycle 643 BDF headline
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`. -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * m.stabilityPolyPoly z
        + (Polynomial.X : Polynomial ℂ) ^ s *
            ( Polynomial.C z *
                ∑ l : Fin s,
                  Polynomial.C
                      (((m.β l.castSucc : ℝ) : ℂ) -
                        ((m.β (Fin.last s) : ℝ) : ℂ) *
                          ((m.α l.castSucc : ℝ) : ℂ)) *
                    Polynomial.X ^ (l : ℕ) )
        - ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( rowFAlphaPoly m +
                (toGLM_stabilityMatrixPY m 0).charpoly *
                  rowFBetaPoly m ) *
              Polynomial.C z ) := by
  rw [D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual m hz hs,
      activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction m z]
  ring

/-- §521 Step C.15 — BDF consistency check between the cycle 698 general
LMM textbook headline and the cycle 643 BDF headline. The "extra"
`X^s · C(z) · correction − residual` terms in the general identity must
collapse to zero under BDF; equivalently, the residual equals the
`X^s · C(z) · correction` summand under BDF. Direct subtraction of the
two headlines. -/
theorem residual_eq_X_pow_mul_correction_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
        Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
      + ( rowFAlphaPoly m +
            (toGLM_stabilityMatrixPY m 0).charpoly *
              rowFBetaPoly m ) *
          Polynomial.C z
    =
    (Polynomial.X : Polynomial ℂ) ^ s *
      ( Polynomial.C z *
          ∑ l : Fin s,
            Polynomial.C
                (((m.β l.castSucc : ℝ) : ℂ) -
                  ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ)) *
              Polynomial.X ^ (l : ℕ) ) := by
  have hgen :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual m hz hs
  have hbd :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf m z hbdf hz
  linear_combination hgen - hbd

/-- §521 Step C.16 — Scalar evaluation of the cycle 698 textbook
headline at an arbitrary complex point `ξ`. Distributes
`Polynomial.eval ξ` over the polynomial identity, exposing the
matrix charpoly evaluation in terms of the textbook scalar
stability function. -/
theorem D_mul_toGLM_charpoly_eval_eq
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval ξ =
      ξ^s * (m.stabilityPolyPoly z).eval ξ
        + ξ^s * (z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) ) * ξ^(l : ℕ))
        - ( (rowYQuot m).eval ξ * ξ^s *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval ξ +
                ((toGLM_stabilityMatrixPY m 0).charpoly).eval ξ *
                  (rowFBetaPoly m).eval ξ ) * z ) := by
  have h :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual m hz hs
  have := congrArg (Polynomial.eval ξ) h
  simpa [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finset_sum] using this

/-- §521 Step C.17 — Under BDF, for every `ξ ≠ 0` and every `z` with
non-zero denominator `D = 1 - z·β_last`, the GLM stability-matrix
characteristic polynomial vanishes at `ξ` iff the textbook scalar
stability polynomial `stabilityPolyPoly z` vanishes at `ξ`. The
non-zero hypothesis on `ξ` discards the `X^s` factor on the RHS of
`D · charpoly = X^s · stabilityPolyPoly`. Direct evaluation of the
cycle 643 BDF headline at `ξ`. -/
theorem toGLM_charpoly_eval_eq_zero_iff_stabilityPoly_of_bdf
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hξ : ξ ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
      (m.stabilityPolyPoly z).eval ξ = 0 := by
  have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf
              m z hbdf hz
  have heval := congrArg (Polynomial.eval ξ) h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  have hξs : ξ ^ s ≠ 0 := pow_ne_zero _ hξ
  constructor
  · intro hcp
    rw [hcp, mul_zero] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left hξs
  · intro hsp
    rw [hsp, mul_zero] at heval
    exact (mul_eq_zero.mp heval).resolve_left hz

/-- §521 Step C.17 contrapositive — Under BDF, the GLM matrix charpoly
is non-vanishing at every non-zero `ξ` iff the textbook scalar
stability polynomial is non-vanishing at every non-zero `ξ`. Useful
form for the unit-disk root-counting argument that drives
`LMM.toGLM_isAStable_iff`. -/
theorem toGLM_charpoly_eval_ne_zero_iff_stabilityPoly_of_bdf
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hξ : ξ ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ ≠ 0 ↔
      (m.stabilityPolyPoly z).eval ξ ≠ 0 :=
  (toGLM_charpoly_eval_eq_zero_iff_stabilityPoly_of_bdf
     m ξ hbdf hz hξ).not

/-- §521 Step C.18 — Under BDF, with `s ≥ 1` and non-zero denominator
`D = 1 - z β_last`, the GLM stability-matrix characteristic polynomial
vanishes at `ξ = 0`. This is the boundary case excluded from Step C.17
(cycle 702) and pins down the spurious-root structure of the BDF
charpoly: every zero of `(m.toGLM.stabilityMatrix z).charpoly` other
than `ξ = 0` is a zero of `m.stabilityPolyPoly z`. Direct evaluation of
the cycle 643 BDF headline `D · charpoly = X^s · stabilityPolyPoly` at
`ξ = 0`, where `X^s` collapses to `0^s = 0` for `s ≥ 1`. -/
theorem toGLM_charpoly_eval_zero_eq_zero_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hs : 0 < s) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf
              m z hbdf hz
  have heval := congrArg (Polynomial.eval (0 : ℂ)) h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  rw [zero_pow hs.ne', zero_mul] at heval
  exact (mul_eq_zero.mp heval).resolve_left hz

/-- §521 Step C.19 — Under BDF, with `s ≥ 1` (from `[NeZero s]`) and
non-zero denominator `D = 1 - z β_last`, the GLM stability-matrix
characteristic polynomial vanishes at `ξ` iff `ξ = 0` or
`m.stabilityPolyPoly z` vanishes at `ξ`. Combines Step C.17 (cycle 702)
non-zero-roots scalar bridge and Step C.18 (cycle 704) `ξ = 0` boundary
case into a unified eval-form iff with no side condition on `ξ`.
Mirrors the IsRoot-form `toGLM_stabilityMatrix_eigenvalue_iff_of_bdf`
in scalar evaluation form. -/
theorem toGLM_charpoly_eval_eq_zero_iff_of_bdf [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
      ξ = 0 ∨ (m.stabilityPolyPoly z).eval ξ = 0 := by
  rw [← Polynomial.IsRoot.def,
      toGLM_stabilityMatrix_eigenvalue_iff_of_bdf m z hbdf hz,
      ← stabilityPolyPoly_eval]

/-- §521 Step C.20 — Eval-form contrapositive of the unified BDF iff
(cycle 706 / Step C.19). The GLM stability-matrix charpoly is non-zero
at `ξ` iff `ξ ≠ 0` AND the textbook scalar stability polynomial is
non-zero at `ξ`. This is the De Morgan dual of Step C.19 and the
natural input to the unit-disk root-counting argument that drives
`LMM.toGLM_isAStable_iff` for general BDFs. -/
theorem toGLM_charpoly_eval_ne_zero_iff_of_bdf [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ ≠ 0 ↔
      ξ ≠ 0 ∧ (m.stabilityPolyPoly z).eval ξ ≠ 0 := by
  rw [Ne, toGLM_charpoly_eval_eq_zero_iff_of_bdf m ξ hbdf hz, not_or]

/-- §521 Step D.1 — General (non-BDF) ξ = 0 evaluation of the cycle 698
textbook headline. With `s ≥ 1`, the three `X^s · …` summands collapse,
leaving a closed form for the constant term `D · charpoly(0)` purely
in terms of the `rowFAlphaPoly`, `rowFBetaPoly`, and `PY(0).charpoly`
evaluators at zero. Under BDF this constant collapses further to zero
(cycle 704 / Step C.18) because both `rowFAlphaPoly` and `rowFBetaPoly`
vanish; the general identity isolates exactly which terms could
contribute a non-spurious ξ = 0 root for non-BDF methods. -/
theorem D_mul_toGLM_charpoly_eval_zero_eq
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaPoly m).eval 0
            + ((toGLM_stabilityMatrixPY m 0).charpoly).eval 0
                * (rowFBetaPoly m).eval 0 ) * z := by
  have h := D_mul_toGLM_charpoly_eval_eq m (z := z) (ξ := 0) hz hs
  have h0 : (0 : ℂ) ^ s = 0 := zero_pow hs.ne'
  rw [h0] at h
  linear_combination h

/-- §521 Step D.2 — Alternative proof of Step C.18 (cycle 704)
`toGLM_charpoly_eval_zero_eq_zero_of_bdf` via the new general-form
identity `D_mul_toGLM_charpoly_eval_zero_eq` (Step D.1). Under BDF,
both `rowFAlphaPoly m` and `rowFBetaPoly m` vanish identically (cycle
672 BDF row collapse + the BDF β-coefficients vanishing on
`Fin.castSucc`), so the constant term of `D · charpoly` produced by
Step D.1 collapses to zero. This routes through the general headline
rather than directly through the BDF charpoly headline used by
Step C.18. -/
theorem D_mul_toGLM_charpoly_eval_zero_eq_zero_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  rw [D_mul_toGLM_charpoly_eval_zero_eq m hz hs]
  have hBeta : rowFBetaPoly m = 0 := by
    unfold rowFBetaPoly
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]
    simp
  have hRowF : toGLM_stabilityCharpolyRowF m = 0 :=
    toGLM_stabilityCharpolyRowF_of_bdf m hs hbdf
  have hSplit :=
    toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly m hs
  rw [hRowF, hBeta, mul_zero, add_zero] at hSplit
  have hAlpha : rowFAlphaPoly m = 0 := hSplit.symm
  rw [hAlpha, hBeta]
  simp

/-- §521 Step D.4 — Constant-term evaluation of `rowFBetaPoly`. The
geometric `∑ k : Fin s, C(β (castSucc k)) * X^k` evaluated at `0`
collapses to the single `k = 0` summand because `0^k = 0` for `k ≥ 1`,
isolating the bare `β 0` coefficient. Companion to `rowFBetaPoly_eval_one`
for the unit-disk boundary argument behind `LMM.toGLM_isAStable_iff`. -/
theorem rowFBetaPoly_eval_zero (m : LMM s) (hs : 0 < s) :
    (rowFBetaPoly m).eval 0 =
      ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) := by
  unfold rowFBetaPoly
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.5 — Unit-circle evaluation of `rowFBetaPoly`. All
`1^k = 1` factors collapse, leaving the bare coefficient sum
`∑ k : Fin s, β(castSucc k)`. Companion to `rowFBetaPoly_eval_zero`
for the unit-disk boundary argument behind
`LMM.toGLM_isAStable_iff`. No `s ≥ 1` hypothesis is needed: at `s = 0`
both sides are the empty sum. -/
theorem rowFBetaPoly_eval_one (m : LMM s) :
    (rowFBetaPoly m).eval 1 =
      ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) := by
  unfold rowFBetaPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp

/-- §521 Step D.3 — General (non-BDF) `ξ = 1` evaluation of the cycle 698
textbook headline. The unit-circle boundary point `ξ = 1` is the natural
input to the boundary-locus argument behind `LMM.toGLM_isAStable_iff`:
all `1^k = 1` powers collapse, isolating the `ξ = 1` value of the GLM
charpoly purely in terms of `m.stabilityPolyPoly z` evaluated at `1`
and linear corrections in `rowYQuot`, `rowFAlphaPoly`, and
`rowFBetaPoly`. -/
theorem D_mul_toGLM_charpoly_eval_one_eq
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval 1 +
                ((toGLM_stabilityMatrixPY m 0).charpoly).eval 1 *
                  (rowFBetaPoly m).eval 1 ) * z ) := by
  have h := D_mul_toGLM_charpoly_eval_eq m (z := z) (ξ := 1) hz hs
  have h1 : (1 : ℂ) ^ s = 1 := one_pow s
  rw [h1] at h
  simp only [one_pow, mul_one, one_mul] at h
  linear_combination h

/-- §521 Step D.6 — Constant-term evaluation of `(PY(0)).charpoly`. The
sum `X^s - ∑ l : Fin s, C((-α(castSucc l) : ℂ)) * X^l` evaluated at `0`
collapses: `X^s` becomes `0` (for `s ≥ 1`) and only the `l = 0` summand
of the corrective sum survives, contributing `-(-α 0) = α 0`. -/
theorem toGLM_stabilityMatrixPY_zero_charpoly_eval_zero
    (m : LMM s) (hs : 0 < s) :
    ((toGLM_stabilityMatrixPY m 0).charpoly).eval 0 =
      ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq m]
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum]
  rw [zero_pow hs.ne']
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.7 — Unit-circle evaluation of `(PY(0)).charpoly`. All
`1^k = 1` powers collapse, leaving
`1 - ∑ l : Fin s, -α(castSucc l) = 1 + ∑ l : Fin s, α(castSucc l)`.
Companion to `toGLM_stabilityMatrixPY_zero_charpoly_eval_zero` for the
unit-disk boundary argument behind `LMM.toGLM_isAStable_iff`. No
`s ≥ 1` hypothesis is needed: at `s = 0`, both sides collapse to
`1`. -/
theorem toGLM_stabilityMatrixPY_zero_charpoly_eval_one (m : LMM s) :
    ((toGLM_stabilityMatrixPY m 0).charpoly).eval 1 =
      1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq m]
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum, one_pow]
  have hsum :
      ∑ l : Fin s,
          (Polynomial.C ((-m.α (Fin.castSucc l) : ℝ) : ℂ) *
            (Polynomial.X : Polynomial ℂ) ^ (l : ℕ)).eval 1
        = -∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hsum]; ring

/-- §521 Step D.8 — Fully concrete coefficient-form of the cycle 708
`ξ = 0` evaluation. Substitutes the closed forms
`(PY(0)).charpoly.eval 0 = α 0` (Step D.6) and
`rowFBetaPoly.eval 0 = β 0` (Step D.4) into the cycle 708 identity
`D_mul_toGLM_charpoly_eval_zero_eq`. The constant term of the GLM
stability matrix charpoly (rescaled by `D`) reduces to a closed form
in `(rowFAlphaPoly m).eval 0`, the bare `α 0` and `β 0` coefficients,
and `z`. -/
theorem D_mul_toGLM_charpoly_eval_zero_concrete
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaPoly m).eval 0
            + ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
                * ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) ) * z := by
  rw [D_mul_toGLM_charpoly_eval_zero_eq m hz hs,
      toGLM_stabilityMatrixPY_zero_charpoly_eval_zero m hs,
      rowFBetaPoly_eval_zero m hs]

/-- §521 Step D.9 — Fully concrete coefficient-form of the cycle 710
`ξ = 1` evaluation. Substitutes the closed forms
`(PY(0)).charpoly.eval 1 = 1 + ∑ α(castSucc l)` (Step D.7) and
`rowFBetaPoly.eval 1 = ∑ β(castSucc k)` (Step D.5) into the cycle 710
identity `D_mul_toGLM_charpoly_eval_one_eq`. The unit-circle value of
the GLM stability matrix charpoly (rescaled by `D`) is now expressed
purely in terms of `m.stabilityPolyPoly z` evaluated at `1`, the bare
α/β coefficient sums, and the abstract residuals
`(rowYQuot m).eval 1` and `(rowFAlphaPoly m).eval 1`. -/
theorem D_mul_toGLM_charpoly_eval_one_concrete
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval 1 +
                (1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ)) *
                  (∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ)) ) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_eq m hz hs,
      toGLM_stabilityMatrixPY_zero_charpoly_eval_one m,
      rowFBetaPoly_eval_one m]

/-- §521 Step D.9b — BDF specialisation of `D_mul_toGLM_charpoly_eval_one_concrete`.
Under BDF, every `β (Fin.castSucc k) = 0`, so
`∑ k : Fin s, β(castSucc k) = 0` and the corrective factor
`(1 + ∑ α(castSucc l)) * (∑ β(castSucc k))` vanishes. Provides a
sanity check that the cycle 700 BDF `ξ = 1` identity is consistent
with the new general-form D.9 substitution. -/
theorem D_mul_toGLM_charpoly_eval_one_concrete_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + (rowFAlphaPoly m).eval 1 * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_concrete m hz hs]
  have hBetaSum : ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]; simp
  rw [hBetaSum]
  ring

/-- §521 Step D.10a — Constant-term evaluation of `rowFAlphaPoly`
collapses to the single `l = 0` summand of the residual decomposition.
The cycle 687 `rowFAlphaPoly_eq_residual_sum` expresses
`rowFAlphaPoly m = ∑ l : Fin s, rowFAlphaResidual m l * X^l`; at
`X = 0`, `0^l = 0` for `l ≥ 1`, leaving only the `l = 0` term whose
`X^0` factor is `1`. The `rowFAlphaResidual` evaluation itself
(`Matrix.vecMul` against `charmatrix.adjugate * map C`) is left
abstract — that hard computation is for a future cycle. -/
theorem rowFAlphaPoly_eval_zero_eq_residual_zero
    (m : LMM s) (hs : 0 < s) :
    (rowFAlphaPoly m).eval 0 =
      (rowFAlphaResidual m ⟨0, hs⟩).eval 0 := by
  rw [rowFAlphaPoly_eq_residual_sum]
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.10b — Unit-circle evaluation of `rowFAlphaPoly`. All
`1^l = 1` factors collapse, leaving `∑ l : Fin s, (rowFAlphaResidual m l).eval 1`.
Companion to `rowFAlphaPoly_eval_zero_eq_residual_zero` for the
unit-disk boundary argument. No `s ≥ 1` hypothesis needed. -/
theorem rowFAlphaPoly_eval_one_eq_residual_sum (m : LMM s) :
    (rowFAlphaPoly m).eval 1 =
      ∑ l : Fin s, (rowFAlphaResidual m l).eval 1 := by
  rw [rowFAlphaPoly_eq_residual_sum]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- §521 Step D.11a — Substitute the cycle 716 D.10a evaluation
`(rowFAlphaPoly m).eval 0 = (rowFAlphaResidual m ⟨0, hs⟩).eval 0`
into the cycle 712 D.8 closed form
`D_mul_toGLM_charpoly_eval_zero_concrete`. The `(rowFAlphaPoly m).eval 0`
term collapses to a single residual evaluation; the rest of D.8 stays
unchanged. -/
theorem D_mul_toGLM_charpoly_eval_zero_substituted
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaResidual m ⟨0, hs⟩).eval 0
            + ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
                * ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) ) * z := by
  rw [D_mul_toGLM_charpoly_eval_zero_concrete m hz hs,
      rowFAlphaPoly_eval_zero_eq_residual_zero m hs]

/-- §521 Step D.11b — Substitute the cycle 716 D.10b evaluation
`(rowFAlphaPoly m).eval 1 = ∑ l : Fin s, (rowFAlphaResidual m l).eval 1`
into the cycle 714 D.9 closed form
`D_mul_toGLM_charpoly_eval_one_concrete`. -/
theorem D_mul_toGLM_charpoly_eval_one_substituted
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (∑ l : Fin s, (rowFAlphaResidual m l).eval 1) +
                (1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ)) *
                  (∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ)) ) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_concrete m hz hs,
      rowFAlphaPoly_eval_one_eq_residual_sum m]

/-- §521 Step D.11c — BDF specialisation of D.11b. Under BDF,
`∑ k : Fin s, β(castSucc k) = 0`, so the corrective product term in
D.11b vanishes (same simplification used in D.9b). -/
theorem D_mul_toGLM_charpoly_eval_one_substituted_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + (∑ l : Fin s, (rowFAlphaResidual m l).eval 1) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_substituted m hz hs]
  have hBetaSum : ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]; simp
  rw [hBetaSum]; ring

/-- §521 Step D.12a — Discharge `dif_neg` branch of `rowYQuot.eval 0`. -/
theorem rowYQuot_eval_zero_eq (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 0 =
      (((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k =>
            Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det).eval 0 := by
  unfold rowYQuot
  rw [dif_neg hs.ne']

/-- §521 Step D.12b — Discharge `dif_neg` branch of `rowYQuot.eval 1`. -/
theorem rowYQuot_eval_one_eq (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 1 =
      (((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k =>
            Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det).eval 1 := by
  unfold rowYQuot
  rw [dif_neg hs.ne']

/-- §521 Step D.13 — Cofactor expansion of `rowYQuot` along the `-α`
updated row, recasting the determinant as a sum of `Polynomial.C`-times-
adjugate-entry contributions. -/
theorem rowYQuot_eq_adjugate_sum (m : LMM s) (hs : 0 < s) :
    rowYQuot m =
      ∑ k : Fin s,
        Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
            ⟨s - 1, by omega⟩ := by
  unfold rowYQuot
  rw [dif_neg hs.ne', ← Matrix.cramer_transpose_apply,
      Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_eq_sum]
  simp [Matrix.adjugate_transpose, mul_comm]

/-- §521 Step D.14a — Push `Polynomial.eval ξ` through `rowYQuot_eq_adjugate_sum`
to obtain the cofactor sum at any complex point `ξ`. -/
theorem rowYQuot_eval_eq_sum (m : LMM s) (hs : 0 < s) (ξ : ℂ) :
    (rowYQuot m).eval ξ =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval ξ := by
  rw [rowYQuot_eq_adjugate_sum m hs]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- §521 Step D.14b — Specialisation of `rowYQuot_eval_eq_sum` at `ξ = 0`. -/
theorem rowYQuot_eval_zero_eq_sum (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 0 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 0 :=
  rowYQuot_eval_eq_sum m hs 0

/-- §521 Step D.14c — Specialisation of `rowYQuot_eval_eq_sum` at `ξ = 1`. -/
theorem rowYQuot_eval_one_eq_sum (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 1 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 1 :=
  rowYQuot_eval_eq_sum m hs 1

/-- §521 Step D.14d — BDF wrapper for `rowYQuot_eval_one_eq_sum`. The
`hbdf` hypothesis is unused at this seam; downstream callers see a
BDF-flavoured name. -/
theorem rowYQuot_eval_one_eq_sum_of_bdf
    (m : LMM s) (hs : 0 < s)
    (_hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (rowYQuot m).eval 1 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 1 :=
  rowYQuot_eval_one_eq_sum m hs

/-- §521 Step D.15 — `rowFAlphaResidual m l` expanded as a double sum
over `(k, j) : Fin s × Fin s` of `Polynomial.C`-coefficients times a
single charmatrix adjugate entry.  Mirrors cycle 720's
`rowYQuot_eq_adjugate_sum` for the rowF side.  The leading
`-α(castSucc k)` is inherited from the `rowFAlphaResidual` definition
(the inner two negations on `adjugate` and `PYHF.map C` cancel via
`neg_mul_neg`; the outer `-α` factor remains). -/
private theorem rowFAlphaResidual_eq_double_sum
    (m : LMM s) (l : Fin s) :
    rowFAlphaResidual m l =
      ∑ k : Fin s, ∑ j : Fin s,
        Polynomial.C
            ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
                * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j := by
  unfold rowFAlphaResidual
  rw [Matrix.vecMul_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply]
  simp only [Matrix.neg_apply, Matrix.map_apply, neg_mul_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.C_mul]
  ring

/-- §521 Step D.16a — Push `Polynomial.eval ξ` through D.15's cofactor
expansion of `rowFAlphaResidual`. -/
private theorem rowFAlphaResidual_eval_eq_double_sum
    (m : LMM s) (l : Fin s) (ξ : ℂ) :
    (rowFAlphaResidual m l).eval ξ =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval ξ := by
  rw [rowFAlphaResidual_eq_double_sum m l]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- §521 Step D.16b — `ξ = 0` specialisation of D.16a. -/
theorem rowFAlphaResidual_eval_zero_eq_double_sum
    (m : LMM s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 0 =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 0 :=
  rowFAlphaResidual_eval_eq_double_sum m l 0

/-- §521 Step D.16c — `ξ = 1` specialisation of D.16a. -/
theorem rowFAlphaResidual_eval_one_eq_double_sum
    (m : LMM s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 1 =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 1 :=
  rowFAlphaResidual_eval_eq_double_sum m l 1

/-- §521 Step D.16d — Under BDF, `rowFAlphaResidual m l` evaluates to
zero at `ξ = 1`, because the entire `PYHF` block vanishes (cycle 643's
`toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`). -/
theorem rowFAlphaResidual_eval_one_of_bdf_eq_zero
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (l : Fin s) :
    (rowFAlphaResidual m l).eval 1 = 0 := by
  rw [rowFAlphaResidual_eval_one_eq_double_sum m l]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro j _
  have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
    have := toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m 0 hbdf
    exact congrFun (congrFun this j) l
  rw [hPYHF]
  ring

/-- §521 Step E.1 — Substitute D.16d into D.11c: under BDF, the
`∑ l, (rowFAlphaResidual m l).eval 1` summand collapses to zero,
yielding the cleaner BDF unit-circle identity. -/
theorem D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - (rowYQuot m).eval 1 *
            (z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  rw [D_mul_toGLM_charpoly_eval_one_substituted_of_bdf m hbdf hz hs]
  have hSum : ∑ l : Fin s, (rowFAlphaResidual m l).eval 1 = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact rowFAlphaResidual_eval_one_of_bdf_eq_zero m hbdf l
  rw [hSum]; ring

/-- §521 Step E.2 — Under BDF, β(castSucc l) = 0 for all l : Fin s,
so the bracketed sum in E.1 collapses to a single term. -/
theorem D_mul_toGLM_charpoly_eval_one_reduced_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        - z * ((m.β (Fin.last s) : ℝ) : ℂ) *
            ∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ)
        - (rowYQuot m).eval 1 *
            (z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  rw [D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf m hbdf hz hs]
  have hβSum :
      ∑ l : Fin s,
          ( ((m.β l.castSucc : ℝ) : ℂ)
            - ((m.β (Fin.last s) : ℝ) : ℂ) *
              ((m.α l.castSucc : ℝ) : ℂ) )
        = -((m.β (Fin.last s) : ℝ) : ℂ) *
            ∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hβ : m.β (Fin.castSucc l) = 0 :=
      hbdf _ (Fin.castSucc_lt_last l).ne
    rw [hβ]
    push_cast
    ring
  rw [hβSum]; ring

/-- §521 Step E.3 — Mirror of D.16d at ξ = 0: under BDF, the entire
PYHF block vanishes (cycle 645), so each `rowFAlphaResidual l`
evaluates to zero at any point including ξ = 0. -/
private theorem rowFAlphaResidual_eval_zero_of_bdf_eq_zero
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (l : Fin s) :
    (rowFAlphaResidual m l).eval 0 = 0 := by
  rw [rowFAlphaResidual_eval_zero_eq_double_sum m l]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro j _
  have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
    have := toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m 0 hbdf
    exact congrFun (congrFun this j) l
  rw [hPYHF]; ring

/-- §521 Step E.4 — Under BDF, the rescaled charpoly vanishes at
ξ = 0. Combine D.11a with E.3 (rowFAlphaResidual vanishes at 0)
and the BDF condition `β(castSucc ⟨0,hs⟩) = 0`. -/
theorem D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  rw [D_mul_toGLM_charpoly_eval_zero_substituted m hz hs]
  have h1 : (rowFAlphaResidual m ⟨0, hs⟩).eval 0 = 0 :=
    rowFAlphaResidual_eval_zero_of_bdf_eq_zero m hbdf ⟨0, hs⟩
  have hβ : m.β (Fin.castSucc ⟨0, hs⟩) = 0 :=
    hbdf _ (Fin.castSucc_lt_last _).ne
  rw [h1, hβ]
  push_cast; ring

/-- §521 Step F.1 — The `(s-1, s-1)` adjugate entry of `(PY 0).charmatrix`
is `X^(s-1)`. The matrix `(PY 0).charmatrix.updateRow (s-1) (Pi.single (s-1) 1)`
is upper triangular with diagonal `[X, X, ..., X, 1]`. Each non-last row of
`PY 0` is the pure shift indicator (cycle 643's
`toGLM_stabilityMatrixPY_apply_shift`), so deleting the last column leaves
an upper-triangular minor with `X` on the diagonal.  The updated last row
is `Pi.single ⟨s-1,_⟩ 1`, contributing `1` on the diagonal. -/
private theorem toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last
    (m : LMM s) (hs : 0 < s) :
    (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate
        ⟨s - 1, by omega⟩ ⟨s - 1, by omega⟩
      = (Polynomial.X : Polynomial ℂ) ^ (s - 1) := by
  rw [Matrix.adjugate_apply]
  set N := (toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
              ⟨s - 1, by omega⟩
              (Pi.single (⟨s - 1, by omega⟩ : Fin s) (1 : Polynomial ℂ))
      with hN_def
  -- Step 1: N is upper triangular.
  have htri : N.BlockTriangular id := by
    intro j l hlt
    have hlt' : (l : ℕ) < (j : ℕ) := hlt
    by_cases hj : j = ⟨s - 1, by omega⟩
    · rw [hj, hN_def, Matrix.updateRow_self]
      apply Pi.single_eq_of_ne
      intro heq
      have hv : (l : ℕ) = s - 1 := congrArg Fin.val heq
      omega
    · have hj_lt : (j : ℕ) + 1 ≠ s := by
        intro heq
        apply hj
        apply Fin.ext
        show (j : ℕ) = s - 1
        omega
      have hN_jl : N j l = (toGLM_stabilityMatrixPY m 0).charmatrix j l := by
        simp [hN_def, Matrix.updateRow_ne hj]
      rw [hN_jl, Matrix.charmatrix_apply]
      rw [Matrix.diagonal_apply_ne _ (fun hjl => by
          have hv : (j : ℕ) = (l : ℕ) := congrArg Fin.val hjl
          omega)]
      rw [toGLM_stabilityMatrixPY_apply_shift m 0 j hj_lt l]
      rw [if_neg (by omega : ¬ (l : ℕ) = (j : ℕ) + 1)]
      simp
  -- Step 2: det N = ∏ i, N i i.
  rw [Matrix.det_of_upperTriangular htri]
  -- Step 3: Diagonal product = X^(s-1).
  have h_last : N ⟨s - 1, by omega⟩ ⟨s - 1, by omega⟩ = (1 : Polynomial ℂ) := by
    rw [hN_def, Matrix.updateRow_self]
    exact Pi.single_eq_same _ _
  have h_other : ∀ i : Fin s, i ≠ ⟨s - 1, by omega⟩ →
      N i i = (Polynomial.X : Polynomial ℂ) := by
    intro i hi
    have hN_ii : N i i = (toGLM_stabilityMatrixPY m 0).charmatrix i i := by
      simp [hN_def, Matrix.updateRow_ne hi]
    rw [hN_ii, Matrix.charmatrix_apply, Matrix.diagonal_apply_eq]
    have hi_lt : (i : ℕ) + 1 ≠ s := by
      intro heq
      apply hi
      apply Fin.ext
      show (i : ℕ) = s - 1
      omega
    rw [toGLM_stabilityMatrixPY_apply_shift m 0 i hi_lt i]
    rw [if_neg (by omega : ¬ (i : ℕ) = (i : ℕ) + 1)]
    simp
  rw [← Finset.mul_prod_erase Finset.univ (fun i => N i i)
        (Finset.mem_univ ⟨s - 1, by omega⟩)]
  rw [h_last, one_mul]
  rw [Finset.prod_congr rfl (fun i hi => h_other i (Finset.ne_of_mem_erase hi))]
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]

/-- §521 Step H.1 — Last-column adjugate entries of `(PY 0).charmatrix`
form the geometric ladder `X^k`. Generalises F.1 (the `k = s-1` diagonal
case) to every row index `k`.

The proof goes through the row equation
`A · (adjugate A) = (det A) • I` at off-diagonal entries `(j, ⟨s-1,_⟩)`
for `j < s - 1`. Each such equation collapses to
`X · adj(j, last) - adj(j+1, last) = 0`, giving the recurrence
`adj(j+1, last) = X · adj(j, last)`. Iterating from `k` upward to `s-1`
together with F.1 as the upper anchor and cancelling `X^(s-1-k)` (a
non-zero-divisor in `Polynomial ℂ`) gives `adj(k, last) = X^k`. -/
private theorem toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col
    (m : LMM s) (hs : 0 < s) (k : Fin s) :
    (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k ⟨s - 1, by omega⟩
      = (Polynomial.X : Polynomial ℂ) ^ (k : ℕ) := by
  set A := (toGLM_stabilityMatrixPY m 0).charmatrix with hA_def
  -- Step 1: recurrence adj(j+1, last) = X * adj(j, last) for j+1 < s.
  have hRec : ∀ (j : ℕ) (hj1 : j + 1 < s),
      A.adjugate ⟨j + 1, hj1⟩ ⟨s - 1, by omega⟩
        = Polynomial.X * A.adjugate ⟨j, by omega⟩ ⟨s - 1, by omega⟩ := by
    intro j hj1
    have hj : j < s := by omega
    have hjne_last : (⟨j, hj⟩ : Fin s) ≠ ⟨s - 1, by omega⟩ := by
      intro h
      have : j = s - 1 := congrArg Fin.val h
      omega
    have hjnotlast : (⟨j, hj⟩ : Fin s).val + 1 ≠ s := by
      show j + 1 ≠ s; omega
    -- mul_adjugate at entry (⟨j, hj⟩, ⟨s-1,_⟩)
    have hMul := Matrix.mul_adjugate A
    have h := congrFun (congrFun hMul ⟨j, hj⟩) ⟨s - 1, by omega⟩
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne hjne_last,
        smul_eq_mul, mul_zero] at h
    -- Compute charmatrix entries on row ⟨j, hj⟩.
    have hCharm : ∀ k' : Fin s, A ⟨j, hj⟩ k' =
        (if k' = ⟨j, hj⟩ then Polynomial.X else 0) -
          (if (k' : ℕ) = j + 1 then 1 else 0) := by
      intro k'
      rw [hA_def, Matrix.charmatrix_apply,
          toGLM_stabilityMatrixPY_apply_shift m 0 ⟨j, hj⟩ hjnotlast k']
      by_cases hkj : k' = ⟨j, hj⟩
      · subst hkj
        have hk_ne : ((⟨j, hj⟩ : Fin s) : ℕ) ≠ j + 1 := by show j ≠ j + 1; omega
        rw [Matrix.diagonal_apply_eq, if_neg hk_ne, if_pos rfl, if_neg hk_ne]
        simp
      · rw [Matrix.diagonal_apply_ne _ (Ne.symm hkj), if_neg hkj]
        by_cases hk1 : (k' : ℕ) = j + 1
        · rw [if_pos hk1, if_pos hk1, Polynomial.C_1]
        · rw [if_neg hk1, if_neg hk1, Polynomial.C_0]
    -- Substitute into h.
    rw [show (∑ k' : Fin s, A ⟨j, hj⟩ k' * A.adjugate k' ⟨s - 1, by omega⟩) =
            ∑ k' : Fin s,
              ((if k' = ⟨j, hj⟩ then Polynomial.X else 0) -
                (if (k' : ℕ) = j + 1 then 1 else 0))
                * A.adjugate k' ⟨s - 1, by omega⟩ from
          Finset.sum_congr rfl (fun k' _ => by rw [hCharm k'])] at h
    rw [show
          (∑ k' : Fin s,
              ((if k' = ⟨j, hj⟩ then Polynomial.X else 0) -
                (if (k' : ℕ) = j + 1 then 1 else 0))
                * A.adjugate k' ⟨s - 1, by omega⟩) =
          (∑ k' : Fin s,
              (if k' = ⟨j, hj⟩ then Polynomial.X else 0)
                * A.adjugate k' ⟨s - 1, by omega⟩)
            - (∑ k' : Fin s,
                (if (k' : ℕ) = j + 1 then 1 else 0)
                  * A.adjugate k' ⟨s - 1, by omega⟩) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          ring] at h
    rw [show
          (∑ k' : Fin s,
              (if k' = ⟨j, hj⟩ then Polynomial.X else 0)
                * A.adjugate k' ⟨s - 1, by omega⟩)
            = Polynomial.X * A.adjugate ⟨j, hj⟩ ⟨s - 1, by omega⟩ from by
          rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin s)]
          · rw [if_pos rfl]
          · intro k' _ hk'; rw [if_neg hk', zero_mul]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem] at h
    rw [show
          (∑ k' : Fin s,
              (if (k' : ℕ) = j + 1 then 1 else 0)
                * A.adjugate k' ⟨s - 1, by omega⟩)
            = A.adjugate ⟨j + 1, hj1⟩ ⟨s - 1, by omega⟩ from by
          rw [Finset.sum_eq_single (⟨j + 1, hj1⟩ : Fin s)]
          · rw [if_pos rfl, one_mul]
          · intro k' _ hk'
            have hne : (k' : ℕ) ≠ j + 1 := by
              intro heq; apply hk'; apply Fin.ext; exact heq
            rw [if_neg hne, zero_mul]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem] at h
    -- h : Polynomial.X * adj(⟨j,_⟩) - adj(⟨j+1,_⟩) = 0
    linear_combination -h
  -- Step 2: telescope X^n · adj(j, last) = adj(j+n, last) for j+n < s.
  have hTele : ∀ (n j : ℕ) (hjn : j + n < s),
      Polynomial.X ^ n * A.adjugate ⟨j, by omega⟩ ⟨s - 1, by omega⟩
        = A.adjugate ⟨j + n, hjn⟩ ⟨s - 1, by omega⟩ := by
    intro n
    induction n with
    | zero =>
      intro j hjn
      simp [pow_zero, one_mul]
    | succ n ih =>
      intro j hjn
      have hjn' : j + n < s := by omega
      have hjnsucc : (j + n) + 1 < s := by omega
      have ihn := ih j hjn'
      have hr := hRec (j + n) hjnsucc
      calc Polynomial.X ^ (n + 1)
              * A.adjugate ⟨j, by omega⟩ ⟨s - 1, by omega⟩
          = Polynomial.X *
              (Polynomial.X ^ n * A.adjugate ⟨j, by omega⟩ ⟨s - 1, by omega⟩) := by
            rw [pow_succ]; ring
        _ = Polynomial.X * A.adjugate ⟨j + n, hjn'⟩ ⟨s - 1, by omega⟩ := by rw [ihn]
        _ = A.adjugate ⟨(j + n) + 1, hjnsucc⟩ ⟨s - 1, by omega⟩ := hr.symm
        _ = A.adjugate ⟨j + (n + 1), hjn⟩ ⟨s - 1, by omega⟩ := by
              have hidx : (⟨(j + n) + 1, hjnsucc⟩ : Fin s)
                            = ⟨j + (n + 1), hjn⟩ := by
                apply Fin.ext
                show (j + n) + 1 = j + (n + 1)
                omega
              rw [hidx]
  -- Step 3: instantiate with j = k, n = s - 1 - k.
  have hKlt : (k : ℕ) < s := k.isLt
  have hKle : (k : ℕ) ≤ s - 1 := by omega
  have hSum : (k : ℕ) + (s - 1 - (k : ℕ)) = s - 1 := by omega
  have hTeleK := hTele (s - 1 - (k : ℕ)) (k : ℕ) (by omega)
  rw [show (⟨(k : ℕ) + (s - 1 - (k : ℕ)), by omega⟩ : Fin s)
        = ⟨s - 1, by omega⟩ from Fin.ext hSum] at hTeleK
  rw [show (⟨(k : ℕ), by omega⟩ : Fin s) = k from Fin.ext rfl] at hTeleK
  rw [hA_def, toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last m hs] at hTeleK
  -- hTeleK : X^(s-1-k) * adj(k, last) = X^(s-1)
  -- Cancel X^(s-1-k) ≠ 0 in Polynomial ℂ.
  have hPow : (Polynomial.X : Polynomial ℂ) ^ (s - 1)
        = (Polynomial.X : Polynomial ℂ) ^ (s - 1 - (k : ℕ))
            * (Polynomial.X : Polynomial ℂ) ^ (k : ℕ) := by
    rw [← pow_add]; congr 1; omega
  rw [hPow] at hTeleK
  have hX_pow_ne : (Polynomial.X : Polynomial ℂ) ^ (s - 1 - (k : ℕ)) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  exact mul_left_cancel₀ hX_pow_ne hTeleK

/-- §521 Step F.2 — Closed form for `rowYQuot m`: a BDF-independent
polynomial identity reading the `(s-1, s-1)` entry of the
`Matrix.mul_adjugate` identity for `(PY 0).charmatrix`, then substituting
F.1 (adjugate diagonal = X^(s-1)), cycle 720's
`rowYQuot_eq_adjugate_sum`, and cycle 692's `(PY 0).charpoly` closed
form (at `z = 0` the resolvent denominator collapses). -/
theorem rowYQuot_eq_neg_alpha_sum (m : LMM s) (hs : 0 < s) :
    rowYQuot m
      = - ∑ l : Fin s,
            Polynomial.C ((m.α (Fin.castSucc l) : ℝ) : ℂ)
              * (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) := by
  have hz_one : (1 : ℂ) - (0 : ℂ) * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0 := by simp
  have h1 : (1 : ℂ) - (0 : ℂ) * ((m.β (Fin.last s) : ℝ) : ℂ) = 1 := by ring
  -- Step 1: (PY 0).charpoly closed form (cycle 692 at z=0).
  have h_charpoly :
      (toGLM_stabilityMatrixPY m 0).charpoly =
        (Polynomial.X : Polynomial ℂ) ^ s -
          ∑ l : Fin s,
            Polynomial.C ((-m.α (Fin.castSucc l) : ℝ) : ℂ) *
              (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) := by
    rw [toGLM_stabilityMatrixPY_charpoly m 0 hz_one]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h1, div_one]
  -- Step 2: (s-1, s-1) entry of charmatrix * adjugate = charpoly.
  have hMul := Matrix.mul_adjugate (toGLM_stabilityMatrixPY m 0).charmatrix
  have hEntry :
      ∑ k : Fin s,
        (toGLM_stabilityMatrixPY m 0).charmatrix
            ⟨s - 1, by omega⟩ k *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
            ⟨s - 1, by omega⟩ =
        (toGLM_stabilityMatrixPY m 0).charpoly := by
    have h := congrFun (congrFun hMul ⟨s - 1, by omega⟩) ⟨s - 1, by omega⟩
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq,
               smul_eq_mul, mul_one] at h
    exact h
  -- Step 3: charmatrix entry at last row.
  have hjeq : ((⟨s - 1, by omega⟩ : Fin s) : ℕ) + 1 = s := by
    show s - 1 + 1 = s; omega
  have hCharm : ∀ k : Fin s,
      (toGLM_stabilityMatrixPY m 0).charmatrix ⟨s - 1, by omega⟩ k =
        (Matrix.diagonal (fun _ : Fin s => (Polynomial.X : Polynomial ℂ)))
            ⟨s - 1, by omega⟩ k -
          Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) := by
    intro k
    rw [Matrix.charmatrix_apply]
    congr 1
    rw [toGLM_stabilityMatrixPY_apply_last m 0 hz_one ⟨s - 1, by omega⟩ hjeq k]
    rw [h1, div_one]
  -- Step 4: split the sum.
  have hSplit :
      ∑ k : Fin s,
        (toGLM_stabilityMatrixPY m 0).charmatrix ⟨s - 1, by omega⟩ k *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
            ⟨s - 1, by omega⟩ =
        Polynomial.X *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate
            ⟨s - 1, by omega⟩ ⟨s - 1, by omega⟩ -
        ∑ k : Fin s,
          Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
            (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩ := by
    rw [show (∑ k : Fin s,
            (toGLM_stabilityMatrixPY m 0).charmatrix ⟨s - 1, by omega⟩ k *
              (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
                ⟨s - 1, by omega⟩) =
          ∑ k : Fin s,
            ((Matrix.diagonal (fun _ : Fin s => (Polynomial.X : Polynomial ℂ)))
                ⟨s - 1, by omega⟩ k *
                (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
                  ⟨s - 1, by omega⟩ -
              Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
                (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
                  ⟨s - 1, by omega⟩) from
        Finset.sum_congr rfl (fun k _ => by rw [hCharm k]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single (⟨s - 1, by omega⟩ : Fin s)]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hk)]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- Step 5: substitute F.1 (adjugate diagonal = X^(s-1)).
  rw [toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last m hs] at hSplit
  -- Step 6: substitute rowYQuot_eq_adjugate_sum.
  rw [show ∑ k : Fin s,
        Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
            ⟨s - 1, by omega⟩ = rowYQuot m from
      (rowYQuot_eq_adjugate_sum m hs).symm] at hSplit
  -- hSplit: ∑ charm * adj = X * X^(s-1) - rowYQuot m
  rw [hSplit] at hEntry
  -- hEntry: X * X^(s-1) - rowYQuot m = charpoly
  rw [h_charpoly] at hEntry
  -- Collapse X * X^(s-1) into X^s.
  have hX_pow : Polynomial.X * (Polynomial.X : Polynomial ℂ) ^ (s - 1) =
      (Polynomial.X : Polynomial ℂ) ^ s := by
    rw [← pow_succ', show s - 1 + 1 = s from by omega]
  rw [hX_pow] at hEntry
  -- hEntry: X^s - rowYQuot m = X^s - ∑ C(-α) * X^l
  -- Goal: rowYQuot m = -∑ C(α) * X^l
  have h_sum_eq : ∑ l : Fin s,
      Polynomial.C ((-m.α (Fin.castSucc l) : ℝ) : ℂ) *
        (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) =
      -∑ l : Fin s,
        Polynomial.C ((m.α (Fin.castSucc l) : ℝ) : ℂ) *
          (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    push_cast
    rw [Polynomial.C_neg]
    ring
  linear_combination -hEntry + h_sum_eq

/-- §521 Step F.3 — Evaluation of `rowYQuot` at `ξ = 1`.
Direct consequence of F.2 by `Polynomial.eval` distribution. -/
theorem rowYQuot_eval_one (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 1
      = - ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [rowYQuot_eq_neg_alpha_sum m hs]
  rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, mul_one]

/-- §521 Step F.3 — Evaluation of `rowYQuot` at `ξ = 0`.
Only the `l = 0` summand survives `(0 : ℂ) ^ l`. -/
theorem rowYQuot_eval_zero (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 0
      = - ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) := by
  rw [rowYQuot_eq_neg_alpha_sum m hs]
  rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
  congr 1
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
    show ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) *
         (0 : ℂ) ^ ((⟨0, hs⟩ : Fin s) : ℕ) = _
    rw [show ((⟨0, hs⟩ : Fin s) : ℕ) = 0 from rfl, pow_zero, mul_one]
  · intro l _ hl
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
    have hlne : (l : ℕ) ≠ 0 := by
      intro h
      apply hl
      apply Fin.ext
      exact h
    rw [zero_pow hlne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step H.2 — Closed form for `rowFAlphaResidual.eval 1` for
**general** (non-BDF) LMMs.

Starting from D.16c (`rowFAlphaResidual_eval_one_eq_double_sum`), the
inner `j`-sum collapses to a single term at `j = ⟨s-1, _⟩`: at every
other index, the PYHF block at `z = 0` returns `0` (its definition
gates on `(j : ℕ) + 1 = s`). At `j = ⟨s-1, _⟩`, the PYHF entry
collapses to `β(castSucc l)` (the `z`-correction vanishes at `z = 0`).
The surviving last-column adjugate factor is then closed by H.1
(`toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col`):
`(adj k ⟨s-1,_⟩).eval 1 = (X^k).eval 1 = 1`. The result is a clean
product of two scalar sums. -/
theorem rowFAlphaResidual_eval_one_closed_form
    (m : LMM s) (hs : 0 < s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 1
      = -((m.β (Fin.castSucc l) : ℝ) : ℂ)
          * ∑ k : Fin s, ((m.α (Fin.castSucc k) : ℝ) : ℂ) := by
  rw [rowFAlphaResidual_eval_one_eq_double_sum m l]
  -- Collapse inner j-sum to the single surviving j = ⟨s-1, _⟩ term.
  have hInner : ∀ k : Fin s,
      ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 1
        = -((m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
    intro k
    rw [Finset.sum_eq_single (⟨s - 1, by omega⟩ : Fin s)]
    · -- Surviving j = ⟨s-1, _⟩ term.
      have hPYHF :
          (toGLM_stabilityMatrixPYHF m 0) ⟨s - 1, by omega⟩ l
            = ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_pos (show ((⟨s - 1, by omega⟩ : Fin s) : ℕ) + 1 = s by
                      show s - 1 + 1 = s; omega)]
        ring
      have hAdj :
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 1 = 1 := by
        rw [toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col m hs k,
            Polynomial.eval_pow, Polynomial.eval_X, one_pow]
      rw [hPYHF, hAdj]
      push_cast
      ring
    · -- j ≠ ⟨s-1, _⟩: PYHF j l = 0.
      intro j _ hj
      have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_neg]
        intro heq
        apply hj
        apply Fin.ext
        show (j : ℕ) = s - 1
        omega
      rw [hPYHF]
      ring
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [show
        (∑ k : Fin s, ∑ j : Fin s,
            ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
                * ((toGLM_stabilityMatrixPYHF m 0) j l) )
              * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 1)
        = ∑ k : Fin s,
            (-((m.α (Fin.castSucc k) : ℝ) : ℂ)
              * ((m.β (Fin.castSucc l) : ℝ) : ℂ)) from
        Finset.sum_congr rfl (fun k _ => hInner k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- §521 Step F.4 — BDF unit-circle scalar identity (headline). Combines
E.2 (`D_mul_toGLM_charpoly_eval_one_reduced_of_bdf`) with F.3
(`rowYQuot_eval_one`): the abstract `(rowYQuot m).eval 1` term cancels the
`z β_last · ∑ α(castSucc l)` correction, leaving only the pure
`(stabilityPolyPoly z).eval 1`. -/
theorem D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1
      = (m.stabilityPolyPoly z).eval 1 := by
  rw [D_mul_toGLM_charpoly_eval_one_reduced_of_bdf m hbdf hz hs]
  rw [rowYQuot_eval_one m hs]
  ring

/-- §521 Step G.1 — General (non-BDF) unit-circle identity.
Substitutes F.3 (`rowYQuot_eval_one`) into D.11b
(`D_mul_toGLM_charpoly_eval_one_substituted`) and collects the
explicit `(rowYQuot m).eval 1 = -∑ α(castSucc l)` cancellation.
After cancellation the residual is a `rowFAlphaResidual` sum plus a
single cross product `∑β(castSucc) · ∑α(castSucc)`. This is the
non-BDF analogue of F.4; the BDF specialisation
`D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly_of_bdf` recovers
F.4 by zeroing both correction summands. -/
theorem D_mul_toGLM_charpoly_eval_one_general
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        - z * (∑ l : Fin s, (rowFAlphaResidual m l).eval 1)
        - z * (∑ l : Fin s, ((m.β l.castSucc : ℝ) : ℂ))
            * (∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ)) := by
  rw [D_mul_toGLM_charpoly_eval_one_substituted m hz hs]
  rw [rowYQuot_eval_one m hs]
  have hsum_split : ∑ l : Fin s,
        ( ((m.β l.castSucc : ℝ) : ℂ)
            - ((m.β (Fin.last s) : ℝ) : ℂ) *
              ((m.α l.castSucc : ℝ) : ℂ) ) =
      (∑ l : Fin s, ((m.β l.castSucc : ℝ) : ℂ))
        - ((m.β (Fin.last s) : ℝ) : ℂ) *
            (∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum_split]
  ring

/-- §521 Step G.2 — BDF specialisation of G.1, recovering F.4 via
the alternative D.11b route. Both correction terms in G.1 vanish
under BDF: the `rowFAlphaResidual` sum by D.16d, and the
`∑β castSucc` factor by direct BDF castSucc-vanishing. -/
theorem D_mul_toGLM_charpoly_eval_one_general_of_bdf
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1 := by
  rw [D_mul_toGLM_charpoly_eval_one_general m hz hs]
  have h1 : ∑ l : Fin s, (rowFAlphaResidual m l).eval 1 = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact rowFAlphaResidual_eval_one_of_bdf_eq_zero m hbdf l
  have h2 : ∑ l : Fin s, ((m.β l.castSucc : ℝ) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hβ := hbdf _ (Fin.castSucc_lt_last l).ne
    rw [hβ]; simp
  rw [h1, h2]; ring

/-- §521 Step H.3 — Headline general (non-BDF) unit-circle identity.
Substitutes H.2 (`rowFAlphaResidual_eval_one_closed_form`) into G.1
(`D_mul_toGLM_charpoly_eval_one_general`). The `rowFAlphaResidual` sum
reduces to `-(∑ β castSucc) · (∑ α castSucc)`, which exactly cancels
the `∑β · ∑α` cross-product correction in G.1. The BDF hypothesis
drops out entirely: this is the same closed identity that
`D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly_of_bdf` (F.4)
proved under BDF, but here at full generality. -/
theorem D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1
      = (m.stabilityPolyPoly z).eval 1 := by
  rw [D_mul_toGLM_charpoly_eval_one_general m hz hs]
  have hRes :
      ∑ l : Fin s, (rowFAlphaResidual m l).eval 1
        = -(∑ l : Fin s, ((m.β (Fin.castSucc l) : ℝ) : ℂ))
            * (∑ k : Fin s, ((m.α (Fin.castSucc k) : ℝ) : ℂ)) := by
    rw [show (∑ l : Fin s, (rowFAlphaResidual m l).eval 1)
            = ∑ l : Fin s,
                (-((m.β (Fin.castSucc l) : ℝ) : ℂ)
                  * ∑ k : Fin s, ((m.α (Fin.castSucc k) : ℝ) : ℂ)) from
          Finset.sum_congr rfl
            (fun l _ => rowFAlphaResidual_eval_one_closed_form m hs l)]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  rw [hRes]
  ring

/-- §521 Step G.3 — General (non-BDF) ξ = 0 mirror of G.1.
This is the public surface of D.11a renamed to match the
G-ladder naming. -/
theorem D_mul_toGLM_charpoly_eval_zero_general
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ((rowFAlphaResidual m ⟨0, hs⟩).eval 0
            + ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
                * ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)) * z :=
  D_mul_toGLM_charpoly_eval_zero_substituted m hz hs

/-- §521 Step I.2 — Closed form for `rowFAlphaResidual.eval 0` for
**general** (non-BDF) LMMs. Inner `j`-sum collapses identically to H.2
(PYHF gates on `j = ⟨s-1, _⟩`). Outer `k`-sum further collapses
because `(X^k).eval 0` vanishes unless `k.val = 0`. -/
theorem rowFAlphaResidual_eval_zero_closed_form
    (m : LMM s) (hs : 0 < s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 0
      = -((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
          * ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [rowFAlphaResidual_eval_zero_eq_double_sum m l]
  -- Inner j-sum collapses to j = ⟨s-1, _⟩, identical to H.2.
  have hInner : ∀ k : Fin s,
      ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 0
        = -((m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((m.β (Fin.castSucc l) : ℝ) : ℂ)
            * ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).eval 0 := by
    intro k
    rw [Finset.sum_eq_single (⟨s - 1, by omega⟩ : Fin s)]
    · -- Surviving j = ⟨s-1, _⟩ term.
      have hPYHF :
          (toGLM_stabilityMatrixPYHF m 0) ⟨s - 1, by omega⟩ l
            = ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_pos (show ((⟨s - 1, by omega⟩ : Fin s) : ℕ) + 1 = s by
                      show s - 1 + 1 = s; omega)]
        ring
      have hAdj :
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩)
            = (Polynomial.X : Polynomial ℂ) ^ (k : ℕ) :=
        toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col m hs k
      rw [hPYHF, hAdj]
      push_cast
      ring
    · intro j _ hj
      have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_neg]
        intro heq
        apply hj
        apply Fin.ext
        show (j : ℕ) = s - 1
        omega
      rw [hPYHF]
      ring
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [show
        (∑ k : Fin s, ∑ j : Fin s,
            ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
                * ((toGLM_stabilityMatrixPYHF m 0) j l) )
              * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 0)
        = ∑ k : Fin s,
            -((m.α (Fin.castSucc k) : ℝ) : ℂ)
              * ((m.β (Fin.castSucc l) : ℝ) : ℂ)
              * ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).eval 0 from
        Finset.sum_congr rfl (fun k _ => hInner k)]
  -- Outer k-sum: (X^k).eval 0 = if k.val = 0 then 1 else 0.
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · -- Surviving k = ⟨0, hs⟩ term: (X^0).eval 0 = 1.
    simp
  · -- k ≠ ⟨0, hs⟩: (k : ℕ) ≠ 0, so 0^k = 0.
    intro k _ hk
    have hpos : (k : ℕ) ≠ 0 := by
      intro h0
      apply hk
      apply Fin.ext
      exact h0
    rw [Polynomial.eval_pow, Polynomial.eval_X, zero_pow hpos]
    ring
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- §521 Step I.3 — Headline general (non-BDF) ξ = 0 identity. Substitutes
I.2 (`rowFAlphaResidual_eval_zero_closed_form`) at `l = ⟨0, hs⟩` into G.3
(`D_mul_toGLM_charpoly_eval_zero_general`). The closed form
`(rowFAlphaResidual m ⟨0,_⟩).eval 0 = -α₀ · β₀` exactly cancels the
`α₀ · β₀` correction, leaving zero. The BDF hypothesis drops out
entirely: this is the general analogue of E.4
(`D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf`). -/
theorem D_mul_toGLM_charpoly_eval_zero_eq_zero
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  rw [D_mul_toGLM_charpoly_eval_zero_general m hz hs,
      rowFAlphaResidual_eval_zero_closed_form m hs ⟨0, hs⟩]
  ring

/-- §521 Step J.1 — Generic-ξ closed form for `rowFAlphaResidual.eval ξ`.
Generalises H.2 (`rowFAlphaResidual_eval_one_closed_form`) and I.2
(`rowFAlphaResidual_eval_zero_closed_form`) to arbitrary `ξ : ℂ`. The
last-column adjugate factor `(X^k).eval ξ` expands to `ξ^(k:ℕ)`,
leaving the outer k-sum as a polynomial in ξ. -/
theorem rowFAlphaResidual_eval_closed_form
    (m : LMM s) (hs : 0 < s) (l : Fin s) (ξ : ℂ) :
    (rowFAlphaResidual m l).eval ξ
      = -((m.β (Fin.castSucc l) : ℝ) : ℂ)
          * ∑ k : Fin s,
              ((m.α (Fin.castSucc k) : ℝ) : ℂ) * ξ ^ (k : ℕ) := by
  rw [rowFAlphaResidual_eval_eq_double_sum m l ξ]
  -- Collapse inner j-sum to the single surviving j = ⟨s-1, _⟩ term.
  have hInner : ∀ k : Fin s,
      ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval ξ
        = -((m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (k : ℕ) := by
    intro k
    rw [Finset.sum_eq_single (⟨s - 1, by omega⟩ : Fin s)]
    · -- Surviving j = ⟨s-1, _⟩ term.
      have hPYHF :
          (toGLM_stabilityMatrixPYHF m 0) ⟨s - 1, by omega⟩ l
            = ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_pos (show ((⟨s - 1, by omega⟩ : Fin s) : ℕ) + 1 = s by
                      show s - 1 + 1 = s; omega)]
        ring
      have hAdj :
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval ξ = ξ ^ (k : ℕ) := by
        rw [toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col m hs k,
            Polynomial.eval_pow, Polynomial.eval_X]
      rw [hPYHF, hAdj]
      push_cast
      ring
    · -- j ≠ ⟨s-1, _⟩: PYHF j l = 0.
      intro j _ hj
      have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
        unfold toGLM_stabilityMatrixPYHF
        rw [if_neg]
        intro heq
        apply hj
        apply Fin.ext
        show (j : ℕ) = s - 1
        omega
      rw [hPYHF]
      ring
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [show
        (∑ k : Fin s, ∑ j : Fin s,
            ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
                * ((toGLM_stabilityMatrixPYHF m 0) j l) )
              * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval ξ)
        = ∑ k : Fin s,
            (-((m.α (Fin.castSucc k) : ℝ) : ℂ)
              * ((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (k : ℕ)) from
        Finset.sum_congr rfl (fun k _ => hInner k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- §521 Step J.2 — Generic-ξ unfolding of `rowFAlphaPoly.eval ξ` as
the position-graded sum of `rowFAlphaResidual` evaluations. Generalises
`rowFAlphaPoly_eval_one_eq_residual_sum` (D.10b) to arbitrary `ξ : ℂ`
by retaining the `ξ^(l:ℕ)` factor that `one_pow` collapses at ξ = 1. -/
theorem rowFAlphaPoly_eval_general (m : LMM s) (ξ : ℂ) :
    (rowFAlphaPoly m).eval ξ
      = ∑ l : Fin s, (rowFAlphaResidual m l).eval ξ * ξ ^ (l : ℕ) := by
  rw [rowFAlphaPoly_eq_residual_sum]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- §521 Step J.3 — Generic-ξ evaluation of `rowYQuot`. Generalises
F.3 at ξ = 1 (`rowYQuot_eval_one`) and ξ = 0 (`rowYQuot_eval_zero`)
by retaining the position-graded `ξ^(l:ℕ)` factor that `one_pow` /
`zero_pow` collapse at the endpoints. -/
theorem rowYQuot_eval_general (m : LMM s) (hs : 0 < s) (ξ : ℂ) :
    (rowYQuot m).eval ξ
      = - ∑ l : Fin s,
            ((m.α (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ) := by
  rw [rowYQuot_eq_neg_alpha_sum m hs]
  rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]

/-- §521 Step J.4 helper — Generic-ξ unfolding of `rowFBetaPoly.eval ξ`.
Generalises `rowFBetaPoly_eval_one` (D.5) to arbitrary `ξ : ℂ`. -/
private theorem rowFBetaPoly_eval_general (m : LMM s) (ξ : ℂ) :
    (rowFBetaPoly m).eval ξ
      = ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) * ξ ^ (k : ℕ) := by
  unfold rowFBetaPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]

/-- §521 Step J.4 helper — Generic-ξ unfolding of
`(toGLM_stabilityMatrixPY m 0).charpoly.eval ξ`. Routine eval of the
C.13a closed form `X^s - ∑ C(-α l.castSucc) * X^l`. -/
private theorem toGLM_stabilityMatrixPY_zero_charpoly_eval_general
    (m : LMM s) (ξ : ℂ) :
    ((toGLM_stabilityMatrixPY m 0).charpoly).eval ξ
      = ξ^s + ∑ l : Fin s,
                ((m.α (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ) := by
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq]
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum]
  have hSum : ∑ l : Fin s,
        (Polynomial.C ((-m.α (Fin.castSucc l) : ℝ) : ℂ) *
          Polynomial.X ^ (l : ℕ)).eval ξ
      = -∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C]
  rw [hSum]; ring

/-- §521 Step J.4 — Generic-ξ headline (general, non-BDF) lifting H.3
and I.3 to arbitrary `ξ : ℂ`. The §521 LMM-side iff bridge
`LMM.toGLM_isAStable_iff` reduces to a unit-disk root-counting argument
over this identity. Substituting J.1, J.2, J.3 plus the
`rowFBetaPoly` and `(PY 0).charpoly` evaluations into C.16
collapses the residual algebra to a single `ring` close after
extracting the two scalar sums `A := ∑ α_k ξ^k` and `B := ∑ β_l ξ^l`. -/
theorem D_mul_toGLM_charpoly_eval_general
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval ξ
      = ξ^s * (m.stabilityPolyPoly z).eval ξ := by
  rw [D_mul_toGLM_charpoly_eval_eq m ξ hz hs]
  rw [rowYQuot_eval_general m hs ξ]
  rw [rowFAlphaPoly_eval_general m ξ]
  rw [rowFBetaPoly_eval_general m ξ]
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eval_general m ξ]
  -- Rewrite each rowFAlphaResidual.eval ξ via J.1.
  rw [show (∑ l : Fin s, (rowFAlphaResidual m l).eval ξ * ξ ^ (l : ℕ))
        = ∑ l : Fin s,
            (-((m.β (Fin.castSucc l) : ℝ) : ℂ)
              * ∑ k : Fin s,
                  ((m.α (Fin.castSucc k) : ℝ) : ℂ) * ξ ^ (k : ℕ))
              * ξ ^ (l : ℕ) from
        Finset.sum_congr rfl (fun l _ => by
          rw [rowFAlphaResidual_eval_closed_form m hs l ξ])]
  -- Pull α-sum out of the rowFAlphaResidual sum: ∑_l (-β_l ξ^l) * A = -B*A.
  set A : ℂ := ∑ k : Fin s,
                  ((m.α (Fin.castSucc k) : ℝ) : ℂ) * ξ ^ (k : ℕ) with hA
  set B : ℂ := ∑ l : Fin s,
                  ((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ) with hB
  have hRes : (∑ l : Fin s,
        (-((m.β (Fin.castSucc l) : ℝ) : ℂ) * A) * ξ ^ (l : ℕ))
      = - B * A := by
    rw [show (∑ l : Fin s,
          (-((m.β (Fin.castSucc l) : ℝ) : ℂ) * A) * ξ ^ (l : ℕ))
        = ∑ l : Fin s,
            -(((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ)) * A from
          Finset.sum_congr rfl (fun l _ => by ring)]
    rw [show (∑ l : Fin s,
          -(((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ)) * A)
        = (∑ l : Fin s,
            -(((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ))) * A from
          (Finset.sum_mul ..).symm]
    rw [Finset.sum_neg_distrib]
  rw [hRes]
  -- Pull β_l - β_last α_l sum apart: ∑(β_l - β_last α_l) ξ^l = B - β_last A.
  have hDiff : (∑ l : Fin s,
        ( ((m.β (Fin.castSucc l) : ℝ) : ℂ)
            - ((m.β (Fin.last s) : ℝ) : ℂ) *
              ((m.α (Fin.castSucc l) : ℝ) : ℂ) ) * ξ ^ (l : ℕ))
      = B - ((m.β (Fin.last s) : ℝ) : ℂ) * A := by
    rw [show (∑ l : Fin s,
          ( ((m.β (Fin.castSucc l) : ℝ) : ℂ)
              - ((m.β (Fin.last s) : ℝ) : ℂ) *
                ((m.α (Fin.castSucc l) : ℝ) : ℂ) ) * ξ ^ (l : ℕ))
        = ∑ l : Fin s,
            (((m.β (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ)
              - ((m.β (Fin.last s) : ℝ) : ℂ) *
                (((m.α (Fin.castSucc l) : ℝ) : ℂ) * ξ ^ (l : ℕ))) from
          Finset.sum_congr rfl (fun l _ => by ring)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hDiff]
  ring

/-- §521 Step K.1 — Polynomial-level lift of J.4. Both sides are
polynomials in the indeterminate over ℂ; J.4 establishes per-ξ
evaluation equality, and `Polynomial.funext` over the infinite integral
domain ℂ upgrades that to polynomial equality. Drops the BDF hypothesis
from `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`. -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * m.stabilityPolyPoly z := by
  apply Polynomial.funext
  intro ξ
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  exact D_mul_toGLM_charpoly_eval_general m ξ hz hs

/-- §521 Step L.1 — General (non-BDF) eval-form root iff. Direct
evaluation of the cycle 736 polynomial identity K.1
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly` at `ξ`. Mirrors
`toGLM_charpoly_eval_eq_zero_iff_of_bdf` (Step C.19 / cycle 706) without
the BDF hypothesis. -/
theorem toGLM_charpoly_eval_eq_zero_iff [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
      ξ = 0 ∨ (m.stabilityPolyPoly z).eval ξ = 0 := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly m hz hs
  have heval := congrArg (Polynomial.eval ξ) h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  constructor
  · intro hcp
    rw [hcp, mul_zero] at heval
    rcases mul_eq_zero.mp heval.symm with hxs | hsp
    · exact Or.inl ((pow_eq_zero_iff hs.ne').mp hxs)
    · exact Or.inr hsp
  · intro h
    rcases h with hξ0 | hsp
    · subst hξ0
      rw [zero_pow hs.ne', zero_mul] at heval
      exact (mul_eq_zero.mp heval).resolve_left hz
    · rw [hsp, mul_zero] at heval
      exact (mul_eq_zero.mp heval).resolve_left hz

/-- §521 Step L.2 — De Morgan dual of Step L.1. Natural input to the
unit-disk root-counting argument behind `LMM.toGLM_isAStable_iff`. -/
theorem toGLM_charpoly_eval_ne_zero_iff [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ ≠ 0 ↔
      ξ ≠ 0 ∧ (m.stabilityPolyPoly z).eval ξ ≠ 0 := by
  rw [Ne, toGLM_charpoly_eval_eq_zero_iff m ξ hz, not_or]

/-- §521 Step L.3 — General LMM A-stability iff bridge. The §503
LMM-as-GLM embedding preserves A-stability in both directions, with no
BDF restriction. The denominator hypothesis `hβ_last` is the same
non-vanishing-on-the-closed-left-half-plane condition that already
appears in `toGLM_isAStable_iff_of_bdf`; for concrete LMMs it is a
short side calculation. -/
theorem toGLM_isAStable_iff
    (m : LMM s)
    (hβ_last : ∀ z : ℂ, z.re ≤ 0 →
      1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    m.toGLM.IsAStable ↔ m.IsAStable := by
  refine ⟨fun hG => ?_, fun ha => ?_⟩
  · -- (⇒) GLM A-stable ⟹ LMM A-stable
    intro z hz_re ξ hξ
    by_cases hs : s = 0
    · subst hs
      exfalso
      apply hβ_last z hz_re
      have hα0 : m.α 0 = 1 := by
        have := m.normalized
        simpa [Fin.last] using this
      have hξ' : (1 : ℂ) - z * ((m.β 0 : ℝ) : ℂ) = 0 := by
        have := hξ
        simp [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, hα0] at this
        exact this
      simpa [Fin.last] using hξ'
    · haveI : NeZero s := ⟨hs⟩
      apply hG z hz_re ξ
      show ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0
      rw [toGLM_charpoly_eval_eq_zero_iff m ξ (hβ_last z hz_re)]
      right
      rw [stabilityPolyPoly_eval]
      exact hξ
  · -- (⇐) LMM A-stable ⟹ GLM A-stable
    intro z hz_re μ hμ
    by_cases hs : s = 0
    · subst hs
      exfalso
      have hcp : ((m.toGLM.stabilityMatrix z).charpoly).eval μ = 0 :=
        Polynomial.IsRoot.eq_zero hμ
      have hone : ((m.toGLM.stabilityMatrix z).charpoly).eval μ = 1 := by
        simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_isEmpty]
      rw [hone] at hcp
      exact one_ne_zero hcp
    · haveI : NeZero s := ⟨hs⟩
      have hcp : ((m.toGLM.stabilityMatrix z).charpoly).eval μ = 0 :=
        Polynomial.IsRoot.eq_zero hμ
      rcases (toGLM_charpoly_eval_eq_zero_iff m μ
                (hβ_last z hz_re)).mp hcp with hμ0 | hsp
      · rw [hμ0]; simp
      · apply ha z hz_re
        rw [← stabilityPolyPoly_eval]
        exact hsp


end LMM
