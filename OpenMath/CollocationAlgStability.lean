import OpenMath.Legendre
import OpenMath.StiffEquations
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Theorem 358A: Algebraic Stability of Collocation Methods

This module contains the sorry-first scaffold for the collocation/algebraic-stability
characterization from Iserles, Theorem 358A:

* a collocation Runge–Kutta method is algebraically stable if and only if its
  abscissae are zeros of a polynomial of the form `P_s^* - θ P_{s-1}^*` with
  `θ ≥ 0`.

The development is kept polynomial-first so it can reuse Mathlib's
`Polynomial.shiftedLegendre` together with the bridge already proved in
`OpenMath.Legendre`.
-/

open Polynomial

namespace ButcherTableau

variable {s : ℕ}

/-- The mapped shifted Legendre polynomial viewed in `ℝ[X]`. -/
noncomputable def shiftedLegendrePoly (n : ℕ) : ℝ[X] :=
  Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)

/-- The textbook-sign shifted Legendre polynomial in `ℝ[X]`. -/
noncomputable def shiftedLegendreStarPoly (n : ℕ) : ℝ[X] :=
  Polynomial.C ((-1 : ℝ) ^ n) * shiftedLegendrePoly n

lemma shiftedLegendreStarPoly_eval (n : ℕ) (x : ℝ) :
    (shiftedLegendreStarPoly n).eval x = shiftedLegendreP n x := by
  simpa [shiftedLegendreStarPoly, Polynomial.eval_mul, Polynomial.eval_C,
    mul_comm, mul_left_comm, mul_assoc] using
    (shiftedLegendreP_eq_eval_map_shiftedLegendre n x).symm

/-- The polynomial `P_s^* - θ P_{s-1}^*` in the polynomial model used for Theorem 358A.

The ambient `shiftedLegendrePoly` uses Mathlib's `Polynomial.shiftedLegendre`,
whose evaluation differs from the textbook `P_n^*` by the factor `(-1)^n`; the
global `(-1)^s` below corrects that convention so the zero set and leading sign
match the textbook boundary polynomial. -/
noncomputable def algStabilityBoundaryPoly (s : ℕ) (θ : ℝ) : ℝ[X] :=
  shiftedLegendreStarPoly s - Polynomial.C θ * shiftedLegendreStarPoly (s - 1)

/-- The theorem-local collocation interface used for Theorem 358A.

We package only the existing assumptions already available in the project:
`B(s)`, `C(s)`, and injective nodes. -/
def IsCollocation (t : ButcherTableau s) : Prop :=
  0 < s ∧ t.SatisfiesB s ∧ t.SatisfiesC s ∧ Function.Injective t.c

/-- The nodes lie on a shifted-Legendre algebraic-stability boundary. -/
def HasAlgStabilityBoundaryNodes (t : ButcherTableau s) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ ∀ i : Fin s, (algStabilityBoundaryPoly s θ).eval (t.c i) = 0

/-- The node polynomial has positive leading coefficient. -/
lemma nodePoly_leadingCoeff_pos (t : ButcherTableau s) :
    0 < (nodePoly t).leadingCoeff := by
  rw [(nodePoly_monic t).leadingCoeff]
  norm_num

private lemma algStabMatrix_quadForm_expand
    (t : ButcherTableau s) (v : Fin s → ℝ) :
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      2 * (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j) -
        (∑ i : Fin s, t.b i * v i) ^ 2 := by
  have h_expand : ∀ i j : Fin s, v i * t.algStabMatrix i j * v j =
      t.b i * v i * t.A i j * v j + t.b j * v j * t.A j i * v i -
        t.b i * v i * t.b j * v j := by
    intro i j
    rw [algStabMatrix]
    ring
  simp_rw [h_expand, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h_sq : ∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.b j * v j =
      (∑ i : Fin s, t.b i * v i) ^ 2 := by
    have : ∀ i j : Fin s, t.b i * v i * t.b j * v j = (t.b i * v i) * (t.b j * v j) := by
      intro i j
      ring
    simp_rw [this, sq, ← Finset.sum_mul_sum]
  have h_sym : ∑ i : Fin s, ∑ j : Fin s, t.b j * v j * t.A j i * v i =
      ∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j := Finset.sum_comm
  linarith [h_sq, h_sym]

private lemma algStabMatrix_monomial_inner_eq
    (t : ButcherTableau s) (hC : t.SatisfiesC s) {k : ℕ} (hk : k < s) :
    ∑ i : Fin s, ∑ j : Fin s, t.b i * t.c i ^ k * t.A i j * t.c j ^ k =
      (1 / (((k + 1 : ℕ) : ℝ))) * (∑ i : Fin s, t.b i * t.c i ^ (2 * k + 1)) := by
  have hCk : ∀ i : Fin s,
      ∑ j : Fin s, t.A i j * t.c j ^ k = t.c i ^ (k + 1) / (((k + 1 : ℕ) : ℝ)) := by
    intro i
    exact hC (k + 1) (by omega) (by omega) i
  calc
    ∑ i : Fin s, ∑ j : Fin s, t.b i * t.c i ^ k * t.A i j * t.c j ^ k
        = ∑ i : Fin s, t.b i * t.c i ^ k * (∑ j : Fin s, t.A i j * t.c j ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ∑ j : Fin s, t.b i * t.c i ^ k * t.A i j * t.c j ^ k
                  = ∑ j : Fin s, (t.b i * t.c i ^ k) * (t.A i j * t.c j ^ k) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      ring
              _ = t.b i * t.c i ^ k * (∑ j : Fin s, t.A i j * t.c j ^ k) := by
                    rw [Finset.mul_sum]
    _ = ∑ i : Fin s, t.b i * t.c i ^ k * (t.c i ^ (k + 1) / (((k + 1 : ℕ) : ℝ))) := by
          simp [hCk]
    _ = (1 / (((k + 1 : ℕ) : ℝ))) * (∑ i : Fin s, t.b i * t.c i ^ (2 * k + 1)) := by
          calc
            ∑ i : Fin s, t.b i * t.c i ^ k * (t.c i ^ (k + 1) / (((k + 1 : ℕ) : ℝ)))
                = ∑ i : Fin s, (1 / (((k + 1 : ℕ) : ℝ))) * (t.b i * t.c i ^ (2 * k + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    rw [show 2 * k + 1 = k + (k + 1) by omega, pow_add]
                    ring
            _ = (1 / (((k + 1 : ℕ) : ℝ))) * (∑ i : Fin s, t.b i * t.c i ^ (2 * k + 1)) := by
                  rw [Finset.mul_sum]

private lemma algStabMatrix_monomial_quadForm_eq
    (t : ButcherTableau s) (hB : t.SatisfiesB s) (hC : t.SatisfiesC s) {k : ℕ} (hk : k < s) :
    ∑ i : Fin s, ∑ j : Fin s, t.c i ^ k * t.algStabMatrix i j * t.c j ^ k =
      2 / (((k + 1 : ℕ) : ℝ)) * (∑ i : Fin s, t.b i * t.c i ^ (2 * k + 1)) -
        1 / ((((k + 1 : ℕ) : ℝ)) ^ 2) := by
  have hBk : ∑ i : Fin s, t.b i * t.c i ^ k = 1 / (((k + 1 : ℕ) : ℝ)) := by
    exact hB (k + 1) (by omega) (by omega)
  rw [algStabMatrix_quadForm_expand (v := fun i => t.c i ^ k),
    algStabMatrix_monomial_inner_eq t hC hk, hBk]
  ring

private lemma algStabMatrix_monomial_quadForm_zero
    (t : ButcherTableau s) (hB : t.SatisfiesB s) (hC : t.SatisfiesC s) {k : ℕ} (hk : k < s)
    (hBhigh : t.SatisfiesB (2 * k + 2)) :
    ∑ i : Fin s, ∑ j : Fin s, t.c i ^ k * t.algStabMatrix i j * t.c j ^ k = 0 := by
  have hmoment : ∑ i : Fin s, t.b i * t.c i ^ (2 * k + 1) = 1 / (((2 * k + 2 : ℕ) : ℝ)) := by
    exact hBhigh (2 * k + 2) (by omega) le_rfl
  rw [algStabMatrix_monomial_quadForm_eq t hB hC hk, hmoment]
  have hcast : (((2 * k + 2 : ℕ) : ℝ)) = 2 * (((k + 1 : ℕ) : ℝ)) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [hcast]
  field_simp
  ring

private lemma algStabMatrix_row_eq_col
    (t : ButcherTableau s) (v : Fin s → ℝ) (j : Fin s) :
    ∑ i : Fin s, v i * t.algStabMatrix i j = ∑ i : Fin s, t.algStabMatrix j i * v i := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [t.algStabMatrix_symm i j]
  ring

private lemma algStabMatrix_quadForm_shift_single
    (t : ButcherTableau s) (v : Fin s → ℝ) (j : Fin s) (z : ℝ) :
    ∑ i : Fin s, ∑ l : Fin s,
        (v i + (Pi.single j z : Fin s → ℝ) i) * t.algStabMatrix i l *
          (v l + (Pi.single j z : Fin s → ℝ) l)
      = (∑ i : Fin s, ∑ l : Fin s, v i * t.algStabMatrix i l * v l)
          + z * (∑ l : Fin s, t.algStabMatrix j l * v l)
          + z * (∑ i : Fin s, v i * t.algStabMatrix i j)
          + z ^ 2 * t.algStabMatrix j j := by
  simp [Pi.single_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, pow_two]
  ring_nf

private lemma algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero
    (t : ButcherTableau s) (hAlg : t.IsAlgStable) (v : Fin s → ℝ)
    (hquad_zero : ∑ i : Fin s, ∑ l : Fin s, v i * t.algStabMatrix i l * v l = 0) :
    ∀ j : Fin s, ∑ i : Fin s, t.algStabMatrix j i * v i = 0 := by
  intro j
  have hdiag_nonneg : 0 ≤ t.algStabMatrix j j := by
    have h := hAlg.posdef_M (Pi.single j (1 : ℝ))
    simpa [Pi.single_apply] using h
  by_contra hrow_ne
  let a : ℝ := ∑ i : Fin s, t.algStabMatrix j i * v i
  let z : ℝ := -a / (t.algStabMatrix j j + 1)
  have hz_neg : 2 * z * a + z ^ 2 * t.algStabMatrix j j < 0 := by
    dsimp [z]
    have hjj_pos : 0 < t.algStabMatrix j j + 1 := by linarith
    have hjj_ne : t.algStabMatrix j j + 1 ≠ 0 := by linarith
    field_simp [hjj_ne]
    have ha2 : 0 < a ^ 2 := by
      dsimp [a]
      nlinarith [sq_pos_of_ne_zero hrow_ne]
    have hfac : -(2 * (t.algStabMatrix j j + 1)) + t.algStabMatrix j j < 0 := by
      nlinarith
    nlinarith
  have hpsd := hAlg.posdef_M (fun i => v i + (Pi.single j z : Fin s → ℝ) i)
  rw [algStabMatrix_quadForm_shift_single t v j z, hquad_zero, algStabMatrix_row_eq_col t v j] at hpsd
  dsimp [a] at hz_neg
  linarith

private lemma algStabMatrix_monomial_row_action
    (t : ButcherTableau s) (j : Fin s) (k : ℕ) :
    ∑ i : Fin s, t.algStabMatrix j i * t.c i ^ k =
      t.b j * (∑ i : Fin s, t.A j i * t.c i ^ k)
        + (∑ i : Fin s, t.b i * t.c i ^ k * t.A i j)
        - t.b j * (∑ i : Fin s, t.b i * t.c i ^ k) := by
  calc
    ∑ i : Fin s, t.algStabMatrix j i * t.c i ^ k
        = ∑ i : Fin s,
            (t.b j * (t.A j i * t.c i ^ k)
              + t.b i * t.c i ^ k * t.A i j
              - t.b j * (t.b i * t.c i ^ k)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [algStabMatrix]
            ring
    _ = (∑ i : Fin s, t.b j * (t.A j i * t.c i ^ k))
          + (∑ i : Fin s, t.b i * t.c i ^ k * t.A i j)
          - (∑ i : Fin s, t.b j * (t.b i * t.c i ^ k)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = t.b j * (∑ i : Fin s, t.A j i * t.c i ^ k)
          + (∑ i : Fin s, t.b i * t.c i ^ k * t.A i j)
          - t.b j * (∑ i : Fin s, t.b i * t.c i ^ k) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]

private lemma monomialVec_D_of_algStable
    (t : ButcherTableau s) (hAlg : t.IsAlgStable) (hB : t.SatisfiesB s) (hC : t.SatisfiesC s)
    {k : ℕ} (hk : k < s)
    (hquad_zero : ∑ i : Fin s, ∑ l : Fin s,
      t.c i ^ k * t.algStabMatrix i l * t.c l ^ k = 0) :
    ∀ j : Fin s,
      ∑ i : Fin s, t.b i * t.c i ^ k * t.A i j =
        t.b j / (((k + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (k + 1)) := by
  let v : Fin s → ℝ := fun i => t.c i ^ k
  have hMv_zero :
      ∀ j : Fin s, ∑ i : Fin s, t.algStabMatrix j i * v i = 0 := by
    apply algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero t hAlg v
    simpa [v] using hquad_zero
  have hB_piece : ∑ i : Fin s, t.b i * t.c i ^ k = 1 / (((k + 1 : ℕ) : ℝ)) := by
    exact hB (k + 1) (by omega) (by omega)
  intro j
  have hC_piece : ∑ i : Fin s, t.A j i * t.c i ^ k = t.c j ^ (k + 1) / (((k + 1 : ℕ) : ℝ)) := by
    exact hC (k + 1) (by omega) (by omega) j
  have hrow_zero : ∑ i : Fin s, t.algStabMatrix j i * t.c i ^ k = 0 := by
    simpa [v] using hMv_zero j
  have hrow :
      t.b j * (∑ i : Fin s, t.A j i * t.c i ^ k)
        + (∑ i : Fin s, t.b i * t.c i ^ k * t.A i j)
        - t.b j * (∑ i : Fin s, t.b i * t.c i ^ k) = 0 := by
    rw [← algStabMatrix_monomial_row_action t j k]
    exact hrow_zero
  have hscalar :
      t.b j * (t.c j ^ (k + 1) / (((k + 1 : ℕ) : ℝ)))
        + (∑ i : Fin s, t.b i * t.c i ^ k * t.A i j)
        - t.b j * (1 / (((k + 1 : ℕ) : ℝ))) = 0 := by
    simpa [hC_piece, hB_piece] using hrow
  have hk1_ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hk1_ne] at hscalar ⊢
  nlinarith

private lemma moment_upgrade_from_D
    (t : ButcherTableau s) (hs : 0 < s) (k : ℕ)
    (hB : t.SatisfiesB s) (hC : t.SatisfiesC s)
    (hD : ∀ j : Fin s,
      ∑ i : Fin s, t.b i * t.c i ^ k * t.A i j =
        t.b j / (((k + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (k + 1))) :
    ∑ i : Fin s, t.b i * t.c i ^ (k + s) = 1 / (((k + s + 1 : ℕ) : ℝ)) := by
  have hC_s : ∀ i, ∑ j, t.A i j * t.c j ^ (s - 1) = t.c i ^ s / ((s : ℕ) : ℝ) := by
    exact fun i => hC s hs le_rfl i
  have h_sum :
      ∑ j, (∑ i, t.b i * t.c i ^ k * t.A i j) * t.c j ^ (s - 1) =
        ∑ i, t.b i * t.c i ^ k * (∑ j, t.A i j * t.c j ^ (s - 1)) := by
    simpa [mul_assoc, Finset.mul_sum, Finset.sum_mul] using Finset.sum_comm
  simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum, pow_add]
  simp_all [mul_sub, ← mul_assoc, ← pow_succ', ← Finset.mul_sum, ← Finset.sum_mul]
  simp_all [mul_assoc, ← pow_add, ← Finset.mul_sum, ← Finset.sum_mul]
  have hBs := hB (s - 1 + 1) (by omega) (by omega)
  simp_all [Nat.sub_add_cancel hs]
  field_simp at *
  rw [show s - 1 + (k + 1) = s + k by omega] at h_sum
  linarith

private lemma satisfiesB_two_mul_sub_one_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    t.SatisfiesB (2 * s - 1) := by
  have hind : ∀ k ≤ s - 1, t.SatisfiesB (s + k) := by
    intro k hk
    induction' k with k ih
    · simpa using hcoll.2.1
    · have hk' : k ≤ s - 2 := by omega
      have hBk : t.SatisfiesB (s + k) := ih (by omega)
      have hBhigh : t.SatisfiesB (2 * k + 2) := SatisfiesB.mono hBk (by omega)
      have hquad_zero :
          ∑ i : Fin s, ∑ j : Fin s, t.c i ^ k * t.algStabMatrix i j * t.c j ^ k = 0 := by
        exact algStabMatrix_monomial_quadForm_zero t hcoll.2.1 hcoll.2.2.1 (by omega) hBhigh
      have hD :
          ∀ j : Fin s,
            ∑ i : Fin s, t.b i * t.c i ^ k * t.A i j =
              t.b j / (((k + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (k + 1)) := by
        exact monomialVec_D_of_algStable t hAlg hcoll.2.1 hcoll.2.2.1 (by omega) hquad_zero
      have hmoment :
          ∑ i : Fin s, t.b i * t.c i ^ (k + s) = 1 / (((k + s + 1 : ℕ) : ℝ)) := by
        exact moment_upgrade_from_D t hcoll.1 k hcoll.2.1 hcoll.2.2.1 hD
      intro n hn1 hn2
      by_cases hle : n ≤ s + k
      · exact hBk n hn1 hle
      · have hn_eq : n = s + k + 1 := by omega
        subst hn_eq
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmoment
  convert hind (s - 1) le_rfl using 1 <;> omega

/-- The live `(358c)` zero statement extracted from the transformed matrix
input behind algebraic stability.

This is the actual theorem-local seam for Theorem 358A: once this interval form
is proved from `hAlg.posdef_M`, the moment formulation below follows from the
existing polynomial/integral bridge in `OpenMath.Legendre`. -/
lemma nodePoly_interval_zero_aux_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  intro q hq
  have hq_lt_s : q.natDegree < s := by
    omega
  have hB2s1 : t.SatisfiesB (2 * s - 1) :=
    satisfiesB_two_mul_sub_one_of_algStable t hcoll hAlg
  have hdeg :
      ((nodePoly t) * q).natDegree < 2 * s - 1 := by
    calc
      ((nodePoly t) * q).natDegree ≤ (nodePoly t).natDegree + q.natDegree :=
        Polynomial.natDegree_mul_le
      _ < s + (s - 1) := by
        rw [nodePoly_natDegree]
        omega
      _ = 2 * s - 1 := by omega
  rw [← polyMomentN_eq_intervalIntegral_of_natDegree_lt (N := 2 * s - 1) ((nodePoly t) * q) hdeg]
  rw [← quadEvalPoly_exact_of_natDegree_lt_of_SatisfiesB t hB2s1 ((nodePoly t) * q) hdeg]
  exact quadEvalPoly_nodePoly_mul_eq_zero t q hq_lt_s

private lemma algStabMatrix_monomial_bilinear_zero_main
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    {a b : ℕ} (ha : a < s) (hb : b < s)
    (ha2 : 2 * a + 2 ≤ 2 * s - 1) (hab2 : a + b + 2 ≤ 2 * s - 1) :
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ a * t.algStabMatrix i j * t.c j ^ b = 0 := by
  have hB2s1 : t.SatisfiesB (2 * s - 1) :=
    satisfiesB_two_mul_sub_one_of_algStable t hcoll hAlg
  have hBa : ∑ i : Fin s, t.b i * t.c i ^ a = 1 / (((a + 1 : ℕ) : ℝ)) := by
    exact hcoll.2.1 (a + 1) (by omega) (by omega)
  have hBb : ∑ i : Fin s, t.b i * t.c i ^ b = 1 / (((b + 1 : ℕ) : ℝ)) := by
    exact hcoll.2.1 (b + 1) (by omega) (by omega)
  have hBab :
      ∑ i : Fin s, t.b i * t.c i ^ (a + b + 1) =
        1 / (((a + b + 2 : ℕ) : ℝ)) := by
    exact hB2s1 (a + b + 2) (by omega) hab2
  have hC_a :
      ∀ j : Fin s,
        ∑ i : Fin s, t.A j i * t.c i ^ a =
          t.c j ^ (a + 1) / (((a + 1 : ℕ) : ℝ)) := by
    intro j
    exact hcoll.2.2.1 (a + 1) (by omega) (by omega) j
  have hBhigh_a : t.SatisfiesB (2 * a + 2) :=
    SatisfiesB.mono hB2s1 ha2
  have hquad_zero_a :
      ∑ i : Fin s, ∑ j : Fin s,
        t.c i ^ a * t.algStabMatrix i j * t.c j ^ a = 0 := by
    exact algStabMatrix_monomial_quadForm_zero
      t hcoll.2.1 hcoll.2.2.1 ha hBhigh_a
  have hD_a :
      ∀ j : Fin s,
        ∑ i : Fin s, t.b i * t.c i ^ a * t.A i j =
          t.b j / (((a + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (a + 1)) := by
    exact monomialVec_D_of_algStable
      t hAlg hcoll.2.1 hcoll.2.2.1 ha hquad_zero_a
  let SD : ℝ :=
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ a * (t.b i * t.A i j) * t.c j ^ b
  let SC : ℝ :=
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ a * (t.b j * t.A j i) * t.c j ^ b
  let SB : ℝ :=
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ a * (t.b i * t.b j) * t.c j ^ b
  have hsplit_direct :
      ∑ i : Fin s, ∑ j : Fin s,
        t.c i ^ a * t.algStabMatrix i j * t.c j ^ b =
        (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.A i j) * t.c j ^ b)
          + (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b j * t.A j i) * t.c j ^ b)
          - (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.b j) * t.c j ^ b) := by
    calc
      ∑ i : Fin s, ∑ j : Fin s,
          t.c i ^ a * t.algStabMatrix i j * t.c j ^ b
          = ∑ i : Fin s, ∑ j : Fin s,
              (t.c i ^ a * (t.b i * t.A i j) * t.c j ^ b
                + t.c i ^ a * (t.b j * t.A j i) * t.c j ^ b
                - t.c i ^ a * (t.b i * t.b j) * t.c j ^ b) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [algStabMatrix]
                  ring
      _ = (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.A i j) * t.c j ^ b)
            + (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b j * t.A j i) * t.c j ^ b)
            - (∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.b j) * t.c j ^ b) := by
              simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hsplit :
      ∑ i : Fin s, ∑ j : Fin s,
        t.c i ^ a * t.algStabMatrix i j * t.c j ^ b =
        SD + SC - SB := by
    simpa [SD, SC, SB] using hsplit_direct
  have hSD :
      SD =
        (1 / (((a + 1 : ℕ) : ℝ))) *
          (∑ j : Fin s, t.b j * t.c j ^ b)
        - (1 / (((a + 1 : ℕ) : ℝ))) *
          (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
    dsimp [SD]
    calc
      ∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.A i j) * t.c j ^ b
          = ∑ j : Fin s, ∑ i : Fin s, t.c j ^ b * (t.b i * t.c i ^ a * t.A i j) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ∑ j : Fin s, t.c j ^ b * (∑ i : Fin s, t.b i * t.c i ^ a * t.A i j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [Finset.mul_sum]
      _ = ∑ j : Fin s,
            t.c j ^ b * (t.b j / (((a + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (a + 1))) := by
            simp [hD_a]
      _ = (1 / (((a + 1 : ℕ) : ℝ))) * (∑ j : Fin s, t.b j * t.c j ^ b)
            - (1 / (((a + 1 : ℕ) : ℝ))) *
                (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
            calc
              ∑ j : Fin s, t.c j ^ b *
                  (t.b j / (((a + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (a + 1)))
                  = ∑ j : Fin s,
                      ((1 / (((a + 1 : ℕ) : ℝ))) * (t.b j * t.c j ^ b)
                        - (1 / (((a + 1 : ℕ) : ℝ))) *
                            (t.b j * t.c j ^ (a + b + 1))) := by
                              refine Finset.sum_congr rfl ?_
                              intro j hj
                              rw [pow_add]
                              ring
              _ = (∑ j : Fin s,
                      (1 / (((a + 1 : ℕ) : ℝ))) * (t.b j * t.c j ^ b))
                    - (∑ j : Fin s,
                        (1 / (((a + 1 : ℕ) : ℝ))) *
                          (t.b j * t.c j ^ (a + b + 1))) := by
                      rw [Finset.sum_sub_distrib]
              _ = (1 / (((a + 1 : ℕ) : ℝ))) * (∑ j : Fin s, t.b j * t.c j ^ b)
                    - (1 / (((a + 1 : ℕ) : ℝ))) *
                        (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
                      rw [Finset.mul_sum, Finset.mul_sum]
  have hSC :
      SC =
        (1 / (((a + 1 : ℕ) : ℝ))) *
          (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
    dsimp [SC]
    calc
      ∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b j * t.A j i) * t.c j ^ b
          = ∑ j : Fin s, ∑ i : Fin s, (t.b j * t.c j ^ b) * (t.A j i * t.c i ^ a) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ∑ j : Fin s, t.b j * t.c j ^ b * (∑ i : Fin s, t.A j i * t.c i ^ a) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [Finset.mul_sum]
      _ = ∑ j : Fin s,
            t.b j * t.c j ^ b * (t.c j ^ (a + 1) / (((a + 1 : ℕ) : ℝ))) := by
            simp [hC_a]
      _ = (1 / (((a + 1 : ℕ) : ℝ))) *
            (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
            calc
              ∑ j : Fin s,
                  t.b j * t.c j ^ b * (t.c j ^ (a + 1) / (((a + 1 : ℕ) : ℝ)))
                  = ∑ j : Fin s,
                      (1 / (((a + 1 : ℕ) : ℝ))) *
                        (t.b j * t.c j ^ (a + b + 1)) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          rw [show a + b + 1 = b + (a + 1) by omega, pow_add]
                          ring
              _ = (1 / (((a + 1 : ℕ) : ℝ))) *
                    (∑ j : Fin s, t.b j * t.c j ^ (a + b + 1)) := by
                      rw [Finset.mul_sum]
  have hSB :
      SB =
        (∑ i : Fin s, t.b i * t.c i ^ a) *
          (∑ j : Fin s, t.b j * t.c j ^ b) := by
    dsimp [SB]
    calc
      ∑ i : Fin s, ∑ j : Fin s, t.c i ^ a * (t.b i * t.b j) * t.c j ^ b
          = ∑ i : Fin s, ∑ j : Fin s,
              (t.b i * t.c i ^ a) * (t.b j * t.c j ^ b) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
      _ = (∑ i : Fin s, t.b i * t.c i ^ a) *
            (∑ j : Fin s, t.b j * t.c j ^ b) := by
              rw [← Finset.sum_mul_sum]
  rw [hsplit, hSD, hSC, hSB, hBa, hBb, hBab]
  have ha1_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hb1_ne : (((b + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hab2_ne : (((a + b + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [ha1_ne, hb1_ne, hab2_ne]
  ring

private lemma algStabMatrix_monomial_bilinear_zero
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    {m n : ℕ} (hm : m < s) (hn : n < s) (hmn : m + n + 2 ≤ 2 * s - 1) :
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ m * t.algStabMatrix i j * t.c j ^ n = 0 := by
  by_cases hmn_le : m ≤ n
  · have hm2 : 2 * m + 2 ≤ 2 * s - 1 := by
      omega
    exact algStabMatrix_monomial_bilinear_zero_main t hcoll hAlg hm hn hm2 hmn
  · have hswap :
        ∑ i : Fin s, ∑ j : Fin s,
          t.c i ^ m * t.algStabMatrix i j * t.c j ^ n =
          ∑ i : Fin s, ∑ j : Fin s,
            t.c i ^ n * t.algStabMatrix i j * t.c j ^ m := by
      calc
        ∑ i : Fin s, ∑ j : Fin s,
            t.c i ^ m * t.algStabMatrix i j * t.c j ^ n
            = ∑ i : Fin s, ∑ j : Fin s,
                t.c j ^ m * t.algStabMatrix j i * t.c i ^ n := by
                  rw [Finset.sum_comm]
        _ = ∑ i : Fin s, ∑ j : Fin s,
              t.c i ^ n * t.algStabMatrix i j * t.c j ^ m := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [t.algStabMatrix_symm]
                ring
    rw [hswap]
    have hn2 : 2 * n + 2 ≤ 2 * s - 1 := by
      omega
    exact algStabMatrix_monomial_bilinear_zero_main t hcoll hAlg hn hm hn2 (by omega)

private lemma algStabMatrix_poly_bilinear_zero
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (p r : ℝ[X]) (hp : p.natDegree < s) (hr : r.natDegree < s)
    (hpr : p.natDegree + r.natDegree + 2 ≤ 2 * s - 1) :
    ∑ i : Fin s, ∑ j : Fin s,
      p.eval (t.c i) * t.algStabMatrix i j * r.eval (t.c j) = 0 := by
  have hpeval : ∀ i : Fin s, p.eval (t.c i) = ∑ m ∈ Finset.range s, p.coeff m * t.c i ^ m := by
    intro i
    simpa using (Polynomial.eval_eq_sum_range' (p := p) hp (t.c i))
  have hreval : ∀ j : Fin s, r.eval (t.c j) = ∑ n ∈ Finset.range s, r.coeff n * t.c j ^ n := by
    intro j
    simpa using (Polynomial.eval_eq_sum_range' (p := r) hr (t.c j))
  simp_rw [hpeval, hreval, Finset.sum_mul, Finset.mul_sum]
  calc
    ∑ x,
        ∑ x_1,
          ∑ x_2 ∈ Finset.range s,
            ∑ i ∈ Finset.range s,
              p.coeff x_2 * t.c x ^ x_2 * t.algStabMatrix x x_1 * (r.coeff i * t.c x_1 ^ i)
      =
        ∑ x,
          ∑ x_2 ∈ Finset.range s,
            ∑ x_1,
              ∑ i ∈ Finset.range s,
                p.coeff x_2 * t.c x ^ x_2 * t.algStabMatrix x x_1 * (r.coeff i * t.c x_1 ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_comm]
    _ =
        ∑ x_2 ∈ Finset.range s,
          ∑ x,
            ∑ x_1,
              ∑ i ∈ Finset.range s,
                p.coeff x_2 * t.c x ^ x_2 * t.algStabMatrix x x_1 * (r.coeff i * t.c x_1 ^ i) := by
          rw [Finset.sum_comm]
    _ =
        ∑ x_2 ∈ Finset.range s,
          ∑ x,
            ∑ i ∈ Finset.range s,
              ∑ x_1,
                p.coeff x_2 * t.c x ^ x_2 * t.algStabMatrix x x_1 * (r.coeff i * t.c x_1 ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro x_2 hx_2
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_comm]
    _ =
        ∑ x_2 ∈ Finset.range s,
          ∑ i ∈ Finset.range s,
            ∑ x,
              ∑ x_1,
                p.coeff x_2 * t.c x ^ x_2 * t.algStabMatrix x x_1 * (r.coeff i * t.c x_1 ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro x_2 hx_2
          rw [Finset.sum_comm]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro m hm
          refine Finset.sum_eq_zero ?_
          intro n hn
          by_cases hmdeg : m ≤ p.natDegree
          · by_cases hndeg : n ≤ r.natDegree
            · have hmn : m + n + 2 ≤ 2 * s - 1 := by
                omega
              rw [show
                    ∑ x, ∑ x_1,
                      p.coeff m * t.c x ^ m * t.algStabMatrix x x_1 * (r.coeff n * t.c x_1 ^ n)
                    =
                    p.coeff m * r.coeff n *
                      (∑ x, ∑ x_1,
                        t.c x ^ m * t.algStabMatrix x x_1 * t.c x_1 ^ n) by
                    calc
                      ∑ x, ∑ x_1,
                          p.coeff m * t.c x ^ m * t.algStabMatrix x x_1 * (r.coeff n * t.c x_1 ^ n)
                          =
                          ∑ x, ∑ x_1,
                            p.coeff m * r.coeff n *
                              (t.c x ^ m * t.algStabMatrix x x_1 * t.c x_1 ^ n) := by
                                refine Finset.sum_congr rfl ?_
                                intro x hx
                                refine Finset.sum_congr rfl ?_
                                intro x_1 hx_1
                                ring
                      _ =
                          p.coeff m * r.coeff n *
                            (∑ x, ∑ x_1,
                              t.c x ^ m * t.algStabMatrix x x_1 * t.c x_1 ^ n) := by
                                simp_rw [Finset.mul_sum]
                                ]
              rw [algStabMatrix_monomial_bilinear_zero t hcoll hAlg
                (Finset.mem_range.mp hm) (Finset.mem_range.mp hn) hmn]
              ring
            · have hcoeff : r.coeff n = 0 := by
                exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hndeg)
              simp [hcoeff]
          · have hcoeff : p.coeff m = 0 := by
              exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hmdeg)
            simp [hcoeff]

private lemma sub_leading_term_natDegree_lt
    (hs : 1 < s) (q : ℝ[X]) (hqtop : q.natDegree = s - 1) :
    let r := q - Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)
    r.natDegree < s - 1 := by
  dsimp
  have hs1 : 0 < s - 1 := by
    omega
  have hq_ne : q ≠ 0 := by
    intro hq0
    subst hq0
    simp at hqtop
    omega
  have hlc_ne : q.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hq_ne
  have htop_deg :
      (Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)).natDegree = s - 1 := by
    simpa using Polynomial.natDegree_C_mul_X_pow (s - 1) q.leadingCoeff hlc_ne
  have htop_ne : Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1) ≠ 0 := by
    exact mul_ne_zero (by simpa using hlc_ne) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hdeg_eq :
      q.degree = (Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)).degree := by
    rw [Polynomial.degree_eq_natDegree hq_ne, Polynomial.degree_eq_natDegree htop_ne, hqtop, htop_deg]
  have hlc_eq :
      q.leadingCoeff = (Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_C_mul_X_pow]
  have hdeg_lt :
      (q - (Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1))).degree < q.degree := by
    exact Polynomial.degree_sub_lt hdeg_eq hq_ne hlc_eq
  by_cases hrzero : q - (Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)) = 0
  · rw [hrzero]
    simpa using hs1
  · rwa [Polynomial.degree_eq_natDegree hrzero, Polynomial.degree_eq_natDegree hq_ne, hqtop,
      Nat.cast_lt] at hdeg_lt

private lemma algStabMatrix_top_monomial_eq_neg_integral
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∑ i : Fin s, ∑ j : Fin s,
      t.c i ^ (s - 1) * t.algStabMatrix i j * t.c j ^ (s - 1) =
      -2 * ((1 : ℝ) / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * Polynomial.X ^ (s - 1)).eval x := by
  have hs : 0 < s := hcoll.1
  let p : ℝ[X] := (nodePoly t) * Polynomial.X ^ (s - 1)
  let lower : ℝ[X] := p - Polynomial.C p.leadingCoeff * Polynomial.X ^ (2 * s - 1)
  have hplc : p.leadingCoeff = 1 := by
    dsimp [p]
    rw [Polynomial.leadingCoeff_mul, (nodePoly_monic t).leadingCoeff,
      Polynomial.leadingCoeff_X_pow]
    norm_num
  have hpdeg : p.natDegree = 2 * s - 1 := by
    dsimp [p]
    rw [Polynomial.natDegree_mul' (by
      simp [(nodePoly_monic t).leadingCoeff])]
    · rw [nodePoly_natDegree t, Polynomial.natDegree_X_pow]
      omega
  have hlower_deg : lower.natDegree < 2 * s - 1 := by
    dsimp [lower]
    simpa [hpdeg, hplc] using
      (sub_leading_term_natDegree_lt (s := 2 * s) (by omega) p (by simpa [hpdeg]))
  have hB2s1 : t.SatisfiesB (2 * s - 1) :=
    satisfiesB_two_mul_sub_one_of_algStable t hcoll hAlg
  have hXdeg : (Polynomial.X ^ (s - 1) : ℝ[X]).natDegree < s := by
    rw [Polynomial.natDegree_X_pow]
    omega
  have hquad_p : quadEvalPoly t p = 0 := by
    dsimp [p]
    exact quadEvalPoly_nodePoly_mul_eq_zero t (Polynomial.X ^ (s - 1)) hXdeg
  have hquad_lower_integral : quadEvalPoly t lower = ∫ x in (0 : ℝ)..1, lower.eval x := by
    rw [quadEvalPoly_exact_of_natDegree_lt_of_SatisfiesB t hB2s1 lower hlower_deg,
      polyMomentN_eq_intervalIntegral_of_natDegree_lt lower hlower_deg]
  have hquad_lower :
      quadEvalPoly t lower = -∑ i : Fin s, t.b i * t.c i ^ (2 * s - 1) := by
    calc
      quadEvalPoly t lower
          = quadEvalPoly t p -
              quadEvalPoly t (Polynomial.C p.leadingCoeff * Polynomial.X ^ (2 * s - 1)) := by
              unfold quadEvalPoly
              simp [lower, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]
      _ = -quadEvalPoly t (Polynomial.C p.leadingCoeff * Polynomial.X ^ (2 * s - 1)) := by
            rw [hquad_p]
            ring
      _ = -∑ i : Fin s, t.b i * t.c i ^ (2 * s - 1) := by
            rw [hplc]
            simp [quadEvalPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
              Polynomial.eval_X]
  have hlower_integral :
      ∫ x in (0 : ℝ)..1, lower.eval x = -∑ i : Fin s, t.b i * t.c i ^ (2 * s - 1) := by
    rw [← hquad_lower_integral]
    exact hquad_lower
  have htop_integral :
      ∫ x in (0 : ℝ)..1,
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ (2 * s - 1)).eval x =
          (1 : ℝ) / (2 * s : ℝ) := by
    rw [hplc]
    rw [Polynomial.C_1, one_mul]
    rw [show (fun x : ℝ => (Polynomial.X ^ (2 * s - 1)).eval x) = fun x : ℝ => x ^ (2 * s - 1) by
      funext x
      simp [Polynomial.eval_pow, Polynomial.eval_X]]
    rw [integral_pow]
    have hnat : (2 * s - 1) + 1 = 2 * s := by
      omega
    have hnatR : ((2 * s - 1 : ℕ) : ℝ) + 1 = (2 * s : ℕ) := by
      exact_mod_cast hnat
    simp
    rw [hnatR]
    have hs_ne : (s : ℝ) ≠ 0 := by positivity
    field_simp [hs_ne]
    norm_num [Nat.cast_mul]
    ring
  have hp_integral :
      ∫ x in (0 : ℝ)..1, p.eval x =
        (1 : ℝ) / (2 * s : ℝ) - ∑ i : Fin s, t.b i * t.c i ^ (2 * s - 1) := by
    have hpeval_split :
        (fun x : ℝ => p.eval x) =
          fun x : ℝ =>
            lower.eval x +
              (Polynomial.C p.leadingCoeff * Polynomial.X ^ (2 * s - 1)).eval x := by
      funext x
      dsimp [lower]
      rw [Polynomial.eval_sub]
      ring
    rw [hpeval_split, intervalIntegral.integral_add]
    · rw [hlower_integral, htop_integral]
      ring
    · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
    · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
  have hmono :=
    algStabMatrix_monomial_quadForm_eq t hcoll.2.1 hcoll.2.2.1 (show s - 1 < s by omega)
  have hs_ne : (s : ℝ) ≠ 0 := by positivity
  have hfinal :
      ∑ i : Fin s, ∑ j : Fin s,
          t.c i ^ (s - 1) * t.algStabMatrix i j * t.c j ^ (s - 1) =
        -2 * ((1 : ℝ) / (s : ℝ)) * ∫ x in (0 : ℝ)..1, p.eval x := by
    calc
    ∑ i : Fin s, ∑ j : Fin s,
        t.c i ^ (s - 1) * t.algStabMatrix i j * t.c j ^ (s - 1)
      = 2 / (s : ℝ) * (∑ i : Fin s, t.b i * t.c i ^ (2 * s - 1)) - 1 / (s : ℝ) ^ 2 := by
          simpa [Nat.sub_add_cancel hs, show 2 * (s - 1) + 1 = 2 * s - 1 by omega, pow_two]
            using hmono
    _ = -2 * ((1 : ℝ) / (s : ℝ)) * ∫ x in (0 : ℝ)..1, p.eval x := by
          rw [hp_integral]
          field_simp [hs_ne]
          ring
  simpa [p] using hfinal

/-- Low-degree branch of `stabilityMatrix_quadForm_eq_neg_integral`. -/
private lemma stabilityMatrix_quadForm_eq_neg_integral_of_lt
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (q : ℝ[X]) (hqsmall : q.natDegree < s - 1)
    (hzero : ∀ r : ℝ[X], r.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * r).eval x = 0) :
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      -2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x := by
  dsimp
  have hquad_zero :
      ∑ i : Fin s, ∑ j : Fin s,
        q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j) = 0 := by
    exact algStabMatrix_poly_bilinear_zero t hcoll hAlg q q (by omega) (by omega) (by omega)
  have hint_zero : ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := hzero q hqsmall
  rw [hquad_zero, hint_zero]
  ring

/-- Top-degree branch of `stabilityMatrix_quadForm_eq_neg_integral`.

The remainder term is reduced to degree `< s - 1`, and every term except the
pure `X^(s - 1)` defect should vanish. -/
private lemma stabilityMatrix_quadForm_eq_neg_integral_of_eq
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (q : ℝ[X]) (hqtop : q.natDegree = s - 1)
    (hzero : ∀ r : ℝ[X], r.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * r).eval x = 0) :
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      -2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x := by
  dsimp
  by_cases hs1 : s = 1
  · subst hs1
    let a : ℝ := q.leadingCoeff
    have hqC0 : q = Polynomial.C (q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by simpa using hqtop)
    have hlead0 : q.leadingCoeff = q.coeff 0 := by
      rw [Polynomial.leadingCoeff, hqtop]
    have hqC : q = Polynomial.C a := by
      dsimp [a]
      rwa [← hlead0] at hqC0
    rw [hqC]
    calc
      ∑ i : Fin 1, ∑ j : Fin 1,
          (Polynomial.C a).eval (t.c i) * t.algStabMatrix i j * (Polynomial.C a).eval (t.c j)
        = a ^ 2 *
            (∑ i : Fin 1, ∑ j : Fin 1,
              t.c i ^ (1 - 1) * t.algStabMatrix i j * t.c j ^ (1 - 1)) := by
            simp [Polynomial.eval_C]
            ring
      _ = a ^ 2 *
            (-2 * ((1 : ℝ) / (1 : ℝ)) *
              ∫ x in (0 : ℝ)..1, ((nodePoly t) * Polynomial.X ^ (1 - 1)).eval x) := by
            rw [algStabMatrix_top_monomial_eq_neg_integral t hcoll hAlg]
            norm_num
      _ = -2 * ((Polynomial.C a).leadingCoeff / ((1 : ℕ) : ℝ)) *
            ∫ x in (0 : ℝ)..1, ((nodePoly t) * Polynomial.C a).eval x := by
            simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
            ring
  · have hs : 1 < s := by
      have hs0 : 0 < s := hcoll.1
      omega
    let a : ℝ := q.leadingCoeff
    let r : ℝ[X] := q - Polynomial.C a * Polynomial.X ^ (s - 1)
    have hrsmall : r.natDegree < s - 1 := by
      exact sub_leading_term_natDegree_lt hs q hqtop
    have hXdeg : (Polynomial.X ^ (s - 1) : ℝ[X]).natDegree < s := by
      rw [Polynomial.natDegree_X_pow]
      omega
    have hrr :
        ∑ i : Fin s, ∑ j : Fin s,
          r.eval (t.c i) * t.algStabMatrix i j * r.eval (t.c j) = 0 := by
      exact algStabMatrix_poly_bilinear_zero t hcoll hAlg r r (by omega) (by omega) (by omega)
    have hrX :
        ∑ i : Fin s, ∑ j : Fin s,
          r.eval (t.c i) * t.algStabMatrix i j * t.c j ^ (s - 1) = 0 := by
      convert algStabMatrix_poly_bilinear_zero t hcoll hAlg r (Polynomial.X ^ (s - 1))
        (by omega) hXdeg (by omega) using 1 <;>
        simp [Polynomial.eval_pow, Polynomial.eval_X]
    have hXr :
        ∑ i : Fin s, ∑ j : Fin s,
          t.c i ^ (s - 1) * t.algStabMatrix i j * r.eval (t.c j) = 0 := by
      convert algStabMatrix_poly_bilinear_zero t hcoll hAlg (Polynomial.X ^ (s - 1)) r
        hXdeg (by omega) (by omega) using 1 <;>
        simp [Polynomial.eval_pow, Polynomial.eval_X]
    have hqeval : ∀ i : Fin s, q.eval (t.c i) = r.eval (t.c i) + a * t.c i ^ (s - 1) := by
      intro i
      dsimp [r, a]
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      ring
    have hquad :
        ∑ i : Fin s, ∑ j : Fin s,
          q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j)
          = a ^ 2 *
              (∑ i : Fin s, ∑ j : Fin s,
                t.c i ^ (s - 1) * t.algStabMatrix i j * t.c j ^ (s - 1)) := by
      simp_rw [hqeval, add_mul, mul_add]
      simp_rw [Finset.sum_add_distrib]
      have hrXa :
          ∑ x, ∑ x_1, r.eval (t.c x) * t.algStabMatrix x x_1 * (a * t.c x_1 ^ (s - 1)) =
            a * ∑ x, ∑ x_1, r.eval (t.c x) * t.algStabMatrix x x_1 * t.c x_1 ^ (s - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x_1 hx_1
        ring
      have hXaR :
          ∑ x, ∑ x_1, a * t.c x ^ (s - 1) * t.algStabMatrix x x_1 * r.eval (t.c x_1) =
            a * ∑ x, ∑ x_1, t.c x ^ (s - 1) * t.algStabMatrix x x_1 * r.eval (t.c x_1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x_1 hx_1
        ring
      have hXaXa :
          ∑ x, ∑ x_1, a * t.c x ^ (s - 1) * t.algStabMatrix x x_1 * (a * t.c x_1 ^ (s - 1)) =
            a ^ 2 * ∑ x, ∑ x_1, t.c x ^ (s - 1) * t.algStabMatrix x x_1 * t.c x_1 ^ (s - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x_1 hx_1
        ring
      rw [hrXa, hXaR, hXaXa, hrr, hrX, hXr]
      ring
    have hqsplit : q = r + Polynomial.C a * Polynomial.X ^ (s - 1) := by
      dsimp [r, a]
      ring
    have h_integral :
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x =
          a * ∫ x in (0 : ℝ)..1, ((nodePoly t) * Polynomial.X ^ (s - 1)).eval x := by
      have hfun :
          (fun x : ℝ => ((nodePoly t) * q).eval x) =
            fun x : ℝ =>
              ((nodePoly t) * r).eval x +
                a * ((nodePoly t) * Polynomial.X ^ (s - 1)).eval x := by
        funext x
        rw [hqsplit]
        simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        ring
      rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
      · rw [hzero r hrsmall]
        ring
      · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
      · exact Continuous.intervalIntegrable
          (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
    calc
      ∑ i : Fin s, ∑ j : Fin s,
          q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j)
        = a ^ 2 *
            (∑ i : Fin s, ∑ j : Fin s,
              t.c i ^ (s - 1) * t.algStabMatrix i j * t.c j ^ (s - 1)) := hquad
      _ = a ^ 2 *
            (-2 * ((1 : ℝ) / (s : ℝ)) *
              ∫ x in (0 : ℝ)..1, ((nodePoly t) * Polynomial.X ^ (s - 1)).eval x) := by
            rw [algStabMatrix_top_monomial_eq_neg_integral t hcoll hAlg]
      _ = -2 * (q.leadingCoeff / (s : ℝ)) *
            ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x := by
            rw [h_integral]
            dsimp [a]
            ring

/-- Second-stage sign helper for the transformed `(358c)` bridge.

This packages the quadratic form from `hAlg.posdef_M` as the signed integral
needed for the degree-`s - 1` case, assuming the lower-degree zero statement is
already available. The fundamental blocker remains
`nodePoly_interval_zero_aux_of_algStable`; this helper is only the one-sided
companion used after that zero theorem. -/
lemma stabilityMatrix_quadForm_eq_neg_integral
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (q : ℝ[X]) (hq : q.natDegree ≤ s - 1)
    (hzero : ∀ r : ℝ[X], r.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * r).eval x = 0) :
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      -2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x := by
  by_cases hqsmall : q.natDegree < s - 1
  · exact stabilityMatrix_quadForm_eq_neg_integral_of_lt t hcoll hAlg q hqsmall hzero
  · have hqtop : q.natDegree = s - 1 := by omega
    exact stabilityMatrix_quadForm_eq_neg_integral_of_eq t hcoll hAlg q hqtop hzero

/-- The live `(358c)` sign statement for degree-`s - 1` test polynomials with
positive leading coefficient.

This is the one-sided companion to
`nodePoly_interval_zero_aux_of_algStable`, and is the input needed later to
extract `θ ≥ 0` from the boundary-polynomial description. -/
lemma nodePoly_interval_nonpos_aux_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree = s - 1 → 0 < q.leadingCoeff →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x ≤ 0 := by
  intro q hq hlc
  have hzero := nodePoly_interval_zero_aux_of_algStable t hcoll hAlg
  have hident := stabilityMatrix_quadForm_eq_neg_integral t hcoll hAlg q
    (by simpa [hq]) hzero
  have hpsd := hAlg.posdef_M (fun i => q.eval (t.c i))
  dsimp only at hident
  rw [hident] at hpsd
  have hs_pos : 0 < (s : ℝ) := Nat.cast_pos.mpr hcoll.1
  have hscale_pos : 0 < 2 * (q.leadingCoeff / (s : ℝ)) := by
    positivity
  by_contra hint
  push_neg at hint
  have hneg : -2 * (q.leadingCoeff / (s : ℝ)) *
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x < 0 := by
    have hprod : 0 < 2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x := by
      exact mul_pos hscale_pos hint
    linarith
  linarith

/-- Matrix-to-polynomial bridge for Theorem 358A.

Under the collocation and algebraic-stability hypotheses, the node polynomial is
orthogonal to every polynomial of degree at most `s - 2`, phrased via
`polyMomentN` on `[0,1]`. -/
lemma nodePoly_polyMoment_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 → polyMomentN (2 * s) (nodePoly t * q) = 0 := by
  intro q hq
  have hq' : q.natDegree < s := by
    omega
  rw [polyMomentN_eq_intervalIntegral_of_natDegree_lt (N := 2 * s) (p := (nodePoly t * q))]
  · exact nodePoly_interval_zero_aux_of_algStable t hcoll hAlg q hq
  · exact nodePoly_mul_natDegree_lt t q hq'

/-- Interval-integral form of the node-polynomial orthogonality bridge. -/
lemma nodePoly_interval_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  exact nodePoly_interval_zero_aux_of_algStable t hcoll hAlg

private lemma shiftedLegendrePoly_natDegree (n : ℕ) :
    (shiftedLegendrePoly n).natDegree = n := by
  unfold shiftedLegendrePoly
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  exact Polynomial.natDegree_shiftedLegendre n

private lemma shiftedLegendreStarPoly_natDegree (n : ℕ) :
    (shiftedLegendreStarPoly n).natDegree = n := by
  unfold shiftedLegendreStarPoly
  rw [Polynomial.natDegree_C_mul]
  · exact shiftedLegendrePoly_natDegree n
  · exact pow_ne_zero _ (by norm_num)

private lemma shiftedLegendreStarPoly_leadingCoeff_pos (n : ℕ) :
    0 < (shiftedLegendreStarPoly n).leadingCoeff := by
  unfold shiftedLegendreStarPoly
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  rw [Polynomial.leadingCoeff, shiftedLegendrePoly_natDegree, shiftedLegendrePoly,
    Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    simp
  have hchoose : 0 < ((Nat.choose (n + n) n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left n n)
  simpa [Nat.choose_self, mul_assoc, mul_left_comm, mul_comm, hsign] using hchoose

private lemma shiftedLegendreStarPoly_interval_orthogonal (n : ℕ) :
    ∀ q : ℝ[X], q.natDegree < n →
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * q).eval x = 0 := by
  intro q hq
  rw [← polyMomentN_eq_intervalIntegral_of_natDegree_lt (N := 2 * n)
    (p := (shiftedLegendreStarPoly n) * q)]
  · unfold shiftedLegendreStarPoly
    rw [show Polynomial.C ((-1 : ℝ) ^ n) * shiftedLegendrePoly n * q =
        Polynomial.C ((-1 : ℝ) ^ n) * (shiftedLegendrePoly n * q) by ring]
    rw [polyMomentN_C_mul]
    simpa [shiftedLegendrePoly] using (polyMomentN_shiftedLegendre_mul_zero (s := n) q hq)
  · calc
      ((shiftedLegendreStarPoly n) * q).natDegree
          ≤ (shiftedLegendreStarPoly n).natDegree + q.natDegree := Polynomial.natDegree_mul_le
      _ < n + n := by
            rw [shiftedLegendreStarPoly_natDegree]
            omega
      _ = 2 * n := by ring

private lemma shiftedLegendreStarPoly_sq_intervalIntegral_pos (n : ℕ) :
    0 < ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * (shiftedLegendreStarPoly n)).eval x := by
  have hnonneg :
      0 ≤ ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * (shiftedLegendreStarPoly n)).eval x := by
    simpa [sq, Polynomial.eval_mul] using
      (intervalIntegral.integral_nonneg zero_le_one fun x hx =>
        sq_nonneg ((shiftedLegendreStarPoly n).eval x))
  by_contra hpos
  have hzero :
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * (shiftedLegendreStarPoly n)).eval x = 0 := by
    linarith
  have hpoly_zero : shiftedLegendreStarPoly n = 0 := by
    apply poly_eq_zero_of_intervalIntegral_sq_zero
    simpa [sq, Polynomial.eval_mul] using hzero
  have hlc_pos := shiftedLegendreStarPoly_leadingCoeff_pos n
  simpa [hpoly_zero] using hlc_pos

private lemma orthogonal_degree_eq_scaled_shiftedLegendreStarPoly
    {n : ℕ} {φ : ℝ[X]}
    (hdeg : φ.natDegree = n)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      ∫ x in (0 : ℝ)..1, (φ * q).eval x = 0) :
    ∃ a : ℝ, φ = Polynomial.C a * shiftedLegendreStarPoly n := by
  rcases n with _ | n
  · have hconst : φ = Polynomial.C (φ.coeff 0) := by
      exact Polynomial.eq_C_of_natDegree_le_zero (by simpa [hdeg])
    refine ⟨φ.coeff 0, ?_⟩
    calc
      φ = Polynomial.C (φ.coeff 0) := hconst
      _ = Polynomial.C (φ.coeff 0) * shiftedLegendreStarPoly 0 := by
            simp [shiftedLegendreStarPoly, shiftedLegendrePoly, Polynomial.shiftedLegendre]
  · have hφ_ne : φ ≠ 0 := by
      intro hφ
      subst hφ
      simp at hdeg
    let a : ℝ := φ.leadingCoeff / (shiftedLegendreStarPoly (n + 1)).leadingCoeff
    let r : ℝ[X] := φ - Polynomial.C a * shiftedLegendreStarPoly (n + 1)
    have hstar_ne : shiftedLegendreStarPoly (n + 1) ≠ 0 := by
      intro hstar
      simpa [hstar] using shiftedLegendreStarPoly_leadingCoeff_pos (n + 1)
    have hstar_lc_ne : (shiftedLegendreStarPoly (n + 1)).leadingCoeff ≠ 0 := by
      exact (Polynomial.leadingCoeff_ne_zero).2 hstar_ne
    have ha_ne : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero ((Polynomial.leadingCoeff_ne_zero).2 hφ_ne) hstar_lc_ne
    have hscaled_ne : Polynomial.C a * shiftedLegendreStarPoly (n + 1) ≠ 0 := by
      exact mul_ne_zero (by simpa using ha_ne) hstar_ne
    have hscaled_deg :
        (Polynomial.C a * shiftedLegendreStarPoly (n + 1)).natDegree = n + 1 := by
      rw [Polynomial.natDegree_C_mul_of_mul_ne_zero]
      · rw [shiftedLegendreStarPoly_natDegree]
      · exact mul_ne_zero ha_ne hstar_lc_ne
    have hlc_eq :
        φ.leadingCoeff = (Polynomial.C a * shiftedLegendreStarPoly (n + 1)).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      dsimp [a]
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hstar_lc_ne, mul_one]
    have hr_deg :
        r.natDegree < n + 1 := by
      have hdeg_eq :
          φ.degree = (Polynomial.C a * shiftedLegendreStarPoly (n + 1)).degree := by
        rw [Polynomial.degree_eq_natDegree hφ_ne, Polynomial.degree_eq_natDegree hscaled_ne,
          hdeg, hscaled_deg]
      have hdeg_lt :
          (φ - Polynomial.C a * shiftedLegendreStarPoly (n + 1)).degree < φ.degree := by
        exact Polynomial.degree_sub_lt hdeg_eq hφ_ne hlc_eq
      by_cases hr_zero : r = 0
      · rw [hr_zero]
        simpa using Nat.succ_pos n
      · dsimp [r] at hr_zero
        rwa [Polynomial.degree_eq_natDegree hr_zero, Polynomial.degree_eq_natDegree hφ_ne,
          hdeg, Nat.cast_lt] at hdeg_lt
    have hr_orth :
        ∀ q : ℝ[X], q.natDegree < n + 1 →
          ∫ x in (0 : ℝ)..1, (r * q).eval x = 0 := by
      intro q hq
      have hfun :
          (fun x : ℝ => (r * q).eval x) =
            fun x : ℝ =>
              (φ * q).eval x - a * ((shiftedLegendreStarPoly (n + 1) * q).eval x) := by
        funext x
        dsimp [r]
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
        ring
      rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
      · rw [horth q hq, shiftedLegendreStarPoly_interval_orthogonal (n + 1) q hq]
        ring
      · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
      · exact Continuous.intervalIntegrable
          (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
    have hr_zero : r = 0 := by
      apply poly_eq_zero_of_intervalIntegral_sq_zero
      simpa [sq, Polynomial.eval_mul] using hr_orth r hr_deg
    refine ⟨a, ?_⟩
    dsimp [r] at hr_zero
    exact sub_eq_zero.mp hr_zero

/-- A degree-`s` polynomial with positive leading coefficient and orthogonal to
all polynomials of degree at most `s - 2` must be a positive multiple of
`P_s^* - θ P_{s-1}^*`. -/
lemma orthogonal_degree_eq_boundaryPoly
    (hs : 0 < s) {φ : ℝ[X]}
    (hdeg : φ.natDegree = s) (hlc : 0 < φ.leadingCoeff)
    (horth : ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, (φ * q).eval x = 0) :
    ∃ θ a : ℝ, 0 < a ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ := by
  let a : ℝ := φ.leadingCoeff / (shiftedLegendreStarPoly s).leadingCoeff
  let r : ℝ[X] := φ - Polynomial.C a * shiftedLegendreStarPoly s
  have hφ_ne : φ ≠ 0 := by
    intro hφ
    subst hφ
    simp at hdeg
    omega
  have hstar_ne : shiftedLegendreStarPoly s ≠ 0 := by
    intro hstar
    simpa [hstar] using shiftedLegendreStarPoly_leadingCoeff_pos s
  have hstar_lc_ne : (shiftedLegendreStarPoly s).leadingCoeff ≠ 0 := by
    exact (Polynomial.leadingCoeff_ne_zero).2 hstar_ne
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos hlc (shiftedLegendreStarPoly_leadingCoeff_pos s)
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hscaled_ne : Polynomial.C a * shiftedLegendreStarPoly s ≠ 0 := by
    exact mul_ne_zero (by simpa using ha_ne) hstar_ne
  have hscaled_deg : (Polynomial.C a * shiftedLegendreStarPoly s).natDegree = s := by
    rw [Polynomial.natDegree_C_mul_of_mul_ne_zero]
    · rw [shiftedLegendreStarPoly_natDegree]
    · exact mul_ne_zero ha_ne hstar_lc_ne
  have hlc_eq :
      φ.leadingCoeff = (Polynomial.C a * shiftedLegendreStarPoly s).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp [a]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hstar_lc_ne, mul_one]
  have hr_deg_lt_s : r.natDegree < s := by
    have hdeg_eq :
        φ.degree = (Polynomial.C a * shiftedLegendreStarPoly s).degree := by
      rw [Polynomial.degree_eq_natDegree hφ_ne, Polynomial.degree_eq_natDegree hscaled_ne,
        hdeg, hscaled_deg]
    have hdeg_lt :
        (φ - Polynomial.C a * shiftedLegendreStarPoly s).degree < φ.degree := by
      exact Polynomial.degree_sub_lt hdeg_eq hφ_ne hlc_eq
    by_cases hr_zero : r = 0
    · rw [hr_zero]
      simpa using hs
    · dsimp [r] at hr_zero
      rwa [Polynomial.degree_eq_natDegree hr_zero, Polynomial.degree_eq_natDegree hφ_ne,
        hdeg, Nat.cast_lt] at hdeg_lt
  have hr_orth :
      ∀ q : ℝ[X], q.natDegree < s - 1 →
        ∫ x in (0 : ℝ)..1, (r * q).eval x = 0 := by
    intro q hq
    have hfun :
        (fun x : ℝ => (r * q).eval x) =
          fun x : ℝ =>
            (φ * q).eval x - a * ((shiftedLegendreStarPoly s * q).eval x) := by
      funext x
      dsimp [r]
      simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
      ring
    rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
    · rw [horth q hq, shiftedLegendreStarPoly_interval_orthogonal s q (by omega)]
      ring
    · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
    · exact Continuous.intervalIntegrable
        (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
  by_cases hr_zero : r = 0
  · refine ⟨0, a, ha_pos, ?_⟩
    have hphi : φ = Polynomial.C a * shiftedLegendreStarPoly s := sub_eq_zero.mp (by
      simpa [r] using hr_zero)
    simpa [algStabilityBoundaryPoly] using hphi
  · have hr_not_lt : ¬ r.natDegree < s - 1 := by
      intro hr_lt
      have hr_zero' : r = 0 := by
        apply poly_eq_zero_of_intervalIntegral_sq_zero
        simpa [sq, Polynomial.eval_mul] using hr_orth r hr_lt
      exact hr_zero hr_zero'
    have hr_deg : r.natDegree = s - 1 := by
      omega
    obtain ⟨b, hr_eq⟩ :=
      orthogonal_degree_eq_scaled_shiftedLegendreStarPoly (hdeg := hr_deg) hr_orth
    refine ⟨-b / a, a, ha_pos, ?_⟩
    calc
      φ = r + Polynomial.C a * shiftedLegendreStarPoly s := by
            dsimp [r]
            ring
      _ = Polynomial.C b * shiftedLegendreStarPoly (s - 1) + Polynomial.C a * shiftedLegendreStarPoly s := by
            rw [hr_eq]
      _ = Polynomial.C a * algStabilityBoundaryPoly s (-b / a) := by
            ext k
            simp [algStabilityBoundaryPoly, ha_ne, mul_assoc, mul_left_comm, mul_comm]
            field_simp [ha_ne]
            ring

/-- Sign extraction for the `θ` parameter in the boundary polynomial.

This is the theorem-local version of the step obtained by testing against
`P_{s-1}^*`. -/
lemma boundary_theta_nonneg_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    {θ a : ℝ} (ha : 0 < a)
    (hnode : nodePoly t = Polynomial.C a * algStabilityBoundaryPoly s θ) :
    0 ≤ θ := by
  let q : ℝ[X] := shiftedLegendreStarPoly (s - 1)
  have hq_deg : q.natDegree = s - 1 := by
    dsimp [q]
    exact shiftedLegendreStarPoly_natDegree (s - 1)
  have hq_lc : 0 < q.leadingCoeff := by
    dsimp [q]
    exact shiftedLegendreStarPoly_leadingCoeff_pos (s - 1)
  have hnode_nonpos :
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x ≤ 0 :=
    nodePoly_interval_nonpos_aux_of_algStable t hcoll hAlg q hq_deg hq_lc
  have horth :
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly s) * q).eval x = 0 := by
    dsimp [q]
    have hq_lt : (shiftedLegendreStarPoly (s - 1)).natDegree < s := by
      rw [shiftedLegendreStarPoly_natDegree]
      simpa using Nat.sub_lt_of_pos_le (a := 1) (b := s) (by decide) (Nat.succ_le_of_lt hcoll.1)
    exact shiftedLegendreStarPoly_interval_orthogonal s (shiftedLegendreStarPoly (s - 1)) hq_lt
  have hboundary :
      ∫ x in (0 : ℝ)..1, ((algStabilityBoundaryPoly s θ) * q).eval x =
        -θ * ∫ x in (0 : ℝ)..1, (q * q).eval x := by
    have hfun :
        (fun x : ℝ => ((algStabilityBoundaryPoly s θ) * q).eval x) =
          fun x : ℝ =>
            ((shiftedLegendreStarPoly s) * q).eval x -
              θ * ((q * q).eval x) := by
      funext x
      dsimp [q]
      simp [algStabilityBoundaryPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
      ring
    rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, horth]
    · ring
    · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
    · exact Continuous.intervalIntegrable
        (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
  have hnode_int :
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x =
        a * (-θ * ∫ x in (0 : ℝ)..1, (q * q).eval x) := by
    rw [hnode]
    have hfun :
        (fun x : ℝ => ((Polynomial.C a * algStabilityBoundaryPoly s θ) * q).eval x) =
          fun x : ℝ => a * ((algStabilityBoundaryPoly s θ * q).eval x) := by
      funext x
      simp [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hboundary]
  have hsq_pos : 0 < ∫ x in (0 : ℝ)..1, (q * q).eval x := by
    dsimp [q]
    exact shiftedLegendreStarPoly_sq_intervalIntegral_pos (s - 1)
  have hprod_nonneg : 0 ≤ a * θ * ∫ x in (0 : ℝ)..1, (q * q).eval x := by
    linarith [hnode_nonpos, hnode_int]
  by_contra hθ
  push_neg at hθ
  have hneg : a * θ * ∫ x in (0 : ℝ)..1, (q * q).eval x < 0 := by
    have haθ_neg : a * θ < 0 := by
      exact mul_neg_of_pos_of_neg ha hθ
    exact mul_neg_of_neg_of_pos haθ_neg hsq_pos
  linarith

/-- Theorem 358A, `only if` direction. -/
theorem thm_358A_only_if
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    t.HasAlgStabilityBoundaryNodes := by
  obtain ⟨θ, a, ha, hnode⟩ :
      ∃ θ a : ℝ, 0 < a ∧ nodePoly t = Polynomial.C a * algStabilityBoundaryPoly s θ := by
    apply orthogonal_degree_eq_boundaryPoly
    · exact hcoll.1
    · exact nodePoly_natDegree t
    · exact nodePoly_leadingCoeff_pos t
    · exact nodePoly_interval_orthogonal_of_algStable t hcoll hAlg
  refine ⟨θ, boundary_theta_nonneg_of_algStable t hcoll hAlg ha hnode, ?_⟩
  intro i
  have hEval := congrArg (fun p : ℝ[X] => p.eval (t.c i)) hnode
  have hEval' : 0 = a * (algStabilityBoundaryPoly s θ).eval (t.c i) := by
    simpa [Polynomial.eval_mul, Polynomial.eval_C] using
      (nodePoly_eval_node t i).symm.trans hEval
  have ha_ne : a ≠ 0 := by linarith
  exact (mul_eq_zero.mp hEval'.symm).resolve_left ha_ne

/-! ### Reverse-direction scaffold for Theorem 358A -/

/-- The Lagrange basis polynomial `L_i` for the collocation nodes. -/
noncomputable def lagrangeBasisPoly (t : ButcherTableau s) (i : Fin s) : ℝ[X] :=
  Lagrange.basis (Finset.univ : Finset (Fin s)) t.c i

/-- Under `B(s)`, the weight `b_i` is the integral of the i-th Lagrange basis polynomial. -/
lemma weight_eq_integral_lagrange
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (i : Fin s) :
    t.b i = ∫ x in (0 : ℝ)..1, (lagrangeBasisPoly t i).eval x := by
  obtain ⟨hs, hB, hC, h_inj⟩ := hcoll
  have h_sum : ∑ j : Fin s, t.b j * (t.lagrangeBasisPoly i).eval (t.c j) = t.b i := by
    rw [Finset.sum_eq_single i]
    · unfold ButcherTableau.lagrangeBasisPoly
      rw [Lagrange.eval_basis_self] <;> aesop
    · simp +decide [ButcherTableau.lagrangeBasisPoly, Lagrange.basis]
      intro j hj
      rw [Polynomial.eval_prod]
      exact Or.inr <|
        Finset.prod_eq_zero (Finset.mem_erase_of_ne_of_mem hj <| Finset.mem_univ _)
          <| by simp +decide [Lagrange.basisDivisor]
    · aesop
  have h_poly_exact :
      ∀ p : Polynomial ℝ, p.natDegree < s →
        ∑ j : Fin s, t.b j * p.eval (t.c j) = ∫ x in (0 : ℝ)..1, p.eval x := by
    intro p hp
    have h_monomial :
        ∀ k : ℕ, k < s →
          ∑ j : Fin s, t.b j * (t.c j) ^ k = ∫ x in (0 : ℝ)..1, x ^ k := by
      intro k hk
      specialize hB (k + 1)
      aesop
    simp_all +decide [Polynomial.eval_eq_sum_range]
    simp +decide [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul,
      intervalIntegral.integral_finset_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [← h_monomial _ (by linarith [Finset.mem_range.mp ‹_›])]
      simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
  rw [← h_sum, h_poly_exact]
  rw [ButcherTableau.lagrangeBasisPoly]
  rw [Lagrange.natDegree_basis] <;> aesop

/-- Under `C(s)`, the coefficient `A i j` is the integral of the j-th Lagrange basis
up to the i-th node. -/
lemma A_eq_integral_lagrange
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (i j : Fin s) :
    t.A i j = ∫ x in (0 : ℝ)..t.c i, (lagrangeBasisPoly t j).eval x := by
  revert j
  have h_poly_integral :
      ∀ r : Polynomial ℝ, r.degree < s →
        ∑ j : Fin s, t.A i j * r.eval (t.c j) = ∫ x in (0 : ℝ)..t.c i, r.eval x := by
    intro r hr
    have h_basis :
        ∀ k : ℕ, k < s →
          ∑ j : Fin s, t.A i j * (t.c j) ^ k = (t.c i) ^ (k + 1) / (k + 1) := by
      exact fun k hk => by
        simpa using hcoll.2.2.1 (k + 1) (by linarith) (by linarith) i
    have h_integral_linear :
        ∫ x in (0 : ℝ)..t.c i, r.eval x =
          ∑ k ∈ r.support, r.coeff k * ∫ x in (0 : ℝ)..t.c i, x ^ k := by
      simp +decide [Polynomial.eval_eq_sum, Polynomial.sum_def]
      rw [intervalIntegral.integral_finset_sum] <;> aesop
    simp_all +decide [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp +decide only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [← h_basis _ (by
        linarith [Polynomial.le_natDegree_of_mem_supp _ ‹_›,
          (Polynomial.natDegree_lt_iff_degree_lt (by aesop)).2 hr])]
      simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
  intro j
  convert h_poly_integral (Lagrange.basis (Finset.univ : Finset (Fin s)) t.c j) _ using 1
  · rw [Finset.sum_eq_single j]
    · simp +decide [Lagrange.basis]
      simp +decide [Polynomial.eval_prod, Finset.prod_eq_zero_iff, Lagrange.basisDivisor]
      rw [Finset.prod_eq_one fun x hx => by
        rw [inv_mul_cancel₀]
        exact sub_ne_zero_of_ne <| by
          intro h
          have := hcoll.2.2.2
          have := @this j x
          aesop]
      ring
    · simp +contextual [Lagrange.basis]
      intro k hk
      rw [Polynomial.eval_prod]
      exact Or.inr <|
        Finset.prod_eq_zero (Finset.mem_erase_of_ne_of_mem hk <| Finset.mem_univ _)
          <| by simp +decide [Lagrange.basisDivisor]
    · aesop
  · rw [Lagrange.degree_basis] <;> norm_num
    · exact hcoll.1
    · exact hcoll.2.2.2

/-- `B(s)` gives quadrature exactness for polynomials of degree `< s`. -/
lemma B_quadrature_exact
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (r : ℝ[X])
    (hr : r.natDegree < s) :
    ∑ i : Fin s, t.b i * r.eval (t.c i) =
      ∫ x in (0 : ℝ)..1, r.eval x := by
  have h_linear :
      ∫ x in (0 : ℝ)..1, r.eval x =
        ∑ k ∈ Finset.range (r.natDegree + 1), r.coeff k * ∫ x in (0 : ℝ)..1, x ^ k := by
    norm_num [Polynomial.eval_eq_sum_range]
    rw [intervalIntegral.integral_finset_sum] <;> norm_num
  have h_linear_sum :
      ∑ i, t.b i * r.eval (t.c i) =
        ∑ k ∈ Finset.range (r.natDegree + 1), r.coeff k * ∑ i, t.b i * (t.c i) ^ k := by
    simp +decide [Polynomial.eval_eq_sum_range, Finset.mul_sum, mul_assoc, mul_comm,
      mul_left_comm]
    exact Finset.sum_comm
  have hB := hcoll.2.1
  exact h_linear_sum.trans <| h_linear.symm ▸
    Finset.sum_congr rfl fun k hk => by
      have := hB (k + 1) (by linarith [Finset.mem_range.mp hk]) (by linarith [Finset.mem_range.mp hk])
      aesop

/-- Shifted Legendre orthogonality on `[0,1]` for the textbook-sign polynomials. -/
lemma shiftedLegendre_orthogonal_integral
    (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * q).eval x = 0 := by
  exact shiftedLegendreStarPoly_interval_orthogonal n q hq

/-- The boundary polynomial is orthogonal to all polynomials of degree `≤ s - 2`. -/
lemma boundary_poly_orthogonal
    (θ : ℝ) (q : ℝ[X]) (hq : q.natDegree + 2 ≤ s) :
    ∫ x in (0 : ℝ)..1, (algStabilityBoundaryPoly s θ * q).eval x = 0 := by
  have hs :
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly s) * q).eval x = 0 := by
    exact shiftedLegendre_orthogonal_integral s q (by omega)
  have hs_prev :
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly (s - 1)) * q).eval x = 0 := by
    exact shiftedLegendre_orthogonal_integral (s - 1) q (by omega)
  have hfun :
      (fun x : ℝ => (algStabilityBoundaryPoly s θ * q).eval x) =
        fun x : ℝ =>
          ((shiftedLegendreStarPoly s) * q).eval x -
            θ * (((shiftedLegendreStarPoly (s - 1)) * q).eval x) := by
    funext x
    simp [algStabilityBoundaryPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
    ring
  rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, hs, hs_prev]
  · ring
  · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
  · exact Continuous.intervalIntegrable
      (Continuous.mul continuous_const (Polynomial.continuous _)) _ _

/-- Under the boundary-node hypothesis, the node polynomial is a positive scalar multiple of
the boundary polynomial. -/
lemma nodePoly_eq_const_mul_boundary
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    ∃ θ κ : ℝ, 0 ≤ θ ∧ 0 < κ ∧
      nodePoly t = Polynomial.C κ * algStabilityBoundaryPoly s θ := by
  obtain ⟨θ, hθ_nonneg, hθ_root⟩ := hroot
  have hs_pos : 0 < s := hcoll.1
  have hlower_deg :
      (Polynomial.C θ * shiftedLegendreStarPoly (s - 1)).natDegree <
        (shiftedLegendreStarPoly s).natDegree := by
    calc
      (Polynomial.C θ * shiftedLegendreStarPoly (s - 1)).natDegree
          ≤ (shiftedLegendreStarPoly (s - 1)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = s - 1 := shiftedLegendreStarPoly_natDegree (s - 1)
      _ < s := by omega
      _ = (shiftedLegendreStarPoly s).natDegree := (shiftedLegendreStarPoly_natDegree s).symm
  have hboundary_natDegree : (algStabilityBoundaryPoly s θ).natDegree = s := by
    unfold algStabilityBoundaryPoly
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlower_deg,
      shiftedLegendreStarPoly_natDegree]
  have hboundary_topCoeff :
      (algStabilityBoundaryPoly s θ).coeff s = (shiftedLegendreStarPoly s).coeff s := by
    unfold algStabilityBoundaryPoly
    rw [Polynomial.coeff_sub]
    have hzero :
        (Polynomial.C θ * shiftedLegendreStarPoly (s - 1)).coeff s = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      calc
        (Polynomial.C θ * shiftedLegendreStarPoly (s - 1)).natDegree
            ≤ (shiftedLegendreStarPoly (s - 1)).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = s - 1 := shiftedLegendreStarPoly_natDegree (s - 1)
        _ < s := by omega
    simp [hzero]
  have hboundary_lc_pos : 0 < (algStabilityBoundaryPoly s θ).leadingCoeff := by
    rw [← Polynomial.coeff_natDegree (p := algStabilityBoundaryPoly s θ), hboundary_natDegree,
      hboundary_topCoeff]
    simpa [Polynomial.leadingCoeff, shiftedLegendreStarPoly_natDegree] using
      shiftedLegendreStarPoly_leadingCoeff_pos s
  let κ : ℝ := 1 / (algStabilityBoundaryPoly s θ).leadingCoeff
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact one_div_pos.mpr hboundary_lc_pos
  have hscaled_lc : (Polynomial.C κ * algStabilityBoundaryPoly s θ).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp [κ]
    exact one_div_mul_cancel (ne_of_gt hboundary_lc_pos)
  have hscaled_ne : Polynomial.C κ * algStabilityBoundaryPoly s θ ≠ 0 := by
    exact mul_ne_zero (by simpa using ne_of_gt hκ_pos) (by
      intro hzero
      simpa [hzero] using hboundary_lc_pos)
  have hscaled_deg :
      (Polynomial.C κ * algStabilityBoundaryPoly s θ).degree = s := by
    rw [Polynomial.degree_eq_natDegree hscaled_ne, Polynomial.natDegree_C_mul (ne_of_gt hκ_pos),
      hboundary_natDegree]
  have hinj : Set.InjOn t.c (Finset.univ : Finset (Fin s)) := by
    intro i _ j _ hij
    exact hcoll.2.2.2 hij
  have h_eval :
      ∀ i ∈ (Finset.univ : Finset (Fin s)),
        (nodePoly t).eval (t.c i) = (Polynomial.C κ * algStabilityBoundaryPoly s θ).eval (t.c i) := by
    intro i hi
    rw [nodePoly_eval_node]
    simp [Polynomial.eval_mul, Polynomial.eval_C, hθ_root i]
  refine ⟨θ, κ, hθ_nonneg, hκ_pos, ?_⟩
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (s := (Finset.univ : Finset (Fin s)))
    (v := t.c) hinj
  · simpa [Finset.card_univ] using
      (show (nodePoly t).degree ≤ (s : WithBot ℕ) by
        rw [Polynomial.degree_eq_natDegree (nodePoly_monic t).ne_zero, nodePoly_natDegree t])
  · simpa [Finset.card_univ] using
      (show (nodePoly t).degree = (Polynomial.C κ * algStabilityBoundaryPoly s θ).degree by
        rw [Polynomial.degree_eq_natDegree (nodePoly_monic t).ne_zero, nodePoly_natDegree t,
          hscaled_deg])
  · simpa [(nodePoly_monic t).leadingCoeff, hscaled_lc]
  · exact h_eval

/-- Under the boundary-node hypothesis, the node polynomial is orthogonal to all polynomials
of degree `≤ s - 2`. -/
lemma nodePoly_orthogonal_low_degree
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes)
    (q : ℝ[X]) (hq : q.natDegree + 2 ≤ s) :
    ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
  obtain ⟨θ, κ, hθ_nonneg, hκ_pos, hnode⟩ := nodePoly_eq_const_mul_boundary t hcoll hroot
  rw [hnode]
  have hfun :
      (fun x : ℝ => ((Polynomial.C κ * algStabilityBoundaryPoly s θ) * q).eval x) =
        fun x : ℝ => κ * ((algStabilityBoundaryPoly s θ * q).eval x) := by
    funext x
    simp [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, boundary_poly_orthogonal θ q hq]
  ring

/-- Boundary nodes upgrade the quadrature rule to exactness on degree `≤ 2s - 2`
polynomials. -/
lemma quadrature_exact_of_boundary
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) (r : ℝ[X])
    (hr : r.natDegree ≤ 2 * s - 2) :
    ∑ i : Fin s, t.b i * r.eval (t.c i) =
      ∫ x in (0 : ℝ)..1, r.eval x := by
  set np := nodePoly t with hnp_def
  set q := r /ₘ np with hq_def
  set rem := r %ₘ np with hrem_def
  have hmonic : np.Monic := nodePoly_monic t
  have hs_pos : 0 < s := hcoll.1
  have hnp_ne_one : np ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [nodePoly_natDegree] at hdeg
    simp at hdeg
    omega
  have hdiv : rem + np * q = r := Polynomial.modByMonic_add_div r hmonic
  have hrem_deg : rem.natDegree < s := by
    calc
      rem.natDegree < np.natDegree := Polynomial.natDegree_modByMonic_lt r hmonic hnp_ne_one
      _ = s := nodePoly_natDegree t
  have heval : ∀ i : Fin s, r.eval (t.c i) = rem.eval (t.c i) := by
    intro i
    have h := congrArg (fun p => p.eval (t.c i)) hdiv
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at h
    rw [hnp_def, nodePoly_eval_node] at h
    linarith
  have hsum :
      ∑ i : Fin s, t.b i * r.eval (t.c i) = ∑ i : Fin s, t.b i * rem.eval (t.c i) := by
    congr 1
    ext i
    rw [heval]
  have hrem_exact :
      ∑ i : Fin s, t.b i * rem.eval (t.c i) = ∫ x in (0 : ℝ)..1, rem.eval x :=
    B_quadrature_exact t hcoll rem hrem_deg
  have horth : ∫ x in (0 : ℝ)..1, (np * q).eval x = 0 := by
    by_cases hq_zero : q = 0
    · simp [hq_zero]
    · have hq_deg : q.natDegree + 2 ≤ s := by
        have hr_nonzero : r ≠ 0 := by
          intro hr_zero
          apply hq_zero
          simp [hq_def, hr_zero]
        have hr_ge_s : s ≤ r.natDegree := by
          by_contra hlt
          apply hq_zero
          rw [hq_def, (Polynomial.divByMonic_eq_zero_iff hmonic).2]
          simpa [hnp_def, nodePoly_natDegree t,
            Polynomial.degree_eq_natDegree hr_nonzero,
            Polynomial.degree_eq_natDegree hmonic.ne_zero] using Nat.not_le.mp hlt
        rw [hq_def, Polynomial.natDegree_divByMonic r hmonic, nodePoly_natDegree]
        omega
      exact nodePoly_orthogonal_low_degree t hcoll hroot q hq_deg
  have hint_split :
      ∫ x in (0 : ℝ)..1, r.eval x =
        (∫ x in (0 : ℝ)..1, rem.eval x) + ∫ x in (0 : ℝ)..1, (np * q).eval x := by
    have hfun : (fun x : ℝ => r.eval x) = fun x => rem.eval x + (np * q).eval x := by
      ext x
      have h := congrArg (fun p => p.eval x) hdiv
      simp only [Polynomial.eval_add] at h
      linarith
    rw [hfun, intervalIntegral.integral_add
      (Continuous.intervalIntegrable (Polynomial.continuous rem) _ _)
      (Continuous.intervalIntegrable (Polynomial.continuous (np * q)) _ _)]
  rw [hsum, hrem_exact, hint_split, horth]
  simp

/-- The collocation weights are nonnegative under the boundary-node hypothesis. -/
lemma weights_nonneg_of_boundary
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    ∀ i : Fin s, 0 ≤ t.b i := by
  intro i
  have h_sum : ∑ j, t.b j * (lagrangeBasisPoly t i).eval (t.c j) ^ 2 = t.b i := by
    unfold ButcherTableau.lagrangeBasisPoly
    rw [Finset.sum_eq_single i] <;> simp +contextual [Lagrange.basis]
    · simp +decide [Lagrange.basisDivisor, Polynomial.eval_prod]
      rw [Finset.prod_congr rfl fun x hx => by
        rw [inv_mul_cancel₀]
        exact sub_ne_zero_of_ne <| by
          intro h
          have := hcoll.2.2.2 h
          aesop]
      norm_num
    · exact fun j hj => Or.inr <| by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase_of_ne_of_mem hj <| Finset.mem_univ _)
          <| by simp +decide [Lagrange.basisDivisor]
  have h_integral :
      ∑ j, t.b j * (lagrangeBasisPoly t i).eval (t.c j) ^ 2 =
        ∫ x in (0 : ℝ)..1, (lagrangeBasisPoly t i).eval x ^ 2 := by
    convert quadrature_exact_of_boundary t hcoll hroot ((lagrangeBasisPoly t i) ^ 2) _ using 1
    · norm_num [Polynomial.eval_pow]
    · norm_num
    · rw [Polynomial.natDegree_pow,
        show t.lagrangeBasisPoly i = Lagrange.basis (Finset.univ : Finset (Fin s)) t.c i from rfl]
      rw [Lagrange.natDegree_basis] <;> norm_num [hcoll.2.2.2]
      omega
  exact h_sum ▸ h_integral ▸
    intervalIntegral.integral_nonneg (by norm_num) fun x hx => sq_nonneg _

/-- The mixed moment `∫ P_{s-1}^*(x) x^(s-1) dx` is positive. -/
lemma shiftedLegendre_mul_Xpow_integral_pos (n : ℕ) :
    0 <
      ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly n) * (Polynomial.X ^ n)).eval x := by
  rcases n with _ | n
  · simp [shiftedLegendreStarPoly, shiftedLegendrePoly, Polynomial.shiftedLegendre]
  · let P : ℝ[X] := shiftedLegendreStarPoly (n + 1)
    let a : ℝ := 1 / P.leadingCoeff
    let r : ℝ[X] := (Polynomial.X : ℝ[X]) ^ (n + 1) - Polynomial.C a * P
    have hP_lc_pos : 0 < P.leadingCoeff := by
      dsimp [P]
      exact shiftedLegendreStarPoly_leadingCoeff_pos (n + 1)
    have ha_pos : 0 < a := by
      dsimp [a]
      exact one_div_pos.mpr hP_lc_pos
    have hscaled_ne : Polynomial.C a * P ≠ 0 := by
      apply mul_ne_zero (by simpa using ne_of_gt ha_pos)
      intro hP_zero
      simpa [P, hP_zero] using hP_lc_pos
    have hscaled_natDegree : (Polynomial.C a * P).natDegree = n + 1 := by
      rw [Polynomial.natDegree_C_mul (ne_of_gt ha_pos)]
      dsimp [P]
      exact shiftedLegendreStarPoly_natDegree (n + 1)
    have hlc_eq :
        (((Polynomial.X : ℝ[X]) ^ (n + 1)).leadingCoeff) = (Polynomial.C a * P).leadingCoeff := by
      rw [Polynomial.leadingCoeff_X_pow, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      dsimp [a]
      field_simp [ne_of_gt hP_lc_pos]
    have hr_deg : r.natDegree < n + 1 := by
      have hdeg_eq : ((Polynomial.X : ℝ[X]) ^ (n + 1)).degree = (Polynomial.C a * P).degree := by
        rw [Polynomial.degree_eq_natDegree (pow_ne_zero _ Polynomial.X_ne_zero),
          Polynomial.natDegree_X_pow, Polynomial.degree_eq_natDegree hscaled_ne, hscaled_natDegree]
      have hdeg_lt : r.degree < ((Polynomial.X : ℝ[X]) ^ (n + 1)).degree := by
        dsimp [r]
        exact Polynomial.degree_sub_lt hdeg_eq (pow_ne_zero _ Polynomial.X_ne_zero) hlc_eq
      by_cases hr_zero : r = 0
      · rw [hr_zero]
        simpa using Nat.succ_pos n
      · dsimp [r] at hr_zero
        rwa [Polynomial.degree_eq_natDegree hr_zero,
          Polynomial.degree_eq_natDegree (pow_ne_zero _ Polynomial.X_ne_zero),
          Polynomial.natDegree_X_pow, Nat.cast_lt] at hdeg_lt
    have horth : ∫ x in (0 : ℝ)..1, (P * r).eval x = 0 := by
      dsimp [P]
      exact shiftedLegendreStarPoly_interval_orthogonal (n + 1) r hr_deg
    have hsq_pos : 0 < ∫ x in (0 : ℝ)..1, (P * P).eval x := by
      dsimp [P]
      exact shiftedLegendreStarPoly_sq_intervalIntegral_pos (n + 1)
    have hfun :
        (fun x : ℝ => (P * ((Polynomial.X : ℝ[X]) ^ (n + 1))).eval x) =
          fun x : ℝ => a * ((P * P).eval x) + (P * r).eval x := by
      funext x
      dsimp [r]
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C]
      ring
    rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, horth]
    · have hpos : 0 < a * ∫ x in (0 : ℝ)..1, (P * P).eval x := mul_pos ha_pos hsq_pos
      linarith
    · exact Continuous.intervalIntegrable
        (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
    · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _

/-- For boundary nodes, the degree-`2s-1` quadrature error is nonnegative whenever the
leading coefficient is nonnegative. This is the reverse-direction substitute for the
overgeneralized artifact lemma. -/
lemma quadrature_error_pQ_nonneg_of_boundary
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) (r : ℝ[X])
    (hr : r.natDegree ≤ 2 * s - 1) (hlc : 0 ≤ r.leadingCoeff) :
    0 ≤ ∑ i : Fin s, t.b i * r.eval (t.c i) -
      ∫ x in (0 : ℝ)..1, r.eval x := by
  obtain ⟨θ, κ, hθ_nonneg, hκ_pos, hnode⟩ := nodePoly_eq_const_mul_boundary t hcoll hroot
  have hs_pos : 0 < s := hcoll.1
  set np := nodePoly t with hnp_def
  set q := r /ₘ np with hq_def
  set rem := r %ₘ np with hrem_def
  have hmonic : np.Monic := by
    simpa [hnp_def] using nodePoly_monic t
  have hnp_ne_one : np ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [hnp_def, nodePoly_natDegree] at hdeg
    simp at hdeg
    omega
  have hdiv : rem + np * q = r := Polynomial.modByMonic_add_div r hmonic
  have hrem_deg : rem.natDegree < s := by
    calc
      rem.natDegree < np.natDegree := Polynomial.natDegree_modByMonic_lt r hmonic hnp_ne_one
      _ = s := by simpa [hnp_def] using nodePoly_natDegree t
  have heval : ∀ i : Fin s, r.eval (t.c i) = rem.eval (t.c i) := by
    intro i
    have h := congrArg (fun p => p.eval (t.c i)) hdiv
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at h
    rw [hnp_def, nodePoly_eval_node] at h
    linarith
  have hsum :
      ∑ i : Fin s, t.b i * r.eval (t.c i) = ∑ i : Fin s, t.b i * rem.eval (t.c i) := by
    congr 1
    ext i
    rw [heval]
  have hrem_exact :
      ∑ i : Fin s, t.b i * rem.eval (t.c i) = ∫ x in (0 : ℝ)..1, rem.eval x :=
    B_quadrature_exact t hcoll rem hrem_deg
  have hint_split :
      ∫ x in (0 : ℝ)..1, r.eval x =
        (∫ x in (0 : ℝ)..1, rem.eval x) + ∫ x in (0 : ℝ)..1, (np * q).eval x := by
    have hfun : (fun x : ℝ => r.eval x) = fun x => rem.eval x + (np * q).eval x := by
      ext x
      have h := congrArg (fun p => p.eval x) hdiv
      simp only [Polynomial.eval_add] at h
      linarith
    rw [hfun, intervalIntegral.integral_add
      (Continuous.intervalIntegrable (Polynomial.continuous rem) _ _)
      (Continuous.intervalIntegrable (Polynomial.continuous (np * q)) _ _)]
  have herr :
      ∑ i : Fin s, t.b i * r.eval (t.c i) - ∫ x in (0 : ℝ)..1, r.eval x =
        - ∫ x in (0 : ℝ)..1, (np * q).eval x := by
    rw [hsum, hrem_exact, hint_split]
    ring
  have hq_deg_le : q.natDegree ≤ s - 1 := by
    rw [hq_def, Polynomial.natDegree_divByMonic r hmonic]
    rw [show np.natDegree = s by simpa [hnp_def] using nodePoly_natDegree t]
    omega
  by_cases hq_lt : q.natDegree < s - 1
  · have horth : ∫ x in (0 : ℝ)..1, (np * q).eval x = 0 := by
      exact nodePoly_orthogonal_low_degree t hcoll hroot q (by omega)
    rw [herr, horth]
    simp
  · have hq_deg_eq : q.natDegree = s - 1 := by omega
    by_cases hq_zero : q = 0
    · rw [herr, hq_zero]
      simp
    have hq_ne : q ≠ 0 := hq_zero
    have hnpq_ne : np * q ≠ 0 := mul_ne_zero hmonic.ne_zero hq_ne
    have hnpq_natDegree : (np * q).natDegree = 2 * s - 1 := by
      rw [hmonic.natDegree_mul' hq_ne, hq_deg_eq]
      rw [show np.natDegree = s by simpa [hnp_def] using nodePoly_natDegree t]
      omega
    have hrem_lt_mul : rem.degree < (np * q).degree := by
      by_cases hrem_zero : rem = 0
      · rw [hrem_zero, Polynomial.degree_eq_natDegree hnpq_ne, hnpq_natDegree]
        have hpos : 0 < 2 * s - 1 := by omega
        simpa using hpos
      · rw [Polynomial.degree_eq_natDegree hrem_zero, Polynomial.degree_eq_natDegree hnpq_ne,
          hnpq_natDegree]
        exact Nat.cast_lt.2 (by omega)
    have hr_lc_eq : r.leadingCoeff = q.leadingCoeff := by
      rw [hdiv.symm, Polynomial.leadingCoeff_add_of_degree_lt hrem_lt_mul,
        Polynomial.leadingCoeff_mul]
      simpa [hmonic.leadingCoeff]
    have hqlc_nonneg : 0 ≤ q.leadingCoeff := by
      simpa [hr_lc_eq] using hlc
    let P : ℝ[X] := shiftedLegendreStarPoly (s - 1)
    have hP_lc_pos : 0 < P.leadingCoeff := by
      dsimp [P]
      exact shiftedLegendreStarPoly_leadingCoeff_pos (s - 1)
    let a : ℝ := q.leadingCoeff / P.leadingCoeff
    let u : ℝ[X] := q - Polynomial.C a * P
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg hqlc_nonneg (le_of_lt hP_lc_pos)
    have ha_ne : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hq_ne) (ne_of_gt hP_lc_pos)
    have hscaled_ne : Polynomial.C a * P ≠ 0 := by
      apply mul_ne_zero (by simpa using ha_ne)
      intro hP_zero
      simpa [P, hP_zero] using hP_lc_pos
    have hscaled_natDegree : (Polynomial.C a * P).natDegree = s - 1 := by
      rw [Polynomial.natDegree_C_mul ha_ne]
      dsimp [P]
      exact shiftedLegendreStarPoly_natDegree (s - 1)
    have hscaled_lc :
        q.leadingCoeff = (Polynomial.C a * P).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      dsimp [a]
      field_simp [ne_of_gt hP_lc_pos]
    have hu_orth : ∫ x in (0 : ℝ)..1, (P * u).eval x = 0 := by
      by_cases hu_zero : u = 0
      · simp [hu_zero]
      · have hu_deg : u.natDegree < s - 1 := by
          have hdeg_eq : q.degree = (Polynomial.C a * P).degree := by
            rw [Polynomial.degree_eq_natDegree hq_ne, hq_deg_eq,
              Polynomial.degree_eq_natDegree hscaled_ne, hscaled_natDegree]
          have hdeg_lt : u.degree < q.degree := by
            dsimp [u]
            exact Polynomial.degree_sub_lt hdeg_eq hq_ne hscaled_lc
          dsimp [u] at hu_zero
          rwa [Polynomial.degree_eq_natDegree hu_zero,
            Polynomial.degree_eq_natDegree hq_ne, hq_deg_eq, Nat.cast_lt] at hdeg_lt
        dsimp [P]
        exact shiftedLegendreStarPoly_interval_orthogonal (s - 1) u hu_deg
    have hPq :
        ∫ x in (0 : ℝ)..1, (P * q).eval x =
          a * ∫ x in (0 : ℝ)..1, (P * P).eval x := by
      have hfun :
          (fun x : ℝ => (P * q).eval x) =
            fun x : ℝ => a * ((P * P).eval x) + (P * u).eval x := by
        funext x
        dsimp [u]
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
        ring
      rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, hu_orth]
      · ring
      · exact Continuous.intervalIntegrable
          (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
      · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
    have hs_orth :
        ∫ x in (0 : ℝ)..1, ((shiftedLegendreStarPoly s) * q).eval x = 0 := by
      exact shiftedLegendreStarPoly_interval_orthogonal s q (by omega)
    have hboundary_int :
        ∫ x in (0 : ℝ)..1, (algStabilityBoundaryPoly s θ * q).eval x =
          -θ * (a * ∫ x in (0 : ℝ)..1, (P * P).eval x) := by
      have hfun :
          (fun x : ℝ => (algStabilityBoundaryPoly s θ * q).eval x) =
            fun x : ℝ =>
              ((shiftedLegendreStarPoly s) * q).eval x -
                θ * ((P * q).eval x) := by
        funext x
        dsimp [P]
        simp [algStabilityBoundaryPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
        ring
      rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, hs_orth, hPq]
      · ring
      · exact Continuous.intervalIntegrable (Polynomial.continuous _) _ _
      · exact Continuous.intervalIntegrable
          (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
    have hnode_int :
        ∫ x in (0 : ℝ)..1, (np * q).eval x =
          κ * (-θ * (a * ∫ x in (0 : ℝ)..1, (P * P).eval x)) := by
      have hfun :
          (fun x : ℝ => (np * q).eval x) =
            fun x : ℝ => κ * ((algStabilityBoundaryPoly s θ * q).eval x) := by
        funext x
        rw [hnode]
        simp [Polynomial.eval_mul, Polynomial.eval_C]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, hboundary_int]
    have hsq_pos : 0 < ∫ x in (0 : ℝ)..1, (P * P).eval x := by
      dsimp [P]
      exact shiftedLegendreStarPoly_sq_intervalIntegral_pos (s - 1)
    have hfinal :
        ∑ i : Fin s, t.b i * r.eval (t.c i) - ∫ x in (0 : ℝ)..1, r.eval x =
          κ * (θ * (a * ∫ x in (0 : ℝ)..1, (P * P).eval x)) := by
      rw [herr, hnode_int]
      ring
    rw [hfinal]
    exact mul_nonneg (le_of_lt hκ_pos) <|
      mul_nonneg hθ_nonneg <|
        mul_nonneg ha_nonneg (le_of_lt hsq_pos)

/-- Positive-semidefiniteness of the algebraic stability matrix under the boundary-node
hypothesis. -/
noncomputable def antiderivPoly (p : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (p.natDegree + 1)) fun k =>
    Polynomial.monomial (k + 1) (p.coeff k / (k + 1))

lemma antiderivPoly_eval
    (p : ℝ[X]) (z : ℝ) :
    (antiderivPoly p).eval z = ∫ x in (0 : ℝ)..z, p.eval x := by
  rw [antiderivPoly]
  rw [Polynomial.eval_finset_sum]
  have hpeval : (fun x : ℝ => p.eval x) =
      fun x => Finset.sum (Finset.range (p.natDegree + 1)) fun k => p.coeff k * x ^ k := by
    funext x
    simp [Polynomial.eval_eq_sum_range]
  rw [hpeval, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Polynomial.eval_monomial, intervalIntegral.integral_const_mul, integral_pow]
    field_simp
    ring
  · intro i hi
    exact Continuous.intervalIntegrable (Continuous.mul continuous_const (continuous_id.pow _)) _ _

lemma antiderivPoly_derivative
    (p : ℝ[X]) :
    (antiderivPoly p).derivative = p := by
  ext n
  rw [antiderivPoly, Polynomial.derivative_sum]
  simp [Polynomial.coeff_monomial]
  by_cases h : n ≤ p.natDegree
  · rw [if_pos h]
    field_simp
  · rw [if_neg h]
    symm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge h)

lemma antiderivPoly_natDegree_le
    (p : ℝ[X]) :
    (antiderivPoly p).natDegree ≤ p.natDegree + 1 := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  have hsum := Polynomial.degree_sum_le (s := Finset.range (p.natDegree + 1))
    (f := fun k => Polynomial.monomial (k + 1) (p.coeff k / (k + 1)))
  rw [show antiderivPoly p = Finset.sum (Finset.range (p.natDegree + 1))
      (fun k => Polynomial.monomial (k + 1) (p.coeff k / (k + 1))) by rfl]
  refine le_trans hsum ?_
  refine Finset.sup_le ?_
  intro k hk
  refine le_trans (Polynomial.degree_monomial_le _ _) ?_
  show ((k + 1 : ℕ) : WithBot ℕ) ≤ ↑(p.natDegree + 1)
  exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)

lemma antiderivPoly_leadingCoeff_of_natDegree_eq
    (p : ℝ[X]) {n : ℕ} (hp : p.natDegree = n) :
    (antiderivPoly p).leadingCoeff = p.leadingCoeff / (n + 1) := by
  by_cases hp0 : p = 0
  · simp [hp0, antiderivPoly]
  have hcoeff_top : (antiderivPoly p).coeff (n + 1) = p.leadingCoeff / (n + 1) := by
    rw [show antiderivPoly p = Finset.sum (Finset.range (p.natDegree + 1))
        (fun k => Polynomial.monomial (k + 1) (p.coeff k / (k + 1))) by rfl]
    simp
    rw [Finset.sum_eq_single n]
    · simpa [Polynomial.leadingCoeff, hp]
    · intro k hk hkn
      rw [Polynomial.coeff_monomial]
      by_cases hks : k + 1 = n + 1
      · omega
      · rw [if_neg hks]
    · have hn_mem : n ∈ Finset.range (p.natDegree + 1) := by
        rw [hp]
        exact Finset.mem_range.mpr (Nat.lt_succ_self n)
      intro hn_not
      exact (hn_not hn_mem).elim
  have htop_ne : (antiderivPoly p).coeff (n + 1) ≠ 0 := by
    rw [hcoeff_top]
    have hlc_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp0
    exact div_ne_zero hlc_ne (by positivity)
  have hdeg_le : (antiderivPoly p).natDegree ≤ n + 1 := by
    simpa [hp] using antiderivPoly_natDegree_le p
  have hdeg_ge : n + 1 ≤ (antiderivPoly p).natDegree := by
    by_contra hlt
    have hzero := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hlt)
    exact htop_ne hzero
  have hdeg : (antiderivPoly p).natDegree = n + 1 := le_antisymm hdeg_le hdeg_ge
  rw [Polynomial.leadingCoeff, hdeg, hcoeff_top]

lemma algStabMatrix_quadForm_nonneg_of_boundary
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    ∀ d : Fin s → ℝ,
      0 ≤ ∑ i : Fin s, ∑ j : Fin s, d i * t.algStabMatrix i j * d j := by
  intro d
  let p : ℝ[X] := ∑ j : Fin s, Polynomial.C (d j) * lagrangeBasisPoly t j
  have h_inj : Set.InjOn t.c (Finset.univ : Finset (Fin s)) := by
    intro i hi j hj hij
    exact hcoll.2.2.2 hij
  have hp_eval : ∀ i : Fin s, p.eval (t.c i) = d i := by
    intro i
    dsimp [p]
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i]
    · rw [Polynomial.eval_mul]
      unfold ButcherTableau.lagrangeBasisPoly
      rw [Lagrange.eval_basis_self h_inj (Finset.mem_univ i)]
      simp
    · intro j hj
      intro hji
      rw [Polynomial.eval_mul]
      unfold ButcherTableau.lagrangeBasisPoly
      rw [Lagrange.eval_basis_of_ne hji]
      · ring
      · exact Finset.mem_univ i
    · aesop
  have hp_deg : p.natDegree < s := by
    have hs : 0 < s := hcoll.1
    by_cases hp0 : p = 0
    · rw [hp0]
      simpa using hs
    · rw [Polynomial.natDegree_lt_iff_degree_lt hp0]
      have hdeg_le :
          p.degree ≤
            (Finset.univ : Finset (Fin s)).sup fun j =>
              (Polynomial.C (d j) * lagrangeBasisPoly t j).degree := by
        simpa [p] using
          (Polynomial.degree_sum_le (s := (Finset.univ : Finset (Fin s)))
            (f := fun j => Polynomial.C (d j) * lagrangeBasisPoly t j))
      have hbot : (⊥ : WithBot ℕ) < (s : WithBot ℕ) := by
        simpa using hs
      have hsup_lt :
          ((Finset.univ : Finset (Fin s)).sup fun j =>
            (Polynomial.C (d j) * lagrangeBasisPoly t j).degree) < (s : WithBot ℕ) := by
        refine (Finset.sup_lt_iff hbot).2 ?_
        intro i hi
        by_cases hdi : d i = 0
        · simp [hdi, lagrangeBasisPoly]
        · rw [Polynomial.degree_C_mul, lagrangeBasisPoly]
          · rw [Lagrange.degree_basis (s := (Finset.univ : Finset (Fin s))) (v := t.c)
              h_inj (Finset.mem_univ i)]
            have hs_sub : s - 1 < s := by omega
            simpa using (show ((s - 1 : ℕ) : WithBot ℕ) < (s : WithBot ℕ) by
              exact_mod_cast hs_sub)
          · simpa using hdi
      exact lt_of_le_of_lt hdeg_le hsup_lt
  have hp_expand_eval : ∀ x : ℝ,
      p.eval x = ∑ j : Fin s, d j * (lagrangeBasisPoly t j).eval x := by
    intro x
    dsimp [p]
    rw [Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hA_eval :
      ∀ i : Fin s, ∑ j : Fin s, t.A i j * d j = ∫ x in (0 : ℝ)..t.c i, p.eval x := by
    intro i
    calc
      ∑ j : Fin s, t.A i j * d j
          = ∑ j : Fin s, d j * ∫ x in (0 : ℝ)..t.c i, (lagrangeBasisPoly t j).eval x := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [A_eq_integral_lagrange t hcoll i j]
              ring
      _ = ∫ x in (0 : ℝ)..t.c i, ∑ j : Fin s, d j * (lagrangeBasisPoly t j).eval x := by
            rw [intervalIntegral.integral_finset_sum]
            · refine Finset.sum_congr rfl ?_
              intro j hj
              rw [intervalIntegral.integral_const_mul]
            · intro j hj
              exact Continuous.intervalIntegrable
                (Continuous.mul continuous_const (Polynomial.continuous _)) _ _
      _ = ∫ x in (0 : ℝ)..t.c i, p.eval x := by
            congr with x
            rw [hp_expand_eval]
  let Q : ℝ[X] := antiderivPoly p
  have hQ_eval : ∀ z : ℝ, Q.eval z = ∫ x in (0 : ℝ)..z, p.eval x := by
    intro z
    simpa [Q] using antiderivPoly_eval p z
  have hsumA :
      ∑ i : Fin s, ∑ j : Fin s, t.b i * d i * t.A i j * d j =
        ∑ i : Fin s, t.b i * d i * Q.eval (t.c i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      ∑ j : Fin s, t.b i * d i * t.A i j * d j
          = t.b i * d i * (∑ j : Fin s, t.A i j * d j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = t.b i * d i * ∫ x in (0 : ℝ)..t.c i, p.eval x := by rw [hA_eval i]
      _ = t.b i * d i * Q.eval (t.c i) := by rw [hQ_eval]
  have hb_eval : ∑ i : Fin s, t.b i * d i = ∫ x in (0 : ℝ)..1, p.eval x := by
    calc
      ∑ i : Fin s, t.b i * d i = ∑ i : Fin s, t.b i * p.eval (t.c i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hp_eval]
      _ = ∫ x in (0 : ℝ)..1, p.eval x := by
        exact B_quadrature_exact t hcoll p hp_deg
  have hprod_eval :
      ∑ i : Fin s, t.b i * d i * Q.eval (t.c i) =
        ∑ i : Fin s, t.b i * (p * Q).eval (t.c i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      t.b i * d i * Q.eval (t.c i) = t.b i * p.eval (t.c i) * Q.eval (t.c i) := by
            rw [hp_eval]
      _ = t.b i * (p * Q).eval (t.c i) := by
            simp [Polynomial.eval_mul]
            ring
  have hint_Q :
      ∫ x in (0 : ℝ)..1, p.eval x * Q.eval x =
        ∫ x in (0 : ℝ)..1, (p * Q).eval x := by
    congr with x
    simp [Polynomial.eval_mul]
  have hQ_one : Q.eval 1 = ∫ x in (0 : ℝ)..1, p.eval x := by
    rw [hQ_eval]
  have hQ_zero : Q.eval 0 = 0 := by
    simpa [Q] using hQ_eval 0
  have hint_pQ :
      ∫ x in (0 : ℝ)..1, p.eval x * Q.eval x =
        (∫ x in (0 : ℝ)..1, p.eval x) ^ 2 / 2 := by
    have hQcont : ContinuousOn (fun y : ℝ => (Q.eval y) ^ 2 / 2) (Set.uIcc (0 : ℝ) 1) := by
      exact (Continuous.div_const ((Polynomial.continuous Q).pow 2) 2).continuousOn
    have hderiv :
        ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivWithinAt (fun y : ℝ => (Q.eval y) ^ 2 / 2) (Q.eval x * p.eval x) (Set.Ioi x) x := by
      intro x hx
      have hQd : HasDerivAt (fun y : ℝ => Q.eval y) (p.eval x) x := by
        simpa [Q, antiderivPoly_derivative] using (Q.hasDerivAt x)
      have hsquare : HasDerivAt (fun y : ℝ => (Q.eval y) ^ 2) (2 * Q.eval x * p.eval x) x := by
        simpa [pow_two, two_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
          hQd.mul hQd
      have hconst :
          HasDerivAt (fun y : ℝ => ((Q.eval y) ^ 2) / 2) ((2 * Q.eval x * p.eval x) / 2) x :=
        hsquare.div_const 2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hconst.hasDerivWithinAt
    have hint_int :
        IntervalIntegrable (fun x : ℝ => Q.eval x * p.eval x) MeasureTheory.volume 0 1 := by
      exact Continuous.intervalIntegrable
        (Continuous.mul (Polynomial.continuous Q) (Polynomial.continuous p)) _ _
    have hmain :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right hQcont hderiv hint_int
    calc
      ∫ x in (0 : ℝ)..1, p.eval x * Q.eval x
          = ∫ x in (0 : ℝ)..1, Q.eval x * p.eval x := by
              congr with x
              ring
      _ = (Q.eval 1) ^ 2 / 2 - (Q.eval 0) ^ 2 / 2 := hmain
      _ = (Q.eval 1) ^ 2 / 2 := by rw [hQ_zero]; ring
      _ = (∫ x in (0 : ℝ)..1, p.eval x) ^ 2 / 2 := by rw [hQ_one]
  have hdeg_pQ : (p * Q).natDegree ≤ 2 * s - 1 := by
    calc
      (p * Q).natDegree ≤ p.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
      _ ≤ p.natDegree + (p.natDegree + 1) := by
        gcongr
        simpa [Q] using antiderivPoly_natDegree_le p
      _ ≤ 2 * s - 1 := by
        omega
  have hlc_pQ : 0 ≤ (p * Q).leadingCoeff := by
    by_cases hp0 : p = 0
    · simp [hp0, Q]
    · dsimp [Q]
      rw [Polynomial.leadingCoeff_mul, antiderivPoly_leadingCoeff_of_natDegree_eq p rfl]
      have hden : 0 < ((p.natDegree : ℝ) + 1) := by
        positivity
      have hrewrite :
          p.leadingCoeff * (p.leadingCoeff / ((p.natDegree : ℝ) + 1)) =
            p.leadingCoeff ^ 2 / ((p.natDegree : ℝ) + 1) := by
        field_simp
      have : 0 ≤ p.leadingCoeff ^ 2 / ((p.natDegree : ℝ) + 1) :=
        div_nonneg (sq_nonneg _) (le_of_lt hden)
      simpa [hrewrite] using this
  have hquad_nonneg :
      0 ≤ ∑ i : Fin s, t.b i * (p * Q).eval (t.c i) -
        ∫ x in (0 : ℝ)..1, (p * Q).eval x := by
    exact quadrature_error_pQ_nonneg_of_boundary t hcoll hroot (p * Q) hdeg_pQ hlc_pQ
  have hident₁ :
      ∑ i : Fin s, ∑ j : Fin s, d i * t.algStabMatrix i j * d j =
        2 * (∑ i : Fin s, t.b i * (p * Q).eval (t.c i)) -
          (∫ x in (0 : ℝ)..1, p.eval x) ^ 2 := by
    rw [algStabMatrix_quadForm_expand (t := t) (v := d), hsumA, hprod_eval, hb_eval]
  have hident₂ :
      2 * (∑ i : Fin s, t.b i * (p * Q).eval (t.c i)) -
        (∫ x in (0 : ℝ)..1, p.eval x) ^ 2 =
          2 * (∑ i : Fin s, t.b i * (p * Q).eval (t.c i) -
            ∫ x in (0 : ℝ)..1, (p * Q).eval x) := by
    have hsq :
        (∫ x in (0 : ℝ)..1, p.eval x) ^ 2 =
          2 * ∫ x in (0 : ℝ)..1, p.eval x * Q.eval x := by
      rw [hint_pQ]
      ring
    rw [hsq, hint_Q]
    ring
  rw [hident₁, hident₂]
  exact mul_nonneg (by norm_num) hquad_nonneg

/-- Theorem 358A, `if` direction. -/
theorem thm_358A_if
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    t.IsAlgStable := by
  exact ⟨weights_nonneg_of_boundary t hcoll hroot,
    algStabMatrix_quadForm_nonneg_of_boundary t hcoll hroot⟩

/-- **Theorem 358A**: a collocation Runge–Kutta method is algebraically stable
iff its nodes are zeros of `P_s^* - θ P_{s-1}^*` for some `θ ≥ 0`. -/
theorem thm_358A
    (t : ButcherTableau s) (hcoll : t.IsCollocation) :
    t.IsAlgStable ↔ t.HasAlgStabilityBoundaryNodes := by
  constructor
  · exact thm_358A_only_if t hcoll
  · exact thm_358A_if t hcoll

end ButcherTableau
