import OpenMath.Legendre
import OpenMath.StiffEquations

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

/-- The polynomial `P_s^* - θ P_{s-1}^*` in the polynomial model used for Theorem 358A. -/
noncomputable def algStabilityBoundaryPoly (s : ℕ) (θ : ℝ) : ℝ[X] :=
  shiftedLegendrePoly s - Polynomial.C θ * shiftedLegendrePoly (s - 1)

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

/-- A degree-`s` polynomial with positive leading coefficient and orthogonal to
all polynomials of degree at most `s - 2` must be a positive multiple of
`P_s^* - θ P_{s-1}^*`. -/
lemma orthogonal_degree_eq_boundaryPoly
    (hs : 0 < s) {φ : ℝ[X]}
    (hdeg : φ.natDegree = s) (hlc : 0 < φ.leadingCoeff)
    (horth : ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, (φ * q).eval x = 0) :
    ∃ θ a : ℝ, 0 < a ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ := by
  sorry

/-- Sign extraction for the `θ` parameter in the boundary polynomial.

This is the theorem-local version of the step obtained by testing against
`P_{s-1}^*`. -/
lemma boundary_theta_nonneg_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    {θ a : ℝ} (ha : 0 < a)
    (hnode : nodePoly t = Polynomial.C a * algStabilityBoundaryPoly s θ) :
    0 ≤ θ := by
  sorry

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

/-- Theorem 358A, `if` direction. -/
theorem thm_358A_if
    (t : ButcherTableau s) (hcoll : t.IsCollocation)
    (hroot : t.HasAlgStabilityBoundaryNodes) :
    t.IsAlgStable := by
  sorry

/-- **Theorem 358A**: a collocation Runge–Kutta method is algebraically stable
iff its nodes are zeros of `P_s^* - θ P_{s-1}^*` for some `θ ≥ 0`. -/
theorem thm_358A
    (t : ButcherTableau s) (hcoll : t.IsCollocation) :
    t.IsAlgStable ↔ t.HasAlgStabilityBoundaryNodes := by
  constructor
  · exact thm_358A_only_if t hcoll
  · exact thm_358A_if t hcoll

end ButcherTableau
