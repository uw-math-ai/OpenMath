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

/-- The theorem-local polynomial antiderivative used in the transformed `(358c)`
argument. The range is truncated at `s`, which is sufficient under the degree
hypotheses used below. -/
private noncomputable def antiderivativePoly (s : ℕ) (q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range s,
    Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * Polynomial.X ^ (i + 1)

private lemma antiderivativePoly_eval (q : ℝ[X]) (x : ℝ) :
    (antiderivativePoly s q).eval x =
      ∑ i ∈ Finset.range s, q.coeff i / ((i : ℝ) + 1) * x ^ (i + 1) := by
  simp [antiderivativePoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private lemma antiderivativePoly_eval_zero (q : ℝ[X]) :
    (antiderivativePoly s q).eval (0 : ℝ) = 0 := by
  simp [antiderivativePoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private lemma antiderivativePoly_eval_one_eq_polyMoment (q : ℝ[X]) :
    (antiderivativePoly s q).eval (1 : ℝ) = polyMomentN s q := by
  simp [antiderivativePoly, polyMomentN, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private lemma antiderivativePoly_eval_one_eq_intervalIntegral
    (q : ℝ[X]) (hq : q.natDegree < s) :
    (antiderivativePoly s q).eval (1 : ℝ) =
      ∫ x in (0 : ℝ)..1, q.eval x := by
  rw [antiderivativePoly_eval_one_eq_polyMoment]
  exact polyMomentN_eq_intervalIntegral_of_natDegree_lt q hq

private lemma antiderivativePoly_eval_one_eq_quadEval
    (t : ButcherTableau s) (hB : t.SatisfiesB s) (q : ℝ[X]) (hq : q.natDegree < s) :
    (antiderivativePoly s q).eval (1 : ℝ) = quadEvalPoly t q := by
  rw [antiderivativePoly_eval_one_eq_polyMoment]
  exact (quadEvalPoly_exact_of_natDegree_lt_of_SatisfiesB t hB q hq).symm

private lemma antiderivativePoly_derivative
    (q : ℝ[X]) (hq : q.natDegree < s) :
    (antiderivativePoly s q).derivative = q := by
  sorry

private lemma antiderivativePoly_natDegree_lt
    (hs : 0 < s) (q : ℝ[X]) (hq : q.natDegree < s - 1) :
    (antiderivativePoly s q).natDegree < s := by
  sorry

private lemma antiderivativePoly_eval_mul_integral
    (q : ℝ[X]) (hq : q.natDegree < s) :
    ∫ x in (0 : ℝ)..1, (q * antiderivativePoly s q).eval x =
      (antiderivativePoly s q).eval (1 : ℝ) ^ 2 / 2 := by
  sorry

private lemma antiderivativePoly_eval_node_eq_collocation
    (t : ButcherTableau s) (hC : t.SatisfiesC s) (q : ℝ[X]) (hq : q.natDegree < s)
    (i : Fin s) :
    (antiderivativePoly s q).eval (t.c i) =
      ∑ j : Fin s, t.A i j * q.eval (t.c j) := by
  have hqEq := q.as_sum_range_C_mul_X_pow' hq
  have hqEval : ∀ j : Fin s, q.eval (t.c j) = ∑ k ∈ Finset.range s, q.coeff k * t.c j ^ k := by
    intro j
    have hEval := congrArg (fun p : ℝ[X] => p.eval (t.c j)) hqEq
    simpa [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hEval
  calc
    (antiderivativePoly s q).eval (t.c i)
        = ∑ k ∈ Finset.range s, q.coeff k / ((k : ℝ) + 1) * t.c i ^ (k + 1) := by
            simpa using antiderivativePoly_eval (s := s) q (t.c i)
    _ = ∑ k ∈ Finset.range s, q.coeff k * (∑ j : Fin s, t.A i j * t.c j ^ k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hCk := hC (k + 1) (by omega) (by simpa using hk) i
          have hCk' : ∑ j : Fin s, t.A i j * t.c j ^ k = t.c i ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
            simpa using hCk
          calc
            q.coeff k / ((k : ℝ) + 1) * t.c i ^ (k + 1)
                = q.coeff k * (t.c i ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
                    rw [div_eq_mul_inv, div_eq_mul_inv]
                    simpa [Nat.cast_add, mul_assoc, mul_left_comm, mul_comm]
            _ = q.coeff k * (∑ j : Fin s, t.A i j * t.c j ^ k) := by
                  rw [hCk']
    _ = ∑ j : Fin s, t.A i j * ∑ k ∈ Finset.range s, q.coeff k * t.c j ^ k := by
          calc
            ∑ k ∈ Finset.range s, q.coeff k * (∑ j : Fin s, t.A i j * t.c j ^ k)
                = ∑ k ∈ Finset.range s, ∑ j : Fin s, q.coeff k * (t.A i j * t.c j ^ k) := by
                    simp [Finset.mul_sum]
            _ = ∑ j : Fin s, ∑ k ∈ Finset.range s, q.coeff k * (t.A i j * t.c j ^ k) := by
                  rw [Finset.sum_comm]
            _ = ∑ j : Fin s, t.A i j * ∑ k ∈ Finset.range s, q.coeff k * t.c j ^ k := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                calc
                  ∑ k ∈ Finset.range s, q.coeff k * (t.A i j * t.c j ^ k)
                      = ∑ k ∈ Finset.range s, t.A i j * (q.coeff k * t.c j ^ k) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          ring
                  _ = t.A i j * ∑ k ∈ Finset.range s, q.coeff k * t.c j ^ k := by
                        rw [Finset.mul_sum]
    _ = ∑ j : Fin s, t.A i j * q.eval (t.c j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hqEval j]
    _ = ∑ j : Fin s, t.A i j * q.eval (t.c j) := by rfl

private lemma nodePoly_ne_one (t : ButcherTableau s) (hs : 0 < s) :
    nodePoly t ≠ 1 := by
  intro h
  have hdeg := congrArg Polynomial.natDegree h
  have hs0 : s = 0 := by
    simpa [nodePoly_natDegree, Polynomial.natDegree_one] using hdeg
  exact hs.ne' hs0

private lemma modByMonic_nodePoly_natDegree_lt
    (t : ButcherTableau s) (hs : 0 < s) (p : ℝ[X]) :
    (p %ₘ nodePoly t).natDegree < s := by
  simpa [nodePoly_natDegree] using
    Polynomial.natDegree_modByMonic_lt p (nodePoly_monic t) (nodePoly_ne_one t hs)

private lemma modByMonic_nodePoly_eval_eq
    (t : ButcherTableau s) (p : ℝ[X]) (i : Fin s) :
    (p %ₘ nodePoly t).eval (t.c i) = p.eval (t.c i) := by
  have hsplit := Polynomial.modByMonic_add_div p (nodePoly_monic t)
  have hEval := congrArg (fun r : ℝ[X] => r.eval (t.c i)) hsplit
  simpa [Polynomial.eval_add, Polynomial.eval_mul, nodePoly_eval_node] using hEval

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

private lemma algStabMatrix_quadForm_eq_antiderivativePoly
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (q : ℝ[X]) (hq : q.natDegree < s) :
    let Qpoly : ℝ[X] := antiderivativePoly s q
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      2 * ∑ i : Fin s, t.b i * q.eval (t.c i) * Qpoly.eval (t.c i) -
        (Qpoly.eval (1 : ℝ)) ^ 2 := by
  dsimp
  rw [algStabMatrix_quadForm_expand]
  have hA :
      ∑ i : Fin s, ∑ j : Fin s, t.b i * q.eval (t.c i) * t.A i j * q.eval (t.c j) =
        ∑ i : Fin s, t.b i * q.eval (t.c i) * (antiderivativePoly s q).eval (t.c i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      ∑ j : Fin s, t.b i * q.eval (t.c i) * t.A i j * q.eval (t.c j)
          = t.b i * q.eval (t.c i) * ∑ j : Fin s, t.A i j * q.eval (t.c j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = t.b i * q.eval (t.c i) * (antiderivativePoly s q).eval (t.c i) := by
            rw [← antiderivativePoly_eval_node_eq_collocation t hcoll.2.2.1 q hq i]
  have hB :
      ∑ i : Fin s, t.b i * q.eval (t.c i) = (antiderivativePoly s q).eval (1 : ℝ) := by
    rw [show (∑ i : Fin s, t.b i * q.eval (t.c i)) = quadEvalPoly t q by rfl]
    rw [← antiderivativePoly_eval_one_eq_quadEval t hcoll.2.1 q hq]
  rw [hA, hB]

private lemma antiderivative_remainder_exact
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (q : ℝ[X]) (hq : q.natDegree ≤ s - 1) :
    let Qpoly : ℝ[X] := antiderivativePoly s q
    let r : ℝ[X] := Qpoly %ₘ nodePoly t
    ∑ i : Fin s, t.b i * q.eval (t.c i) * r.eval (t.c i)
      = ∫ x in (0 : ℝ)..1, (q * r).eval x := by
  sorry

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
  let Qpoly : ℝ[X] := antiderivativePoly s q
  let r : ℝ[X] := Qpoly %ₘ nodePoly t
  have hq_lt_s : q.natDegree < s := by
    omega
  have hr_natDegree : r.natDegree < s := by
    dsimp [r]
    exact modByMonic_nodePoly_natDegree_lt t hcoll.1 Qpoly
  have hr_eval : ∀ i : Fin s, r.eval (t.c i) = Qpoly.eval (t.c i) := by
    intro i
    dsimp [r, Qpoly]
    exact modByMonic_nodePoly_eval_eq t _ i
  have hquad :
      ∑ i : Fin s, ∑ j : Fin s,
          q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j) =
        2 * ∑ i : Fin s, t.b i * q.eval (t.c i) * r.eval (t.c i) -
          (Qpoly.eval (1 : ℝ)) ^ 2 := by
    rw [algStabMatrix_quadForm_eq_antiderivativePoly t hcoll q hq_lt_s]
    refine congrArg (fun z : ℝ => 2 * z - (Qpoly.eval (1 : ℝ)) ^ 2) ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hr_eval i]
  have hexact :
      ∑ i : Fin s, t.b i * q.eval (t.c i) * r.eval (t.c i) =
        ∫ x in (0 : ℝ)..1, (q * r).eval x := by
    rw [antiderivative_remainder_exact t hcoll q (by omega)]
  have hQ1 :
      Qpoly.eval (1 : ℝ) = ∫ x in (0 : ℝ)..1, q.eval x := by
    dsimp [Qpoly]
    exact antiderivativePoly_eval_one_eq_intervalIntegral q hq_lt_s
  have hquot_zero : Qpoly /ₘ nodePoly t = 0 := by
    have hQdeg : Qpoly.natDegree < s := by
      dsimp [Qpoly]
      exact antiderivativePoly_natDegree_lt hcoll.1 q hq
    rw [Polynomial.divByMonic_eq_zero_iff (nodePoly_monic t)]
    have hQdegNode : Qpoly.natDegree < (nodePoly t).natDegree := by
      simpa [nodePoly_natDegree] using hQdeg
    exact Polynomial.degree_lt_degree hQdegNode
  have hr_eq_Q : r = Qpoly := by
    dsimp [r]
    have hsplit := Polynomial.modByMonic_add_div Qpoly (nodePoly_monic t)
    rw [hquot_zero, mul_zero, add_zero] at hsplit
    exact hsplit
  have hexactQ :
      ∑ i : Fin s, t.b i * q.eval (t.c i) * Qpoly.eval (t.c i) =
        ∫ x in (0 : ℝ)..1, (q * Qpoly).eval x := by
    simpa [hr_eq_Q] using hexact
  have hquadQ :
      ∑ i : Fin s, ∑ j : Fin s,
          q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j) =
        2 * ∑ i : Fin s, t.b i * q.eval (t.c i) * Qpoly.eval (t.c i) -
          (Qpoly.eval (1 : ℝ)) ^ 2 := by
    simpa [hr_eq_Q] using hquad
  have hquad_zero : ∑ i : Fin s, ∑ j : Fin s,
      q.eval (t.c i) * t.algStabMatrix i j * q.eval (t.c j) = 0 := by
    rw [hquadQ, hexactQ, antiderivativePoly_eval_mul_integral q hq_lt_s]
    ring
  have hnode :
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0 := by
    sorry
  exact hnode

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
  sorry

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
