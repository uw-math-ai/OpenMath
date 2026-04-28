import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Hamiltonian systems

Basic infrastructure for Iserles, Chapter 5: Hamiltonians on the standard
phase space, separable Hamiltonians, the Hamiltonian vector field, and
conservation of the Hamiltonian along exact flow trajectories.
-/

noncomputable section

open scoped BigOperators
open InnerProductSpace

namespace Hamiltonian

/-- Standard phase space with `d` position and `d` momentum coordinates. -/
abbrev PhaseSpace (d : ℕ) := EuclideanSpace ℝ (Fin (2 * d))

/-- The `d`-dimensional coordinate block used for positions or momenta. -/
abbrev ConfigSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The standard split of `Fin (2*d)` into the left and right `d`-blocks. -/
def splitIndexEquiv (d : ℕ) : (Fin d ⊕ Fin d) ≃ Fin (2 * d) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul d).symm)

/-- Position-coordinate index in phase space. -/
def qIndex {d : ℕ} (i : Fin d) : Fin (2 * d) :=
  splitIndexEquiv d (Sum.inl i)

/-- Momentum-coordinate index in phase space. -/
def pIndex {d : ℕ} (i : Fin d) : Fin (2 * d) :=
  splitIndexEquiv d (Sum.inr i)

@[simp] lemma splitIndexEquiv_symm_qIndex {d : ℕ} (i : Fin d) :
    (splitIndexEquiv d).symm (qIndex i) = Sum.inl i := by
  simp [qIndex]

@[simp] lemma splitIndexEquiv_symm_pIndex {d : ℕ} (i : Fin d) :
    (splitIndexEquiv d).symm (pIndex i) = Sum.inr i := by
  simp [pIndex]

/-- Position part of a phase-space vector. -/
def qPart {d : ℕ} (x : PhaseSpace d) : ConfigSpace d :=
  WithLp.toLp 2 fun i : Fin d => x (qIndex i)

/-- Momentum part of a phase-space vector. -/
def pPart {d : ℕ} (x : PhaseSpace d) : ConfigSpace d :=
  WithLp.toLp 2 fun i : Fin d => x (pIndex i)

@[simp] lemma qPart_apply {d : ℕ} (x : PhaseSpace d) (i : Fin d) :
    qPart x i = x (qIndex i) := by
  rfl

@[simp] lemma pPart_apply {d : ℕ} (x : PhaseSpace d) (i : Fin d) :
    pPart x i = x (pIndex i) := by
  rfl

/-- A Hamiltonian is smooth enough here to take gradients and prove energy conservation. -/
def IsHamiltonian {d : ℕ} (H : PhaseSpace d → ℝ) : Prop :=
  ContDiff ℝ 2 H

/-- A separable Hamiltonian has the form `H(q,p) = T(p) + V(q)`. -/
def IsSeparable {d : ℕ} (H : PhaseSpace d → ℝ) : Prop :=
  ∃ T V : ConfigSpace d → ℝ,
    ContDiff ℝ 2 T ∧ ContDiff ℝ 2 V ∧
      ∀ x : PhaseSpace d, H x = T (pPart x) + V (qPart x)

/-- The canonical symplectic rotation `(q,p) ↦ (p,-q)`. -/
def canonicalJ {d : ℕ} (v : PhaseSpace d) : PhaseSpace d :=
  WithLp.toLp 2 fun k : Fin (2 * d) =>
    match (splitIndexEquiv d).symm k with
    | Sum.inl i => v (pIndex i)
    | Sum.inr i => -v (qIndex i)

@[simp] lemma canonicalJ_qIndex {d : ℕ} (v : PhaseSpace d) (i : Fin d) :
    canonicalJ v (qIndex i) = v (pIndex i) := by
  simp [canonicalJ]

@[simp] lemma canonicalJ_pIndex {d : ℕ} (v : PhaseSpace d) (i : Fin d) :
    canonicalJ v (pIndex i) = -v (qIndex i) := by
  simp [canonicalJ]

lemma inner_canonicalJ_self_eq_zero {d : ℕ} (v : PhaseSpace d) :
    inner ℝ v (canonicalJ v) = 0 := by
  simp +decide [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [← Equiv.sum_comp (splitIndexEquiv d)]
  simp +decide [canonicalJ]
  ring_nf!
  simp +decide [mul_comm, qIndex, pIndex]

/-- Hamiltonian vector field `J * grad H`, i.e. `q' = H_p`, `p' = -H_q`. -/
def hamiltonianVectorField {d : ℕ} (H : PhaseSpace d → ℝ) :
    PhaseSpace d → PhaseSpace d :=
  fun x => canonicalJ (gradient H x)

/-- Exact trajectory of the Hamiltonian vector field. -/
def IsHamiltonianTrajectory {d : ℕ} (H : PhaseSpace d → ℝ) (γ : ℝ → PhaseSpace d) :
    Prop :=
  Differentiable ℝ γ ∧ ∀ t, HasDerivAt γ (hamiltonianVectorField H (γ t)) t

lemma dH_along_trajectory_eq_zero {d : ℕ} (H : PhaseSpace d → ℝ)
    (γ : ℝ → PhaseSpace d) (hH : IsHamiltonian H)
    (hγ : IsHamiltonianTrajectory H γ) :
    ∀ t, HasDerivAt (fun s => H (γ s)) 0 t := by
  have h_diff_H : ∀ t, DifferentiableAt ℝ H (γ t) := by
    exact fun t => hH.contDiffAt.differentiableAt (by norm_num)
  intro t
  have h_deriv_H :
      HasDerivAt (fun s => H (γ s))
        (inner ℝ (gradient H (γ t)) (hamiltonianVectorField H (γ t))) t := by
    convert HasFDerivAt.comp_hasDerivAt t ((h_diff_H t).hasFDerivAt) (hγ.2 t) using 1
    simp +decide [gradient]
  convert h_deriv_H using 1
  exact (inner_canonicalJ_self_eq_zero (gradient H (γ t))).symm

theorem energy_conserved {d : ℕ} (H : PhaseSpace d → ℝ) (γ : ℝ → PhaseSpace d)
    (hH : IsHamiltonian H) (hγ : IsHamiltonianTrajectory H γ) :
    ∀ t s, H (γ t) = H (γ s) := by
  have h_const : ∀ t, HasDerivAt (fun s => H (γ s)) 0 t :=
    dH_along_trajectory_eq_zero H γ hH hγ
  exact fun t s =>
    is_const_of_deriv_eq_zero
      (fun t => (h_const t).differentiableAt)
      (fun t => (h_const t).deriv) t s

end Hamiltonian
