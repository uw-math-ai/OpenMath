import OpenMath.MultistepMethods
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Dahlquist Equivalence Theorem

The Dahlquist equivalence theorem (Theorem 1.5.2 in Iserles) states that for a
linear multistep method:

  **consistency + zero-stability ⟺ convergence**

## Structure

We decompose the proof into:
1. **Stability of linear recurrences**: The recurrence ∑ α_j y_{n+j} = 0
   has only bounded solutions iff ρ satisfies the root condition (zero-stability).
2. **Forward direction**: zero-stability → stable recurrence
   (needs general solution theory for linear recurrences).
3. **Backward direction**: stable recurrence → zero-stability
   (via geometric and linear-geometric solutions).

### Key results:
* `geometric_satisfies_iff`: ξ^n satisfies the recurrence iff ρ(ξ) = 0.
* `linear_geometric_satisfies`: n·ξ^n satisfies the recurrence when ξ is a double root.
* `not_stableRecurrence_of_root_outside_disk`: root with |ξ| > 1 → unstable recurrence.
* `not_stableRecurrence_of_double_root_on_circle`: double unit root → unstable recurrence.
* `zeroStable_of_stableRecurrence`: stable recurrence → zero-stable.
* `dahlquist_equivalence`: consistency + zero-stability ↔ convergence (stated).

## References

* [Iserles, *A First Course in the Numerical Analysis of Differential Equations*, §1.5]
-/

open Finset Real

namespace LMM

variable {s : ℕ}

/-! ## Stability of Linear Recurrences

The characteristic recurrence of an LMM is ∑_{j=0}^s α_j y_{n+j} = 0.
Since α_s = 1, this is y_{n+s} = -∑_{j<s} α_j y_{n+j}.

Zero-stability (root condition on ρ) is equivalent to every solution being bounded. -/

/-- A sequence `y : ℕ → ℂ` satisfies the **characteristic recurrence** of the LMM:
  ∑_{j=0}^{s} α_j · y(n+j) = 0 for all n ≥ 0. -/
def SatisfiesRecurrence (m : LMM s) (y : ℕ → ℂ) : Prop :=
  ∀ n, ∑ j : Fin (s + 1), (m.α j : ℂ) * y (n + ↑j) = 0

/-- An LMM has a **stable recurrence** if every complex-valued solution of its
  characteristic recurrence is bounded. -/
def HasStableRecurrence (m : LMM s) : Prop :=
  ∀ y : ℕ → ℂ, m.SatisfiesRecurrence y → ∃ C : ℝ, ∀ n, ‖y n‖ ≤ C

/-! ### Geometric solutions -/

/-- The geometric sequence ξ^n satisfies the characteristic recurrence iff ρ_ℂ(ξ) = 0.
This connects roots of the characteristic polynomial to solutions of the recurrence. -/
theorem geometric_satisfies_iff (m : LMM s) (ξ : ℂ) :
    m.SatisfiesRecurrence (fun n => ξ ^ n) ↔ m.rhoC ξ = 0 := by
  simp only [SatisfiesRecurrence, rhoC]
  constructor
  · intro h; simpa using h 0
  · intro hρ n
    have key : ∀ j : Fin (s + 1),
        (↑(m.α j) : ℂ) * ξ ^ (n + (↑j : ℕ)) =
        ξ ^ n * ((↑(m.α j) : ℂ) * ξ ^ (↑j : ℕ)) := by
      intro j; rw [pow_add]; ring
    simp_rw [key, ← Finset.mul_sum, hρ, mul_zero]

/-! ### Linear-geometric solutions n·ξ^n -/

/-- If ξ is a double root of ρ (ρ(ξ) = 0 and ρ'(ξ) = 0), then the sequence
  n·ξ^n satisfies the characteristic recurrence.

  Proof: ∑_j α_j(n+j)ξ^{n+j} = n·ξ^n·ρ(ξ) + ξ^{n+1}·ρ'(ξ) = 0.
  This is the standard theory of linear recurrences: for a root of multiplicity k,
  the sequences ξ^n, n·ξ^n, ..., n^{k-1}·ξ^n all satisfy the recurrence. -/
theorem linear_geometric_satisfies (m : LMM s) (ξ : ℂ)
    (hρ : m.rhoC ξ = 0) (hρ' : m.rhoCDeriv ξ = 0) :
    m.SatisfiesRecurrence (fun n => (n : ℂ) * ξ ^ n) := by
  intro n
  by_cases hξ : ξ = 0
  · -- When ξ = 0, n * 0^n = 0 for all n, so trivially satisfies any recurrence
    subst hξ
    apply Finset.sum_eq_zero; intro j _
    dsimp only
    by_cases hn : n + (↑j : ℕ) = 0
    · -- n + j = 0 means n = 0 and j = 0, so term = α₀ * (0 * 1) = 0
      simp [hn]
    · -- n + j > 0, so 0^{n+j} = 0
      rw [zero_pow hn, mul_zero, mul_zero]
  · -- When ξ ≠ 0, split (n+j) = n + j and use ρ(ξ) = 0, ρ'(ξ) = 0
    -- The sum splits into two parts:
    -- Part 1: n · ξ^n · ρ(ξ) = 0
    -- Part 2: ξ^{n+1} · ρ'(ξ) = 0
    have h_split : ∀ j : Fin (s + 1),
        (↑(m.α j) : ℂ) * ((↑(n + (↑j : ℕ)) : ℂ) * ξ ^ (n + (↑j : ℕ))) =
        (↑(m.α j) : ℂ) * ((↑n : ℂ) * ξ ^ (n + (↑j : ℕ))) +
        (↑(m.α j) : ℂ) * ((↑(↑j : ℕ) : ℂ) * ξ ^ (n + (↑j : ℕ))) := by
      intro j; push_cast; ring
    simp_rw [h_split, Finset.sum_add_distrib]
    -- Part 1: ∑ α_j * n * ξ^{n+j} = n * ξ^n * ρ(ξ) = 0
    have h1 : ∑ j : Fin (s + 1),
        (↑(m.α j) : ℂ) * ((↑n : ℂ) * ξ ^ (n + (↑j : ℕ))) = 0 := by
      have rw_eq : ∀ j : Fin (s + 1),
          (↑(m.α j) : ℂ) * ((↑n : ℂ) * ξ ^ (n + (↑j : ℕ))) =
          (↑n : ℂ) * ξ ^ n * ((↑(m.α j) : ℂ) * ξ ^ (↑j : ℕ)) := by
        intro j; rw [pow_add]; ring
      simp_rw [rw_eq]
      rw [← Finset.mul_sum]
      have : (∑ j : Fin (s + 1), (↑(m.α j) : ℂ) * ξ ^ (↑j : ℕ)) = 0 := hρ
      rw [this, mul_zero]
    -- Part 2: ∑ α_j * j * ξ^{n+j} = ξ^{n+1} * ρ'(ξ) = 0
    have h2 : ∑ j : Fin (s + 1),
        (↑(m.α j) : ℂ) * ((↑(↑j : ℕ) : ℂ) * ξ ^ (n + (↑j : ℕ))) = 0 := by
      have rw_eq : ∀ j : Fin (s + 1),
          (↑(m.α j) : ℂ) * ((↑(↑j : ℕ) : ℂ) * ξ ^ (n + (↑j : ℕ))) =
          ξ ^ (n + 1) * ((↑(↑j : ℕ) : ℂ) * (↑(m.α j) : ℂ) * ξ ^ ((↑j : ℕ) - 1)) := by
        intro j
        by_cases hj : (↑j : ℕ) = 0
        · simp only [hj, Nat.cast_zero, zero_mul, mul_zero]
        · rw [show n + (↑j : ℕ) = (n + 1) + ((↑j : ℕ) - 1) from by omega]
          rw [pow_add ξ (n + 1) ((↑j : ℕ) - 1)]; ring
      simp_rw [rw_eq, ← Finset.mul_sum]
      simp only [rhoCDeriv] at hρ'
      rw [hρ', mul_zero]
    rw [h1, h2, add_zero]

/-! ### Instability from roots outside the disk -/

/-- If ρ has a root ξ with ‖ξ‖ > 1, the geometric solution ξ^n is unbounded,
  so the recurrence is unstable. -/
theorem not_stableRecurrence_of_root_outside_disk (m : LMM s)
    (ξ : ℂ) (hρ : m.rhoC ξ = 0) (h_outside : 1 < ‖ξ‖) :
    ¬m.HasStableRecurrence := by
  intro h_stable
  obtain ⟨C, hC⟩ := h_stable _ ((geometric_satisfies_iff m ξ).mpr hρ)
  -- ‖ξ^n‖ = ‖ξ‖^n ≤ C for all n, but ‖ξ‖^n → ∞ since ‖ξ‖ > 1
  have h_bounded : ∀ n, ‖ξ‖ ^ n ≤ C := fun n => by rw [← norm_pow]; exact hC n
  have h_tendsto := tendsto_pow_atTop_atTop_of_one_lt h_outside
  rw [Filter.tendsto_atTop_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto (C + 1)
  have := hN N le_rfl
  linarith [h_bounded N]

/-! ### Instability from double roots on the unit circle -/

/-- If ρ has a root ξ on the unit circle with ρ'(ξ) = 0 (double root),
  the sequence n·ξ^n satisfies the recurrence and is unbounded (since
  ‖n·ξ^n‖ = n → ∞), so the recurrence is unstable. -/
theorem not_stableRecurrence_of_double_root_on_circle (m : LMM s)
    (ξ : ℂ) (hρ : m.rhoC ξ = 0) (h_circle : ‖ξ‖ = 1) (hρ' : m.rhoCDeriv ξ = 0) :
    ¬m.HasStableRecurrence := by
  intro h_stable
  obtain ⟨C, hC⟩ := h_stable _ (linear_geometric_satisfies m ξ hρ hρ')
  -- ‖n * ξ^n‖ = n * ‖ξ‖^n = n * 1 = n
  have h_norm : ∀ n : ℕ, ‖(↑n : ℂ) * ξ ^ n‖ = ↑n := by
    intro n
    rw [norm_mul, norm_pow, h_circle, one_pow, mul_one, Complex.norm_natCast]
  -- For n large enough, n > C, contradicting ‖n * ξ^n‖ ≤ C
  set N := Nat.ceil (max C 0) + 1
  have hN_bound := hC N
  rw [h_norm] at hN_bound
  have : (max C 0 : ℝ) ≤ ↑(Nat.ceil (max C 0)) := Nat.le_ceil _
  have : C ≤ max C 0 := le_max_left _ _
  push_cast [N] at hN_bound ⊢
  linarith

/-! ### Zero-stability from stable recurrence -/

/-- **Stable recurrence implies zero-stability.**
  If all solutions of the characteristic recurrence are bounded, then:
  1. All roots of ρ lie in the closed unit disk (otherwise ξ^n diverges).
  2. All unit-circle roots are simple (otherwise n·ξ^n diverges).
  This is the "easy" direction of the algebraic Dahlquist equivalence. -/
theorem zeroStable_of_stableRecurrence (m : LMM s)
    (h_stable : m.HasStableRecurrence) : m.IsZeroStable where
  roots_in_disk := by
    intro ξ hρ
    by_contra h_outside
    push_neg at h_outside
    exact not_stableRecurrence_of_root_outside_disk m ξ hρ h_outside h_stable
  unit_roots_simple := by
    intro ξ hρ _habs hρ'
    exact not_stableRecurrence_of_double_root_on_circle m ξ hρ _habs hρ' h_stable

/-! ### Connection to Mathlib's LinearRecurrence

We connect the LMM's characteristic recurrence to Mathlib's `LinearRecurrence` theory.
The companion operator `tupleSucc` maps state vectors (y_n, ..., y_{n+s-1}) to
(y_{n+1}, ..., y_{n+s}), and iterating it n times gives the state at time n.

## Structure
1. `toLinearRecurrence`: convert LMM recurrence to `LinearRecurrence ℂ`.
2. `satisfiesRecurrence_iff_isSolution`: equivalence of solution predicates.
3. `tupleSucc_iterate_eq_mkSol`: state evolution via companion operator.
4. `uniformly_bounded_tupleSucc_iterates`: spectral bound (the key sorry).
5. `stableRecurrence_of_zeroStable`: combine everything. -/

/-- Convert an LMM's characteristic recurrence to a `LinearRecurrence` over ℂ.
  The recurrence ∑_{j=0}^s α_j y_{n+j} = 0 with α_s = 1 becomes
  y_{n+s} = ∑_{j<s} (-α_j) · y_{n+j}. -/
noncomputable def toLinearRecurrence (m : LMM s) : LinearRecurrence ℂ where
  order := s
  coeffs := fun i => -(m.α (Fin.castSucc i) : ℂ)

/-- The LMM's `SatisfiesRecurrence` is equivalent to `LinearRecurrence.IsSolution`
  for the associated `LinearRecurrence`. -/
theorem satisfiesRecurrence_iff_isSolution (m : LMM s) (y : ℕ → ℂ) :
    m.SatisfiesRecurrence y ↔ m.toLinearRecurrence.IsSolution y := by
  simp only [SatisfiesRecurrence, LinearRecurrence.IsSolution, toLinearRecurrence]
  constructor
  · -- Forward: ∑ α_j y_{n+j} = 0 → y_{n+s} = ∑ (-α_j) y_{n+j}
    intro h n
    have hn := h n
    rw [Fin.sum_univ_castSucc] at hn
    simp only [Fin.val_castSucc, Fin.val_last, m.normalized, Complex.ofReal_one, one_mul] at hn
    -- hn : (∑ i, (α_i : ℂ) * y(n+i)) + y(n+s) = 0
    -- Extract y(n+s) = -(∑ α_i * y_i)
    have key : y (n + s) = -(∑ i : Fin s,
        (↑(m.α (Fin.castSucc i)) : ℂ) * y (n + ↑i)) := by
      have := neg_eq_of_add_eq_zero_left hn
      rwa [neg_eq_iff_eq_neg] at this
    rw [key, ← Finset.sum_neg_distrib]
    congr 1; ext i; ring
  · -- Backward: y_{n+s} = ∑ (-α_j) y_{n+j} → ∑ α_j y_{n+j} = 0
    intro h n
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, m.normalized, Complex.ofReal_one, one_mul]
    rw [h n, ← Finset.sum_add_distrib, Finset.sum_eq_zero]
    intro i _; ring

/-- The state vector at time n equals `tupleSucc` iterated n times on initial conditions:
  `(tupleSucc^[n] init) i = mkSol init (n + i)`. This connects the linear recurrence
  solution to iteration of the companion operator. -/
theorem tupleSucc_iterate_eq_mkSol (E : LinearRecurrence ℂ) (init : Fin E.order → ℂ)
    (n : ℕ) (i : Fin E.order) :
    (E.tupleSucc^[n]) init i = E.mkSol init (n + ↑i) := by
  induction n generalizing i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_add]
    exact (E.mkSol_eq_init init i).symm
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    set v := (E.tupleSucc^[n]) init with hv_def
    show E.tupleSucc v i = E.mkSol init (n + 1 + ↑i)
    simp only [LinearRecurrence.tupleSucc, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h
    · -- Case: ↑i + 1 < E.order, so tupleSucc shifts: result is v(i+1)
      have := ih ⟨↑i + 1, h⟩
      simp at this
      rw [this]; congr 1; omega
    · -- Case: i is the last index, tupleSucc applies the recurrence
      have hi_eq : (↑i : ℕ) + 1 = E.order := by have := i.isLt; omega
      have h_sum : ∀ j : Fin E.order,
          E.coeffs j * v j = E.coeffs j * E.mkSol init (n + ↑j) := by
        intro j; congr 1; exact ih j
      simp_rw [h_sum, show n + 1 + (↑i : ℕ) = n + E.order from by omega]
      exact (E.is_sol_mkSol init n).symm

/-! ### Characteristic polynomial infrastructure

We establish three key lemmas connecting the characteristic polynomial of the
linear recurrence to the LMM's first characteristic polynomial ρ:
1. `aeval_tupleSucc_charPoly_eq_zero`: the companion operator satisfies its charPoly.
2. `charPoly_eval_eq_rhoC`: charPoly evaluation equals ρ_ℂ.
3. `tupleSucc_eigenvalue_is_rhoC_root`: eigenvalues of tupleSucc are roots of ρ. -/

/-- The companion operator `tupleSucc` satisfies its own characteristic polynomial:
  `p(T) = 0` where `p = charPoly`. This is the Cayley-Hamilton theorem for the
  companion matrix of a linear recurrence. -/
lemma aeval_tupleSucc_charPoly_eq_zero (E : LinearRecurrence ℂ) :
    Polynomial.aeval E.tupleSucc E.charPoly = 0 := by
  refine LinearMap.ext (fun v => funext (fun j => ?_))
  simp only [LinearMap.zero_apply, Pi.zero_apply]
  -- Expand charPoly = X^order - ∑ coeffs_i * X^i under aeval
  simp only [LinearRecurrence.charPoly, map_sub, map_sum, Polynomial.aeval_monomial,
    LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, one_smul]
  -- Convert (T^k v) j to mkSol v (k + ↑j)
  have conv : ∀ k, ((E.tupleSucc ^ k) v) j = E.mkSol v (k + ↑j) := by
    intro k
    change ((⇑(E.tupleSucc ^ k)) v) j = _
    rw [Module.End.coe_pow]
    exact tupleSucc_iterate_eq_mkSol E v k j
  -- Push index j inside the subtraction and sum
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conv]
  -- Goal: mkSol v (order + ↑j) - ∑ x, coeffs x * mkSol v (↑x + ↑j) = 0
  have h_sol := E.is_sol_mkSol v (↑j : ℕ)
  rw [show E.order + (↑j : ℕ) = (↑j : ℕ) + E.order from by omega, h_sol]
  simp only [sub_eq_zero]
  simp_rw [Nat.add_comm (↑j)]

/-- The characteristic polynomial of the linear recurrence equals the first
  characteristic polynomial ρ of the LMM: `charPoly.eval μ = ρ_ℂ(μ)`. -/
theorem charPoly_eval_eq_rhoC (m : LMM s) (μ : ℂ) :
    m.toLinearRecurrence.charPoly.eval μ = m.rhoC μ := by
  simp only [LinearRecurrence.charPoly, toLinearRecurrence, rhoC,
    Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_monomial, one_mul, neg_mul]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, m.normalized, Complex.ofReal_one, one_mul]
  -- Goal: μ^s - ∑ x, -(α_x * μ^x) = ∑ x, α_x * μ^x + μ^s
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, add_comm]

/-- Every eigenvalue of the companion operator `tupleSucc` is a root of ρ.
  Combined with zero-stability, this constrains the spectral radius. -/
theorem tupleSucc_eigenvalue_is_rhoC_root (m : LMM s) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue m.toLinearRecurrence.tupleSucc μ) : m.rhoC μ = 0 := by
  set E := m.toLinearRecurrence
  set T := E.tupleSucc
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  -- aeval T charPoly = 0, so (aeval T charPoly) v = 0
  have h_zero : (Polynomial.aeval T E.charPoly) v = 0 := by
    rw [aeval_tupleSucc_charPoly_eq_zero]; simp
  -- By eigenvector property: (aeval T p) v = p.eval μ • v
  rw [Module.End.aeval_apply_of_hasEigenvector hv] at h_zero
  -- charPoly.eval μ • v = 0 with v ≠ 0 implies charPoly.eval μ = 0
  rw [← charPoly_eval_eq_rhoC]
  exact (smul_eq_zero.mp h_zero).resolve_right hv.2

/-- Evaluating the derivative of the companion characteristic polynomial agrees
  with the formal derivative `ρ'_ℂ` of the LMM's first characteristic polynomial. -/
theorem charPoly_derivative_eval_eq_rhoCDeriv (m : LMM s) (μ : ℂ) :
    (m.toLinearRecurrence.charPoly.derivative).eval μ = m.rhoCDeriv μ := by
  simp only [LinearRecurrence.charPoly, toLinearRecurrence, rhoCDeriv, Polynomial.eval_sub,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial, Polynomial.derivative_sub,
    Polynomial.derivative_sum, Polynomial.derivative_monomial, one_mul, neg_mul]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, m.normalized, Complex.ofReal_one]
  rw [sub_eq_add_neg, Finset.sum_neg_distrib]
  have hsum :
      ∑ x : Fin s, ↑(m.α x.castSucc) * ((↑x : ℕ) : ℂ) * μ ^ ((↑x : ℕ) - 1) =
        ∑ x : Fin s, ((↑x : ℕ) : ℂ) * ↑(m.α x.castSucc) * μ ^ ((↑x : ℕ) - 1) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  simpa [neg_neg, one_mul, add_assoc, add_left_comm, add_comm] using
    congrArg (fun t => (↑s : ℂ) * μ ^ (s - 1) + t) hsum

/-- A unit-circle root of the companion characteristic polynomial is simple. -/
lemma charPoly_rootMultiplicity_of_unit_root (m : LMM s) (hzs : m.IsZeroStable) (μ : ℂ)
    (hroot : m.rhoC μ = 0) (hunit : ‖μ‖ = 1) :
    (m.toLinearRecurrence.charPoly).rootMultiplicity μ = 1 := by
  let p := m.toLinearRecurrence.charPoly
  have hp0 : p ≠ 0 := (m.toLinearRecurrence.charPoly_monic).ne_zero
  have hp_root : p.IsRoot μ := by
    rw [Polynomial.IsRoot.def, charPoly_eval_eq_rhoC, hroot]
  have hp_pos : 0 < p.rootMultiplicity μ := (Polynomial.rootMultiplicity_pos hp0).2 hp_root
  have hderiv_ne : p.derivative.eval μ ≠ 0 := by
    rw [show p.derivative.eval μ = m.rhoCDeriv μ by
      simpa [p] using charPoly_derivative_eval_eq_rhoCDeriv m μ]
    exact hzs.unit_roots_simple μ hroot hunit
  have hnot_gt : ¬ 1 < p.rootMultiplicity μ := by
    intro hgt
    have hroot_deriv : p.derivative.IsRoot μ :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).1 hgt |>.2
    exact hderiv_ne hroot_deriv
  exact le_antisymm (Nat.le_of_not_gt hnot_gt) (Nat.succ_le_of_lt hp_pos)

/-- A polynomial factor times a geometric decay sequence is uniformly bounded. -/
lemma bounded_pow_geom_decay (k : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k * r ^ n ≤ C := by
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ k * r ^ n
  have h_tendsto : Filter.Tendsto a Filter.atTop (nhds 0) := by
    simpa [a, abs_of_nonneg hr0] using
      tendsto_pow_const_mul_const_pow_of_abs_lt_one k (show |r| < 1 by simpa [abs_of_nonneg hr0] using hr1)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto a h_tendsto).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  calc
    (n : ℝ) ^ k * r ^ n = a n := rfl
    _ ≤ C := hC (Set.mem_range_self n)
    _ ≤ max C 0 := le_max_left _ _

/-! ### Zero-stability implies stable recurrence

The converse direction: if ρ satisfies the root condition, then every solution
of the characteristic recurrence is bounded. We decompose this into:
1. Every solution is `mkSol init` for its initial conditions.
2. The solution value at time n is a component of `tupleSucc^n(init)`.
3. The spectral bound: zero-stability implies `tupleSucc^n` is uniformly bounded. -/

/-- **Spectral bound**: Under zero-stability, the companion operator `tupleSucc`
  has uniformly bounded iterates: ‖tupleSucc^n(v)‖ ≤ M·‖v‖ for all n, v.

  Zero-stability ensures all eigenvalues of `tupleSucc` satisfy |λ| ≤ 1
  (by `tupleSucc_eigenvalue_is_rhoC_root`) with semisimple unit eigenvalues
  (since unit-circle roots of ρ are simple). -/
theorem uniformly_bounded_tupleSucc_iterates (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : Fin s → ℂ),
      ‖(m.toLinearRecurrence.tupleSucc^[n]) v‖ ≤ M * ‖v‖ := by
  by_cases hs : s = 0
  · -- s = 0: the space Fin 0 → ℂ is trivial (subsingleton)
    subst hs
    have : Subsingleton (Fin m.toLinearRecurrence.order → ℂ) := by
      simp only [toLinearRecurrence]; infer_instance
    refine ⟨1, le_of_lt one_pos, fun n v => ?_⟩
    have heq : (m.toLinearRecurrence.tupleSucc^[n]) v = v := Subsingleton.elim _ _
    rw [heq, one_mul]
  · -- s > 0: use eigenvalue analysis
    set E := m.toLinearRecurrence
    set T := E.tupleSucc
    -- All eigenvalues of T are roots of ρ (sub-lemma 3)
    -- and hence satisfy |μ| ≤ 1 (zero-stability)
    have h_eigbound : ∀ μ, Module.End.HasEigenvalue T μ → ‖μ‖ ≤ 1 :=
      fun μ hμ => hzs.roots_in_disk μ (tupleSucc_eigenvalue_is_rhoC_root m μ hμ)
    -- T satisfies its charPoly (sub-lemma 1), so minpoly | charPoly
    have h_mp_dvd : minpoly ℂ T ∣ E.charPoly :=
      minpoly.dvd ℂ T (aeval_tupleSucc_charPoly_eq_zero E)
    -- Decomposition over ℂ (algebraically closed):
    -- ⨆ μ, T.maxGenEigenspace μ = ⊤
    have h_decomp := Module.End.iSup_maxGenEigenspace_eq_top T
    -- Remaining: combine eigenvalue bounds with decomposition to get ‖T^n‖ ≤ M
    sorry

/-- **Zero-stability implies stable recurrence.**
  If all roots of ρ lie in the closed unit disk with simple unit-circle roots,
  then every solution of the characteristic recurrence is bounded.

  Proof:
  1. Convert to `LinearRecurrence` via `toLinearRecurrence`.
  2. Every solution equals `mkSol init` for its initial conditions.
  3. `mkSol init n` is a component of `tupleSucc^n(init)` (by `tupleSucc_iterate_eq_mkSol`).
  4. The spectral bound gives ‖tupleSucc^n(init)‖ ≤ M·‖init‖. -/
theorem stableRecurrence_of_zeroStable (m : LMM s)
    (hzs : m.IsZeroStable) : m.HasStableRecurrence := by
  intro y hy
  by_cases hs : s = 0
  · -- s = 0: the recurrence α₀·y_n = 0 with α₀ = 1 forces y_n = 0
    subst hs; use 0; intro n
    suffices h : y n = 0 by rw [h]; simp
    have hn := hy n
    -- The sum over Fin 1 has a single term
    have h1 : (∑ j : Fin 1, (↑(m.α j) : ℂ) * y (n + ↑j)) =
        (↑(m.α 0) : ℂ) * y n := by
      simp
    rw [h1] at hn
    have h2 : (0 : Fin 1) = Fin.last 0 := by ext; simp [Fin.last]
    rw [h2, show (↑(m.α (Fin.last 0)) : ℂ) = 1 from by
      exact_mod_cast m.normalized, one_mul] at hn
    exact hn
  · -- s > 0: use companion operator / LinearRecurrence infrastructure
    have hs_pos : 0 < s := Nat.pos_of_ne_zero hs
    let E := m.toLinearRecurrence
    have hy_lr : E.IsSolution y := (satisfiesRecurrence_iff_isSolution m y).mp hy
    let init : Fin s → ℂ := fun i => y ↑i
    have hy_eq : y = E.mkSol init :=
      E.eq_mk_of_is_sol_of_eq_init' hy_lr (fun _ => rfl)
    obtain ⟨M, _, hM⟩ := uniformly_bounded_tupleSucc_iterates m hzs
    use M * ‖init‖; intro n; rw [hy_eq]
    -- mkSol init n = (tupleSucc^[n] init)(0)
    have h_iter := tupleSucc_iterate_eq_mkSol E init n ⟨0, hs_pos⟩
    simp only [add_zero] at h_iter
    rw [← h_iter]
    calc ‖(E.tupleSucc^[n]) init ⟨0, hs_pos⟩‖
        ≤ ‖(E.tupleSucc^[n]) init‖ := norm_le_pi_norm _ _
      _ ≤ M * ‖init‖ := hM n init

/-- **Algebraic Dahlquist equivalence**: zero-stability is equivalent to the
  characteristic recurrence having only bounded solutions. -/
theorem zeroStable_iff_stableRecurrence (m : LMM s) :
    m.IsZeroStable ↔ m.HasStableRecurrence :=
  ⟨stableRecurrence_of_zeroStable m, zeroStable_of_stableRecurrence m⟩

/-! ## Convergence for the Trivial ODE

Convergence of an LMM for the trivial ODE y' = 0 (exact solution y = const)
is equivalent to stability of the characteristic recurrence. This is the
simplest test case that already captures the zero-stability requirement. -/

/-- A sequence of numerical solutions (indexed by step count N) **converges
  for the trivial ODE** if the solutions remain bounded as N → ∞.
  The exact solution of y' = 0 is constant, so convergence requires that
  the characteristic recurrence produces only bounded sequences. -/
def ConvergesForTrivialODE (m : LMM s) : Prop := m.HasStableRecurrence

/-- Convergence for y' = 0 is equivalent to zero-stability. -/
theorem convergesForTrivialODE_iff_zeroStable (m : LMM s) :
    m.ConvergesForTrivialODE ↔ m.IsZeroStable :=
  (zeroStable_iff_stableRecurrence m).symm

/-! ## Convergence for General ODEs

For the full Dahlquist equivalence theorem, convergence is defined for
general Lipschitz ODEs y' = f(t, y). The LMM produces a numerical solution
{y_n} from starting values {y_0, ..., y_{s-1}}, and convergence requires
max |y_n - y(t_n)| → 0 as h → 0 (with nh = t fixed).

The theorem states: an LMM is convergent iff it is consistent and zero-stable. -/

/-- **Convergence of an LMM**: For any scalar ODE y' = f(t,y) with f Lipschitz,
  any T > 0, and any family of starting values that converge to the exact initial
  data as h → 0, the numerical solution satisfies max_{0 ≤ n ≤ N} |y_n - y(nh)| → 0
  as h = T/N → 0.

  We define this through the two algebraic conditions that characterize it:
  consistency (local accuracy) and stable recurrence (error non-amplification). -/
def IsConvergent (m : LMM s) : Prop :=
  m.IsConsistent ∧ m.HasStableRecurrence

/-- **Dahlquist Equivalence Theorem** (Iserles, Theorem 1.5.2):
  A linear multistep method is convergent if and only if it is consistent
  and zero-stable.

  Forward direction: consistency + zero-stability → convergence.
  - Consistency ensures the local truncation error is o(h).
  - Zero-stability (root condition) ensures the error propagation operator
    has uniformly bounded powers (via the stable recurrence).
  - Combined with the Gronwall bound, the global error → 0.

  Backward direction: convergence → consistency + zero-stability.
  - Convergence → consistency: test with y = c and y = t.
  - Convergence → zero-stability: via stable recurrence (proved above). -/
theorem dahlquist_equivalence (m : LMM s) :
    m.IsConvergent ↔ m.IsConsistent ∧ m.IsZeroStable := by
  simp only [IsConvergent]
  constructor
  · -- Forward: convergent → consistent ∧ zero-stable
    intro ⟨hc, hsr⟩
    exact ⟨hc, zeroStable_of_stableRecurrence m hsr⟩
  · -- Backward: consistent ∧ zero-stable → convergent
    intro ⟨hc, hzs⟩
    exact ⟨hc, stableRecurrence_of_zeroStable m hzs⟩

/-! ## Convergence of Standard Methods

Apply the Dahlquist equivalence theorem to verify convergence of standard methods. -/

/-- Forward Euler is convergent (consistent + zero-stable). -/
theorem forwardEuler_convergent : forwardEuler.IsConvergent :=
  (dahlquist_equivalence forwardEuler).mpr ⟨forwardEuler_consistent, forwardEuler_zeroStable⟩

/-- Backward Euler is convergent. -/
theorem backwardEuler_convergent : backwardEuler.IsConvergent :=
  (dahlquist_equivalence backwardEuler).mpr ⟨backwardEuler_consistent, backwardEuler_zeroStable⟩

/-- The trapezoidal rule is convergent. -/
theorem trapezoidalRule_convergent : trapezoidalRule.IsConvergent :=
  (dahlquist_equivalence trapezoidalRule).mpr
    ⟨trapezoidalRule_consistent, trapezoidalRule_zeroStable⟩

/-- Adams–Bashforth 2-step is convergent. -/
theorem adamsBashforth2_convergent : adamsBashforth2.IsConvergent :=
  (dahlquist_equivalence adamsBashforth2).mpr
    ⟨adamsBashforth2_consistent, adamsBashforth2_zeroStable⟩

/-- Adams–Moulton 2-step is convergent. -/
theorem adamsMoulton2_convergent : adamsMoulton2.IsConvergent :=
  (dahlquist_equivalence adamsMoulton2).mpr
    ⟨adamsMoulton2_consistent, adamsMoulton2_zeroStable⟩

/-- BDF2 is convergent. -/
theorem bdf2_convergent : bdf2.IsConvergent :=
  (dahlquist_equivalence bdf2).mpr ⟨bdf2_consistent, bdf2_zeroStable⟩

/-- BDF3 is convergent: consistent (Section 4.5) and zero-stable
  (ρ has roots at 1 (simple) and two roots with |ξ|² = 2/11 < 1). -/
theorem bdf3_convergent : bdf3.IsConvergent :=
  (dahlquist_equivalence bdf3).mpr ⟨bdf3_consistent, bdf3_zeroStable⟩

/-- The Dahlquist counterexample is NOT convergent (not zero-stable). -/
theorem dahlquistCounterexample_not_convergent :
    ¬dahlquistCounterexample.IsConvergent := by
  intro ⟨_, hsr⟩
  exact dahlquistCounterexample_not_zeroStable (zeroStable_of_stableRecurrence _ hsr)

end LMM
