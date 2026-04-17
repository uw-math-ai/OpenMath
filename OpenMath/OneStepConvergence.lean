import OpenMath.EulerConvergence

open Set Filter Real

/-!
# Convergence theorem for one-step methods

This file formalizes the standard convergence framework for one-step methods
from Iserles, Section 4.2.
-/

section OneStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A one-step method is determined by its increment map `Φ(x, y, h)`. -/
structure OneStepMethod (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Φ : ℝ → E → ℝ → E

namespace OneStepMethod

/-- Consistency at zero stepsize. -/
def IsConsistent (m : OneStepMethod E) (f : ℝ → E → E) : Prop :=
  ∀ x y, m.Φ x y 0 = f x y

/-- Uniform Lipschitz continuity of `Φ` in the state variable on a spacetime box. -/
def IsLipschitzInY (m : OneStepMethod E) (L : ℝ) (a b : ℝ) (hmax : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ h ∈ Set.Icc 0 hmax, ∀ u v : E,
    ‖m.Φ x u h - m.Φ x v h‖ ≤ L * ‖u - v‖

/-- The usual local truncation error per unit stepsize. -/
noncomputable def localTruncationError (m : OneStepMethod E) (y : ℝ → E)
    (x h : ℝ) : E :=
  (h⁻¹ : ℝ) • (y (x + h) - y x) - m.Φ x (y x) h

/-- One-step recurrence started at `(x0, y0)` with constant stepsize `h`. -/
def numericalSolution (m : OneStepMethod E) (x0 h : ℝ) (y0 : E) : ℕ → E
  | 0 => y0
  | n + 1 => numericalSolution m x0 h y0 n +
      h • m.Φ (x0 + n * h) (numericalSolution m x0 h y0 n) h

@[simp] theorem numericalSolution_zero (m : OneStepMethod E) (x0 h : ℝ) (y0 : E) :
    numericalSolution m x0 h y0 0 = y0 := rfl

@[simp] theorem numericalSolution_succ (m : OneStepMethod E) (x0 h : ℝ) (y0 : E) (n : ℕ) :
    numericalSolution m x0 h y0 (n + 1) =
      numericalSolution m x0 h y0 n +
        h • m.Φ (x0 + n * h) (numericalSolution m x0 h y0 n) h := rfl

/-- Exact one-step defect, i.e. the residual of the exact solution in the numerical scheme. -/
def exactStepDefect (m : OneStepMethod E) (y : ℝ → E) (x h : ℝ) : E :=
  y (x + h) - (y x + h • m.Φ x (y x) h)

/-- Sequence of pointwise global errors. -/
def globalError (m : OneStepMethod E) (x0 h : ℝ) (y0 : E) (y : ℝ → E) : ℕ → ℝ :=
  fun n => ‖numericalSolution m x0 h y0 n - y (x0 + n * h)‖

/-- Abstract convergence along a family of step sizes. -/
def IsConvergent (m : OneStepMethod E) (a b L : ℝ) : Prop :=
  ∀ (x0 : ℝ) (y : ℝ → E) (hseq τseq : ℕ → ℝ) (Nseq : ℕ → ℕ),
    a ≤ x0 →
    (∀ k, 0 ≤ hseq k) →
    (∀ k, 0 ≤ τseq k) →
    Tendsto hseq atTop (nhds 0) →
    Tendsto τseq atTop (nhds 0) →
    (∀ k, x0 + (Nseq k : ℝ) * hseq k ≤ b) →
    (∀ k, IsLipschitzInY m L a b (hseq k)) →
    (∀ k, numericalSolution m x0 (hseq k) (y x0) (0 : ℕ) = y x0) →
    (∀ k n, n < Nseq k →
      ‖exactStepDefect m y (x0 + n * hseq k) (hseq k)‖ ≤ hseq k * τseq k) →
    Tendsto
      (fun k =>
        ‖numericalSolution m x0 (hseq k) (y x0) (Nseq k) -
          y (x0 + (Nseq k : ℝ) * hseq k)‖)
      atTop (nhds 0)

theorem one_step_error_recursion
    (m : OneStepMethod E) {a b x0 h L τ : ℝ} {y : ℝ → E} {N : ℕ}
    (hh_nonneg : 0 ≤ h)
    (hLip : IsLipschitzInY m L a b h)
    (hτ_nonneg : 0 ≤ τ)
    (hx : ∀ n, n ≤ N → x0 + n * h ∈ Set.Icc a b)
    (hdefect : ∀ n, n < N →
      ‖exactStepDefect m y (x0 + n * h) h‖ ≤ h * τ) :
    ∀ n, n < N →
      globalError m x0 h (y x0) y (n + 1) ≤
        (1 + h * L) * globalError m x0 h (y x0) y n + h * τ := by
  intro n hn
  have hx_n : x0 + n * h ∈ Set.Icc a b := hx n (Nat.le_of_lt hn)
  have hstep : h ∈ Set.Icc 0 h := ⟨hh_nonneg, le_rfl⟩
  have hLip' :
      ‖m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
          m.Φ (x0 + n * h) (y (x0 + n * h)) h‖
        ≤ L * ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖ :=
    hLip (x0 + n * h) hx_n h hstep _ _
  have hdefect' := hdefect n hn
  have hnext : x0 + ((n + 1 : ℕ) : ℝ) * h = x0 + (n : ℝ) * h + h := by
    norm_num
    ring
  have hdecomp :
      numericalSolution m x0 h (y x0) (n + 1) - y (x0 + n * h + h) =
        (numericalSolution m x0 h (y x0) n - y (x0 + n * h)) +
          h • (m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
            m.Φ (x0 + n * h) (y (x0 + n * h)) h) -
          exactStepDefect m y (x0 + n * h) h := by
    simp [numericalSolution, exactStepDefect, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  rw [globalError, hnext]
  rw [hdecomp]
  calc
    ‖(numericalSolution m x0 h (y x0) n - y (x0 + n * h)) +
        h •
          (m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
            m.Φ (x0 + n * h) (y (x0 + n * h)) h) -
        exactStepDefect m y (x0 + n * h) h‖
      ≤ ‖(numericalSolution m x0 h (y x0) n - y (x0 + n * h)) +
            h •
              (m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
                m.Φ (x0 + n * h) (y (x0 + n * h)) h)‖ +
          ‖exactStepDefect m y (x0 + n * h) h‖ := by
            exact norm_sub_le _ _
    _ ≤ ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖ +
          ‖h •
              (m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
                m.Φ (x0 + n * h) (y (x0 + n * h)) h)‖ +
          ‖exactStepDefect m y (x0 + n * h) h‖ := by
            gcongr
            exact norm_add_le _ _
    _ = ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖ +
          h * ‖m.Φ (x0 + n * h) (numericalSolution m x0 h (y x0) n) h -
              m.Φ (x0 + n * h) (y (x0 + n * h)) h‖ +
          ‖exactStepDefect m y (x0 + n * h) h‖ := by
            rw [norm_smul, Real.norm_of_nonneg hh_nonneg]
    _ ≤ ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖ +
          h * (L * ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖) +
          ‖exactStepDefect m y (x0 + n * h) h‖ := by
            gcongr
    _ ≤ ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖ +
          h * (L * ‖numericalSolution m x0 h (y x0) n - y (x0 + n * h)‖) + h * τ := by
            gcongr
    _ = (1 + h * L) * globalError m x0 h (y x0) y n + h * τ := by
            simp [globalError]
            ring

theorem one_step_global_error_bound
    (m : OneStepMethod E) {a b x0 h L τ : ℝ} {y : ℝ → E} {N : ℕ}
    (hh_nonneg : 0 ≤ h)
    (hLip : IsLipschitzInY m L a b h)
    (hL_nonneg : 0 ≤ L)
    (hτ_nonneg : 0 ≤ τ)
    (hx : ∀ n, n ≤ N → x0 + n * h ∈ Set.Icc a b)
    (hdefect : ∀ n, n < N →
      ‖exactStepDefect m y (x0 + n * h) h‖ ≤ h * τ)
    (n : ℕ) (hn : n ≤ N) :
    globalError m x0 h (y x0) y n ≤ gronwallBound 0 L τ ((n : ℝ) * h) := by
  have hrec :
      ∀ i, i < n →
        globalError m x0 h (y x0) y (i + 1) ≤
          (1 + h * L) * globalError m x0 h (y x0) y i + h * τ := by
    intro i hi
    exact one_step_error_recursion m hh_nonneg hLip hτ_nonneg hx hdefect i
      (lt_of_lt_of_le hi hn)
  have hbound :=
    theorem_212A
      (a := globalError m x0 h (y x0) y)
      (h := fun _ => h)
      L τ n
      (ha_nonneg := by
        intro i hi
        exact norm_nonneg _)
      (hh_nonneg := by
        intro i
        exact hh_nonneg)
      (hC_nonneg := hτ_nonneg)
      (hL_nonneg := hL_nonneg)
      (hrec := by
        intro i hi
        simpa [globalError] using hrec i hi)
  simpa [globalError, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hbound

theorem one_step_global_error_bound_exp
    (m : OneStepMethod E) {a b x0 h L τ : ℝ} {y : ℝ → E} {N n : ℕ}
    (hh_nonneg : 0 ≤ h)
    (hLip : IsLipschitzInY m L a b h)
    (hL_pos : 0 < L)
    (hτ_nonneg : 0 ≤ τ)
    (hx0 : a ≤ x0)
    (hx : ∀ k, k ≤ N → x0 + k * h ∈ Set.Icc a b)
    (hdefect : ∀ k, k < N →
      ‖exactStepDefect m y (x0 + k * h) h‖ ≤ h * τ)
    (hn : n ≤ N) :
    globalError m x0 h (y x0) y n ≤
      τ / L * (Real.exp (L * (b - a)) - 1) := by
  have hmain :=
    one_step_global_error_bound m hh_nonneg hLip (le_of_lt hL_pos) hτ_nonneg hx hdefect n hn
  have hnh_le : (n : ℝ) * h ≤ b - a := by
    have hx_n := hx n hn
    have hx_upper : x0 + (n : ℝ) * h ≤ b := hx_n.2
    linarith
  have hexp_le : Real.exp (L * ((n : ℝ) * h)) - 1 ≤ Real.exp (L * (b - a)) - 1 := by
    refine sub_le_sub_right ?_ 1
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnh_le (le_of_lt hL_pos))
  have hcoeff_nonneg : 0 ≤ τ / L := by
    exact div_nonneg hτ_nonneg (le_of_lt hL_pos)
  calc
    globalError m x0 h (y x0) y n ≤ gronwallBound 0 L τ ((n : ℝ) * h) := hmain
    _ = τ / L * (Real.exp (L * ((n : ℝ) * h)) - 1) := by
      rw [gronwallBound_of_K_ne_0 (ne_of_gt hL_pos)]
      ring
    _ ≤ τ / L * (Real.exp (L * (b - a)) - 1) := by
      gcongr

theorem one_step_convergence
    (m : OneStepMethod E) {a b L : ℝ}
    (hL_pos : 0 < L)
    (_hab : a < b) :
    IsConvergent m a b L := by
  intro x0 y hseq τseq Nseq hx0 hh_nonneg hτ_nonneg hhconv hτconv hxN hLip hinit hdefect
  let err : ℕ → ℝ := fun k =>
    ‖numericalSolution m x0 (hseq k) (y x0) (Nseq k) -
      y (x0 + (Nseq k : ℝ) * hseq k)‖
  let ub : ℕ → ℝ := fun k =>
    τseq k / L * (Real.exp (L * (b - a)) - 1)
  have hgrid : ∀ k n, n ≤ Nseq k → x0 + (n : ℝ) * hseq k ∈ Set.Icc a b := by
    intro k n hn
    refine ⟨?_, ?_⟩
    · have hnh_nonneg : 0 ≤ (n : ℝ) * hseq k := by
        exact mul_nonneg (by positivity) (hh_nonneg k)
      linarith
    · have hcast : (n : ℝ) ≤ (Nseq k : ℝ) := by
        exact_mod_cast hn
      have hmul_le : (n : ℝ) * hseq k ≤ (Nseq k : ℝ) * hseq k := by
        gcongr
        exact hh_nonneg k
      linarith [hxN k, hmul_le]
  have hub_le : ∀ k, err k ≤ ub k := by
    intro k
    have hbound :=
      one_step_global_error_bound_exp
        m
        (hh_nonneg k)
        (hLip k)
        hL_pos
        (hτ_nonneg k)
        hx0
        (fun n hn => hgrid k n hn)
        (hdefect k)
        (n := Nseq k)
        le_rfl
    simpa [err, ub, globalError] using hbound
  have hub_tendsto : Tendsto ub atTop (nhds 0) := by
    have htmp :
        Tendsto
          (fun k => τseq k / L * (Real.exp (L * (b - a)) - 1))
          atTop
          (nhds (0 / L * (Real.exp (L * (b - a)) - 1))) :=
      (hτconv.div_const L).mul_const (Real.exp (L * (b - a)) - 1)
    simpa [ub] using htmp
  have herr_tendsto : Tendsto err atTop (nhds 0) := by
    apply squeeze_zero
    · intro k
      exact norm_nonneg _
    · intro k
      exact hub_le k
    · exact hub_tendsto
  simpa [err] using herr_tendsto

/-- Forward Euler viewed as a one-step method. -/
def eulerMethod (f : ℝ → E → E) : OneStepMethod E where
  Φ x y _h := f x y

theorem euler_is_consistent (f : ℝ → E → E) :
    (eulerMethod f).IsConsistent f := by
  intro x y
  rfl

theorem euler_is_lipschitzInY
    (f : ℝ → E → E) {K : ℝ} {a b hmax : ℝ}
    (_hK_nonneg : 0 ≤ K)
    (hf : ∀ x ∈ Set.Icc a b, ∀ u v : E, ‖f x u - f x v‖ ≤ K * ‖u - v‖) :
    (eulerMethod f).IsLipschitzInY K a b hmax := by
  intro x hx h hh u v
  simpa [eulerMethod] using hf x hx u v

theorem euler_isConvergent
    (f : ℝ → E → E) {a b L : ℝ}
    (hL_pos : 0 < L)
    (hab : a < b) :
    IsConvergent (eulerMethod f) a b L := by
  exact one_step_convergence (eulerMethod f) hL_pos hab

end OneStepMethod
end OneStep
