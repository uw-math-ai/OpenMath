import OpenMath.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Real

/-!
# One-sided Lipschitz conditions and stiffness bounds

This file formalizes Iserles, Definition 1.12A and Theorem 1.12B.
-/

section OneSidedLipschitz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `f` satisfies a one-sided Lipschitz condition with constant `l` on `[a, b]` if
`⟪f x u - f x v, u - v⟫ ≤ l * ‖u - v‖^2` for all `x ∈ [a, b]`. Reference: Iserles,
Definition 1.12A. -/
def IsOneSidedLipschitz (f : ℝ → H → H) (l : ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ u v : H,
    @inner ℝ H _ (f x u - f x v) (u - v) ≤ l * ‖u - v‖ ^ 2

/-- A Lipschitz map is one-sided Lipschitz with the same constant. -/
theorem lipschitzWith_implies_oneSidedLipschitz
    {f : ℝ → H → H} {K : NNReal} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, LipschitzWith K (f x)) :
    IsOneSidedLipschitz f K a b := by
  intro x hx u v
  have hLip : ‖f x u - f x v‖ ≤ (K : ℝ) * ‖u - v‖ := by
    simpa [dist_eq_norm] using (hf x hx).dist_le_mul u v
  calc
    @inner ℝ H _ (f x u - f x v) (u - v)
      ≤ ‖f x u - f x v‖ * ‖u - v‖ := real_inner_le_norm _ _
    _ ≤ ((K : ℝ) * ‖u - v‖) * ‖u - v‖ := by
      gcongr
    _ = (K : ℝ) * ‖u - v‖ ^ 2 := by ring

section SolutionBound

variable {f : ℝ → H → H} {l x0 x1 : ℝ} {y z : ℝ → H}

private noncomputable def diffFun (y z : ℝ → H) : ℝ → H := fun x => y x - z x

private noncomputable def sqDist (y z : ℝ → H) : ℝ → ℝ :=
  fun x => ‖diffFun y z x‖ ^ 2

private noncomputable def weightedSqDist (l x0 : ℝ) (y z : ℝ → H) : ℝ → ℝ :=
  fun x => Real.exp (-2 * l * (x - x0)) * sqDist y z x

private theorem hasDerivAt_sqDist
    (hy : ∀ x ∈ Icc x0 x1, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x ∈ Icc x0 x1, HasDerivAt z (f x (z x)) x)
    {x : ℝ} (hx : x ∈ Icc x0 x1) :
    HasDerivAt (sqDist y z)
      (2 * @inner ℝ H _ (f x (y x) - f x (z x)) (y x - z x)) x := by
  have hdiff :
      HasDerivAt (diffFun y z) (f x (y x) - f x (z x)) x :=
    (hy x hx).sub (hz x hx)
  have hinner :
      HasDerivAt (fun t => @inner ℝ H _ (diffFun y z t) (diffFun y z t))
        (@inner ℝ H _ (diffFun y z x) (f x (y x) - f x (z x)) +
          @inner ℝ H _ (f x (y x) - f x (z x)) (diffFun y z x)) x :=
    hdiff.inner ℝ hdiff
  simpa [sqDist, diffFun, real_inner_self_eq_norm_sq, two_mul, real_inner_comm, add_comm,
    add_left_comm, add_assoc] using hinner

private theorem hasDerivAt_weightedSqDist
    (hy : ∀ x ∈ Icc x0 x1, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x ∈ Icc x0 x1, HasDerivAt z (f x (z x)) x)
    {x : ℝ} (hx : x ∈ Ioo x0 x1) :
    HasDerivAt (weightedSqDist l x0 y z)
      (Real.exp (-2 * l * (x - x0)) *
        (2 * @inner ℝ H _ (f x (y x) - f x (z x)) (y x - z x) - 2 * l * ‖y x - z x‖ ^ 2)) x := by
  have hExp :
      HasDerivAt (fun t => Real.exp (-2 * l * (t - x0)))
        ((-2 * l) * Real.exp (-2 * l * (x - x0))) x := by
    convert ((((hasDerivAt_id x).sub_const x0).const_mul (-2 * l)).exp) using 1
    · simp only [id_eq]
      ring_nf
  have hSq : HasDerivAt (sqDist y z)
      (2 * @inner ℝ H _ (f x (y x) - f x (z x)) (y x - z x)) x :=
    hasDerivAt_sqDist hy hz (Ioo_subset_Icc_self hx)
  have hMul := hExp.mul hSq
  change HasDerivAt (fun t => Real.exp (-2 * l * (t - x0)) * sqDist y z t)
    (Real.exp (-2 * l * (x - x0)) *
      (2 * @inner ℝ H _ (f x (y x) - f x (z x)) (y x - z x) - 2 * l * ‖y x - z x‖ ^ 2)) x
  convert hMul using 1
  simp [sqDist, diffFun]
  ring_nf

/-- If `f` satisfies a one-sided Lipschitz condition with constant `l`, then any two solutions of
`y' = f(x, y)` satisfy the exponential difference bound from Iserles, Theorem 1.12B. -/
theorem oneSidedLipschitz_solution_bound
    (hOSL : IsOneSidedLipschitz f l x0 x1)
    (hy : ∀ x ∈ Icc x0 x1, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x ∈ Icc x0 x1, HasDerivAt z (f x (z x)) x) :
    ∀ x ∈ Icc x0 x1,
      ‖y x - z x‖ ≤ Real.exp (l * (x - x0)) * ‖y x0 - z x0‖ := by
  intro x hx
  have hy_cont : ContinuousOn y (Icc x0 x1) := HasDerivAt.continuousOn hy
  have hz_cont : ContinuousOn z (Icc x0 x1) := HasDerivAt.continuousOn hz
  have hsq_cont : ContinuousOn (sqDist y z) (Icc x0 x1) := by
    simpa [sqDist, diffFun] using ((continuous_norm.comp_continuousOn (hy_cont.sub hz_cont)).pow 2)
  have hweight_cont : ContinuousOn (weightedSqDist l x0 y z) (Icc x0 x1) := by
    have hExp : Continuous fun t : ℝ => Real.exp (-2 * l * (t - x0)) := by
      fun_prop
    change ContinuousOn (fun t => Real.exp (-2 * l * (t - x0)) * sqDist y z t) (Icc x0 x1)
    exact hExp.continuousOn.mul hsq_cont
  have hDeriv :
      ∀ t ∈ interior (Icc x0 x1),
        HasDerivWithinAt (weightedSqDist l x0 y z)
          (Real.exp (-2 * l * (t - x0)) *
            (2 * @inner ℝ H _ (f t (y t) - f t (z t)) (y t - z t) - 2 * l * ‖y t - z t‖ ^ 2))
          (interior (Icc x0 x1)) t := by
    intro t ht
    have ht' : t ∈ Ioo x0 x1 := by simpa [interior_Icc] using ht
    exact (hasDerivAt_weightedSqDist hy hz ht').hasDerivWithinAt
  have hNonpos :
      ∀ t ∈ interior (Icc x0 x1),
        Real.exp (-2 * l * (t - x0)) *
            (2 * @inner ℝ H _ (f t (y t) - f t (z t)) (y t - z t) - 2 * l * ‖y t - z t‖ ^ 2)
          ≤ 0 := by
    intro t ht
    have ht' : t ∈ Ioo x0 x1 := by simpa [interior_Icc] using ht
    have hOSL' := hOSL t (Ioo_subset_Icc_self ht') (y t) (z t)
    have hBracket : 2 * @inner ℝ H _ (f t (y t) - f t (z t)) (y t - z t) -
        2 * l * ‖y t - z t‖ ^ 2 ≤ 0 := by
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hBracket
  have hAnti : AntitoneOn (weightedSqDist l x0 y z) (Icc x0 x1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x0 x1) hweight_cont hDeriv hNonpos
  have hx0_mem : x0 ∈ Icc x0 x1 := ⟨le_rfl, hx.1.trans hx.2⟩
  have hWeighted :
      weightedSqDist l x0 y z x ≤ weightedSqDist l x0 y z x0 :=
    hAnti hx0_mem hx hx.1
  have hBase' :
      Real.exp (-2 * l * (x - x0)) * ‖y x - z x‖ ^ 2 ≤
        Real.exp (-2 * l * (x0 - x0)) * ‖y x0 - z x0‖ ^ 2 := by
    simpa [weightedSqDist, sqDist] using hWeighted
  have hBase :
      Real.exp (-2 * l * (x - x0)) * ‖y x - z x‖ ^ 2 ≤ ‖y x0 - z x0‖ ^ 2 := by
    have hWeighted' := hWeighted
    change Real.exp (-2 * l * (x - x0)) * ‖y x - z x‖ ^ 2 ≤
      Real.exp (-2 * l * (x0 - x0)) * ‖y x0 - z x0‖ ^ 2 at hWeighted'
    simpa using hWeighted'
  have hExpCancel :
      Real.exp (2 * l * (x - x0)) * Real.exp (-2 * l * (x - x0)) = 1 := by
    rw [← Real.exp_add]
    have : 2 * l * (x - x0) + -2 * l * (x - x0) = 0 := by ring
    rw [this, Real.exp_zero]
  have hSq :
      ‖y x - z x‖ ^ 2 ≤ Real.exp (2 * l * (x - x0)) * ‖y x0 - z x0‖ ^ 2 := by
    calc
      ‖y x - z x‖ ^ 2
        = Real.exp (2 * l * (x - x0)) *
            (Real.exp (-2 * l * (x - x0)) * ‖y x - z x‖ ^ 2) := by
              rw [← mul_assoc, hExpCancel, one_mul]
      _ ≤ Real.exp (2 * l * (x - x0)) * ‖y x0 - z x0‖ ^ 2 := by
            gcongr
  have hSq' :
      ‖y x - z x‖ ^ 2 ≤ (Real.exp (l * (x - x0)) * ‖y x0 - z x0‖) ^ 2 := by
    have hExpSq : Real.exp (2 * l * (x - x0)) = (Real.exp (l * (x - x0))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      ‖y x - z x‖ ^ 2 ≤ Real.exp (2 * l * (x - x0)) * ‖y x0 - z x0‖ ^ 2 := hSq
      _ = (Real.exp (l * (x - x0))) ^ 2 * ‖y x0 - z x0‖ ^ 2 := by rw [hExpSq]
      _ = (Real.exp (l * (x - x0)) * ‖y x0 - z x0‖) ^ 2 := by ring
  exact le_of_sq_le_sq hSq' (by positivity)

/-- If the one-sided Lipschitz constant is nonpositive, solution differences do not grow. -/
theorem oneSidedLipschitz_nonpos_implies_contractive
    (hOSL : IsOneSidedLipschitz f l x0 x1)
    (hl : l ≤ 0)
    (hy : ∀ x ∈ Icc x0 x1, HasDerivAt y (f x (y x)) x)
    (hz : ∀ x ∈ Icc x0 x1, HasDerivAt z (f x (z x)) x) :
    ∀ x ∈ Icc x0 x1, ‖y x - z x‖ ≤ ‖y x0 - z x0‖ := by
  intro x hx
  have hMain := oneSidedLipschitz_solution_bound hOSL hy hz x hx
  have hExpLeOne : Real.exp (l * (x - x0)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg hl (sub_nonneg.mpr hx.1)
  calc
    ‖y x - z x‖ ≤ Real.exp (l * (x - x0)) * ‖y x0 - z x0‖ := hMain
    _ ≤ ‖y x0 - z x0‖ := by
      simpa [one_mul, mul_comm] using
        mul_le_of_le_one_right (norm_nonneg (y x0 - z x0)) hExpLeOne

end SolutionBound
end OneSidedLipschitz
