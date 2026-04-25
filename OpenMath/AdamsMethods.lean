import OpenMath.MultistepMethods

/-!
# Adams Methods

Adams-Bashforth and Adams-Moulton linear multistep methods from Iserles,
*A First Course in the Numerical Analysis of Differential Equations*, Section 1.2.
-/

open Finset Real

/-! ## Definitions -/

/-- **Adams–Bashforth 2-step** method:
y_{n+2} = y_{n+1} + h·(3/2·f_{n+1} - 1/2·f_n).
Coefficients: α = [0, -1, 1], β = [-1/2, 3/2, 0]. -/
noncomputable def adamsBashforth2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/2, 3/2, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 2-step** method:
y_{n+2} = y_{n+1} + h·(5/12·f_{n+2} + 8/12·f_{n+1} - 1/12·f_n).
Coefficients: α = [0, -1, 1], β = [-1/12, 8/12, 5/12].
This is an implicit method of order 3.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton2 : LMM 2 where
  α := ![0, -1, 1]
  β := ![-1/12, 8/12, 5/12]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 3-step** method:
y_{n+3} = y_{n+2} + h·(23/12·f_{n+2} - 16/12·f_{n+1} + 5/12·f_n).
Coefficients: α = [0, 0, -1, 1], β = [5/12, -16/12, 23/12, 0].
This is an explicit method of order 3.
Reference: Iserles, Section 1.3. -/
noncomputable def adamsBashforth3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![5/12, -16/12, 23/12, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 3-step** method:
y_{n+3} = y_{n+2} + h·(9/24·f_{n+3} + 19/24·f_{n+2}
  - 5/24·f_{n+1} + 1/24·f_n).
Coefficients: α = [0, 0, -1, 1], β = [1/24, -5/24, 19/24, 9/24].
This is an implicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton3 : LMM 3 where
  α := ![0, 0, -1, 1]
  β := ![1/24, -5/24, 19/24, 9/24]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 4-step** method:
y_{n+4} = y_{n+3} + h·(55/24·f_{n+3} - 59/24·f_{n+2}
  + 37/24·f_{n+1} - 9/24·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-9/24, 37/24, -59/24, 55/24, 0].
This is an explicit method of order 4.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-9/24, 37/24, -59/24, 55/24, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 4-step** method:
y_{n+4} = y_{n+3} + h·(251/720·f_{n+4} + 646/720·f_{n+3}
  - 264/720·f_{n+2} + 106/720·f_{n+1} - 19/720·f_n).
Coefficients: α = [0, 0, 0, -1, 1], β = [-19/720, 106/720, -264/720, 646/720, 251/720].
This is an implicit method of order 5.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton4 : LMM 4 where
  α := ![0, 0, 0, -1, 1]
  β := ![-19/720, 106/720, -264/720, 646/720, 251/720]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 5-step** method:
y_{n+5} = y_{n+4} + h·(1901/720·f_{n+4} - 2774/720·f_{n+3}
  + 2616/720·f_{n+2} - 1274/720·f_{n+1} + 251/720·f_n).
Coefficients: α = [0, 0, 0, 0, -1, 1], β = [251/720, -1274/720, 2616/720, -2774/720, 1901/720, 0].
This is an explicit method of order 5.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth5 : LMM 5 where
  α := ![0, 0, 0, 0, -1, 1]
  β := ![251/720, -1274/720, 2616/720, -2774/720, 1901/720, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Bashforth 6-step** method:
y_{n+6} = y_{n+5} + h·(4277/1440·f_{n+5} - 7923/1440·f_{n+4}
  + 9982/1440·f_{n+3} - 7298/1440·f_{n+2}
  + 2877/1440·f_{n+1} - 475/1440·f_n).
Coefficients: α = [0, 0, 0, 0, 0, -1, 1],
β = [-475/1440, 2877/1440, -7298/1440, 9982/1440, -7923/1440, 4277/1440, 0].
This is an explicit method of order 6.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsBashforth6 : LMM 6 where
  α := ![0, 0, 0, 0, 0, -1, 1]
  β := ![-475/1440, 2877/1440, -7298/1440, 9982/1440, -7923/1440, 4277/1440, 0]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 5-step** method:
y_{n+5} = y_{n+4} + h·(475/1440·f_{n+5} + 1427/1440·f_{n+4}
  − 798/1440·f_{n+3} + 482/1440·f_{n+2} − 173/1440·f_{n+1} + 27/1440·f_n).
Coefficients: α = [0, 0, 0, 0, -1, 1],
β = [27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440].
This is an implicit method of order 6.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton5 : LMM 5 where
  α := ![0, 0, 0, 0, -1, 1]
  β := ![27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440]
  normalized := by simp [Fin.last]

/-- **Adams–Moulton 6-step** method:
y_{n+6} = y_{n+5} + h·(19087/60480·f_{n+6} + 65112/60480·f_{n+5}
  − 46461/60480·f_{n+4} + 37504/60480·f_{n+3}
  − 20211/60480·f_{n+2} + 6312/60480·f_{n+1} − 863/60480·f_n).
Coefficients: α = [0, 0, 0, 0, 0, -1, 1],
β = [-863/60480, 6312/60480, -20211/60480, 37504/60480, -46461/60480,
     65112/60480, 19087/60480].
This is an implicit method of order 7.
Reference: Iserles, Section 1.2. -/
noncomputable def adamsMoulton6 : LMM 6 where
  α := ![0, 0, 0, 0, 0, -1, 1]
  β := ![-863/60480, 6312/60480, -20211/60480, 37504/60480, -46461/60480,
        65112/60480, 19087/60480]
  normalized := by simp [Fin.last]

/-! ## Consistency / explicitness / implicitness -/

/-- Adams–Bashforth 2-step is consistent. -/
theorem adamsBashforth2_consistent : adamsBashforth2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsBashforth2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Bashforth 2-step is explicit (β₂ = 0). -/
theorem adamsBashforth2_explicit : adamsBashforth2.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth2, Fin.last]

/-- Adams–Moulton 2-step is consistent. -/
theorem adamsMoulton2_consistent : adamsMoulton2.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton2, Fin.sum_univ_three],
   by simp [LMM.sigma, adamsMoulton2, Fin.sum_univ_three]; norm_num⟩

/-- Adams–Moulton 2-step is implicit (β₂ = 5/12 ≠ 0). -/
theorem adamsMoulton2_implicit : adamsMoulton2.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton2, Fin.last]

/-- Adams–Bashforth 3-step is consistent. -/
theorem adamsBashforth3_consistent : adamsBashforth3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsBashforth3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Bashforth 3-step is explicit (β₃ = 0). -/
theorem adamsBashforth3_explicit : adamsBashforth3.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth3, Fin.last]

/-- Adams–Moulton 3-step is consistent. -/
theorem adamsMoulton3_consistent : adamsMoulton3.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton3, Fin.sum_univ_four],
   by simp [LMM.sigma, adamsMoulton3, Fin.sum_univ_four]; norm_num⟩

/-- Adams–Moulton 3-step is implicit (β₃ = 9/24 ≠ 0). -/
theorem adamsMoulton3_implicit : adamsMoulton3.IsImplicit := by
  simp [LMM.IsImplicit, adamsMoulton3, Fin.last]

/-- Adams–Bashforth 4-step is consistent. -/
theorem adamsBashforth4_consistent : adamsBashforth4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsBashforth4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Bashforth 4-step is explicit (β₄ = 0). -/
theorem adamsBashforth4_explicit : adamsBashforth4.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth4, Fin.last]

/-- Adams–Moulton 4-step is consistent. -/
theorem adamsMoulton4_consistent : adamsMoulton4.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton4, Fin.sum_univ_five],
   by simp [LMM.sigma, adamsMoulton4, Fin.sum_univ_five]; norm_num⟩

/-- Adams–Moulton 4-step is implicit (β₄ = 251/720 ≠ 0). -/
theorem adamsMoulton4_implicit : adamsMoulton4.β 4 ≠ 0 := by
  change (251 / 720 : ℝ) ≠ 0
  norm_num

/-- Adams–Bashforth 5-step is consistent. -/
theorem adamsBashforth5_consistent : adamsBashforth5.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth5, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth5, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 5-step is explicit (β₅ = 0). -/
theorem adamsBashforth5_explicit : adamsBashforth5.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth5, Fin.last]

/-- Adams–Bashforth 6-step is consistent. -/
theorem adamsBashforth6_consistent : adamsBashforth6.IsConsistent :=
  ⟨by simp [LMM.rho, adamsBashforth6, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsBashforth6, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Bashforth 6-step is explicit (β₆ = 0). -/
theorem adamsBashforth6_explicit : adamsBashforth6.IsExplicit := by
  simp [LMM.IsExplicit, adamsBashforth6, Fin.last]

/-- Adams–Moulton 5-step is consistent. -/
theorem adamsMoulton5_consistent : adamsMoulton5.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton5, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton5, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 5-step is implicit (β₅ = 475/1440 ≠ 0). -/
theorem adamsMoulton5_implicit : adamsMoulton5.β 5 ≠ 0 := by
  change (475 / 1440 : ℝ) ≠ 0
  norm_num

/-- Adams–Moulton 6-step is consistent. -/
theorem adamsMoulton6_consistent : adamsMoulton6.IsConsistent :=
  ⟨by simp [LMM.rho, adamsMoulton6, Fin.sum_univ_succ],
   by simp [LMM.sigma, adamsMoulton6, Fin.sum_univ_succ]; norm_num⟩

/-- Adams–Moulton 6-step is implicit (β₆ = 19087/60480 ≠ 0). -/
theorem adamsMoulton6_implicit : adamsMoulton6.β 6 ≠ 0 := by
  change (19087 / 60480 : ℝ) ≠ 0
  norm_num

/-! ## Order theorems -/

/-- Adams–Bashforth 2-step has order 2. -/
theorem adamsBashforth2_order_two : adamsBashforth2.HasOrder 2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;> simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth2, Fin.sum_univ_three]; norm_num

/-- Adams–Moulton 2-step has order 3. -/
theorem adamsMoulton2_order_three : adamsMoulton2.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton2, Fin.sum_univ_three]; norm_num

/-- Adams–Bashforth 3-step has order 3. -/
theorem adamsBashforth3_order_three : adamsBashforth3.HasOrder 3 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth3, Fin.sum_univ_four]; norm_num

/-- Adams–Moulton 3-step has order 4. -/
theorem adamsMoulton3_order_four : adamsMoulton3.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton3, Fin.sum_univ_four]; norm_num

/-- Adams–Bashforth 4-step has order 4. -/
theorem adamsBashforth4_order_four : adamsBashforth4.HasOrder 4 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth4, Fin.sum_univ_five]; norm_num

/-- Adams–Moulton 4-step has order 5. -/
theorem adamsMoulton4_order_five : adamsMoulton4.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton4, Fin.sum_univ_five]; norm_num

/-- Adams–Bashforth 5-step has order 5. -/
theorem adamsBashforth5_order_five : adamsBashforth5.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth5, Fin.sum_univ_succ]; norm_num

/-- Adams–Bashforth 6-step has order 6. -/
theorem adamsBashforth6_order_six : adamsBashforth6.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsBashforth6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsBashforth6, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 5-step has order 6. -/
theorem adamsMoulton5_order_six : adamsMoulton5.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton5, Fin.sum_univ_succ]; norm_num

/-- Adams–Moulton 6-step has order 7. -/
theorem adamsMoulton6_order_seven : adamsMoulton6.HasOrder 7 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, adamsMoulton6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, adamsMoulton6, Fin.sum_univ_succ]; norm_num

/-! ## Zero-stability theorems -/

/-- Adams–Bashforth 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1,
both in the closed unit disk, and the unit root ξ = 1 is simple (ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth2_zeroStable : adamsBashforth2.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth2, Fin.sum_univ_three]
    simp [LMM.rhoC, adamsBashforth2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 2-step is zero-stable: ρ(ξ) = ξ² - ξ has roots 0 and 1
(same as Adams–Bashforth 2-step). -/
theorem adamsMoulton2_zeroStable : adamsMoulton2.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton2, Fin.sum_univ_three]
    simp [LMM.rhoC, adamsMoulton2, Fin.sum_univ_three] at hξ
    have h : ξ * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · rw [h0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Bashforth 3-step is zero-stable: ρ(ξ) = ξ³ - ξ² = ξ²(ξ - 1) has a double
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth3_zeroStable : adamsBashforth3.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth3, Fin.sum_univ_four]
    simp [LMM.rhoC, adamsBashforth3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 3-step is zero-stable: it has the same first characteristic
polynomial as Adams–Bashforth 3-step. -/
theorem adamsMoulton3_zeroStable : adamsMoulton3.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton3, Fin.sum_univ_four]
    simp [LMM.rhoC, adamsMoulton3, Fin.sum_univ_four] at hξ
    have h : ξ ^ 2 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 2) (a := ξ) (by norm_num : (2 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Bashforth 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth4_zeroStable : adamsBashforth4.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth4, Fin.sum_univ_five]
    simp [LMM.rhoC, adamsBashforth4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 4-step is zero-stable: ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1) has a triple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsMoulton4_zeroStable : adamsMoulton4.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton4, Fin.sum_univ_five]
    simp [LMM.rhoC, adamsMoulton4, Fin.sum_univ_five] at hξ
    have h : ξ ^ 3 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 3) (a := ξ) (by norm_num : (3 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Bashforth 5-step is zero-stable: ρ(ξ) = ξ⁵ - ξ⁴ = ξ⁴(ξ - 1) has a quadruple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth5_zeroStable : adamsBashforth5.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth5, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 4 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 4) (a := ξ) (by norm_num : (4 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth5, Fin.sum_univ_succ]
    simp [LMM.rhoC, adamsBashforth5, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 4 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 4) (a := ξ) (by norm_num : (4 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Bashforth 6-step is zero-stable: ρ(ξ) = ξ⁶ - ξ⁵ = ξ⁵(ξ - 1) has a
quintuple root at 0 (interior to the unit disk) and a simple root at 1 (on the
unit circle, with ρ'(1) = 1 ≠ 0). -/
theorem adamsBashforth6_zeroStable : adamsBashforth6.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsBashforth6, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 5 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 5) (a := ξ) (by norm_num : (5 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsBashforth6, Fin.sum_univ_succ]
    simp [LMM.rhoC, adamsBashforth6, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 5 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 5) (a := ξ) (by norm_num : (5 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 5-step is zero-stable: ρ(ξ) = ξ⁵ - ξ⁴ = ξ⁴(ξ - 1) has a quadruple
root at 0 (interior to the unit disk) and a simple root at 1 (on the unit circle,
with ρ'(1) = 1 ≠ 0). Same ρ as Adams–Bashforth 5-step. -/
theorem adamsMoulton5_zeroStable : adamsMoulton5.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton5, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 4 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 4) (a := ξ) (by norm_num : (4 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton5, Fin.sum_univ_succ]
    simp [LMM.rhoC, adamsMoulton5, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 4 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 4) (a := ξ) (by norm_num : (4 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num

/-- Adams–Moulton 6-step is zero-stable: ρ(ξ) = ξ⁶ - ξ⁵ = ξ⁵(ξ - 1) has a
quintuple root at 0 (interior to the unit disk) and a simple root at 1 (on the
unit circle, with ρ'(1) = 1 ≠ 0). Same ρ as Adams–Bashforth 6-step. -/
theorem adamsMoulton6_zeroStable : adamsMoulton6.IsZeroStable where
  roots_in_disk := by
    intro ξ hξ
    simp [LMM.rhoC, adamsMoulton6, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 5 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 5) (a := ξ) (by norm_num : (5 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0]; simp
    · have : ξ = 1 := by linear_combination h1
      rw [this]; simp
  unit_roots_simple := by
    intro ξ hξ habs
    simp [LMM.rhoCDeriv, adamsMoulton6, Fin.sum_univ_succ]
    simp [LMM.rhoC, adamsMoulton6, Fin.sum_univ_succ] at hξ
    have h : ξ ^ 5 * (ξ - 1) = 0 := by linear_combination hξ
    rcases mul_eq_zero.mp h with h0 | h1
    · have hξ0 : ξ = 0 := by
        have := pow_eq_zero_iff (n := 5) (a := ξ) (by norm_num : (5 : ℕ) ≠ 0)
        exact this.mp h0
      rw [hξ0] at habs; simp at habs
    · have h1' : ξ = 1 := by linear_combination h1
      rw [h1']; norm_num
