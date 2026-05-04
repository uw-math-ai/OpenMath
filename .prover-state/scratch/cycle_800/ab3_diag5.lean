import OpenMath.LMMAsGLM

open scoped Classical

set_option maxHeartbeats 1000000

theorem adamsBashforth3_toGLM_hasOrderGe3 :
    adamsBashforth3.toGLM.HasOrderGe3 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 9)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 27 * ((j : ℕ) : ℝ))
      (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 9))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth3.toGLM_V_nordsieckQ_eq adamsBashforth3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    · -- case 0
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
    · -- case 1
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
    · -- case 2 (closure row)
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
    · -- case 3
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
    · -- case 4
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
    · -- case 5
      simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
      sorry
