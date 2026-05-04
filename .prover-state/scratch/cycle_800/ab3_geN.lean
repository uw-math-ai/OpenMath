import OpenMath.LMMAsGLM

open scoped Classical

namespace AB3GE3

private noncomputable def qN : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 9)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 27 * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 9))
    (Fin.cast (Nat.two_mul 3) k)

-- Helper for the q''' (third-derivative) obligation, factored out so that
-- each `Fin 6` case gets its own heartbeat budget.
private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, adamsBashforth3.toGLM.B k j *
            ((∑ i, adamsBashforth3.toGLM.A j i *
                ((∑ i', adamsBashforth3.toGLM.A i i') +
                  ∑ l, adamsBashforth3.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth3.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end AB3GE3

theorem adamsBashforth3_toGLM_hasOrderGe3 :
    adamsBashforth3.toGLM.HasOrderGe3 := by
  refine ⟨AB3GE3.qN, AB3GE3.q'N, AB3GE3.q''N, AB3GE3.q'''N,
    ?_, ?_, ?_, ?_, AB3GE3.q'''_obligation⟩
  · exact adamsBashforth3.toGLM_V_nordsieckQ_eq adamsBashforth3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ, AB3GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      AB3GE3.qN, AB3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      AB3GE3.qN, AB3GE3.q'N, AB3GE3.q''N]
    all_goals norm_num
