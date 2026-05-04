import OpenMath.LMMAsGLM

open scoped Classical

set_option maxHeartbeats 400000

example : True := by
  have hgoal : ∀ (q q' q'' q''' : Fin 6 → ℝ),
      ∀ (k : Fin 6),
      6 * (∑ j, adamsBashforth3.toGLM.B k j *
            ((∑ i', adamsBashforth3.toGLM.A j i') +
              ∑ l, adamsBashforth3.toGLM.U j l * q' l +
              0)) +
        ∑ l, adamsBashforth3.toGLM.V k l * q''' l =
      q k + 3 * q' k + 3 * q'' k + q''' k := by
    sorry
  trivial
