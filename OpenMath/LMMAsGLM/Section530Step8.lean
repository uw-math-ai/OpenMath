import OpenMath.LMMAsGLM.Section530

/-!
# Butcher §530 — LMM-as-GLM order witnesses, 8-step methods

Sibling leaf to `Section530Step7.lean` (cycle 1178). Hosts the `s = 8`
order-≥ 2 (and any future `s = 8`) Nordsieck-shift witnesses.

Reference: J. C. Butcher, *Numerical Methods for Ordinary
Differential Equations*, 2nd ed., §530.
-/

open Finset Real

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 8-step

`adamsBashforth8` (`s = 8`, sixteen GLM input slots `Fin 16`, explicit
with `β_s = 0`, classical order 8) embeds as a GLM of order ≥ 2 using
the unshifted natural Nordsieck vectors. Same helper-extraction recipe
as AB7GE2 (cycle 1166), with helpers for `q''` rows k = 7..15 (nine
helpers) and inline `q''` rows k = 0..6. The `k = 8` boundary case
(first past-`h·f` row, `β_s = 0`) closes with just `simp` (no
`norm_num`), mirroring the AB7GE2 nuance from cycle 1166. -/

namespace AB8GE2

private noncomputable def qN : Fin (2 * 8) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 8 => (1 : ℝ)) (fun _ : Fin 8 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 8) k)

private noncomputable def q'N : Fin (2 * 8) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 8 => ((j : ℕ) : ℝ)) (fun _ : Fin 8 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 8) k)

private noncomputable def q''N : Fin (2 * 8) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 8 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 8 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 8) k)

private theorem q'_obligation (k : Fin 16) :
    (∑ j, adamsBashforth8.toGLM.B k j) +
        ∑ l, adamsBashforth8.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 7` case (last past-`y` row) for `q''_obligation`. -/
private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨7, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨7, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 8` case (first past-`h·f` row, `β_s = 0`). Closes with
just `simp` — adding `norm_num` triggers "no goals to be solved". -/
private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨8, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨8, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨9, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨9, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨10, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨10, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨11, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨11, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨12, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨12, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨13, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨13, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨14, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨14, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsBashforth8.toGLM.B (⟨15, by decide⟩ : Fin 16) j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨15, by decide⟩ : Fin 16) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 16) :
    2 * (∑ j, adamsBashforth8.toGLM.B k j *
          ((∑ i, adamsBashforth8.toGLM.A j i) +
            ∑ l, adamsBashforth8.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth8.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven
  · exact q''_obligation_twelve
  · exact q''_obligation_thirteen
  · exact q''_obligation_fourteen
  · exact q''_obligation_fifteen

end AB8GE2

theorem adamsBashforth8_toGLM_hasOrderGe2 :
    adamsBashforth8.toGLM.HasOrderGe2 := by
  refine ⟨AB8GE2.qN, AB8GE2.q'N, AB8GE2.q''N,
    ?_, ?_, AB8GE2.q'_obligation, AB8GE2.q''_obligation⟩
  · exact adamsBashforth8.toGLM_V_nordsieckQ_eq adamsBashforth8_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth8, Fin.addCases,
      Fin.sum_univ_succ, AB8GE2.qN]

theorem adamsBashforth8_toGLM_hasOrderGe1 :
    adamsBashforth8.toGLM.HasOrderGe1 :=
  adamsBashforth8_toGLM_hasOrderGe2.toHasOrderGe1
