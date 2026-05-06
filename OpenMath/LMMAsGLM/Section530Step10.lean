import OpenMath.LMMAsGLM.Section530

/-!
# Butcher §530 — LMM-as-GLM order witnesses, 10-step methods

Sibling leaf to `Section530Step9.lean` (cycles 1184–1190). Hosts the
`s = 10` order-≥ 2 (and any future `s = 10`) Nordsieck-shift witnesses.

Reference: J. C. Butcher, *Numerical Methods for Ordinary
Differential Equations*, 2nd ed., §530.
-/

open Finset Real

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 10-step

`adamsBashforth10` (`s = 10`, twenty GLM input slots `Fin 20`, explicit
with `β_s = 0`, classical order 10) embeds as a GLM of order ≥ 2 using
the unshifted natural Nordsieck vectors. Same helper-extraction recipe
as AB9GE2 (cycle 1184), with helpers for `q''` rows k = 0..19 and the
`q'_obligation` kept inline. The `k = 10` boundary case (first
past-`h·f` row, `β_s = 0`) closes with just `simp` (no `norm_num`),
mirroring the AB9GE2 nuance from cycle 1184. -/

namespace AB10GE2

private noncomputable def qN : Fin (2 * 10) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 10 => (1 : ℝ)) (fun _ : Fin 10 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 10) k)

private noncomputable def q'N : Fin (2 * 10) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 10 => ((j : ℕ) : ℝ)) (fun _ : Fin 10 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 10) k)

private noncomputable def q''N : Fin (2 * 10) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 10 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 10 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 10) k)

private theorem q'_obligation (k : Fin 20) :
    (∑ j, adamsBashforth10.toGLM.B k j) +
        ∑ l, adamsBashforth10.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_zero :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨0, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨0, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨0, by decide⟩ + 2 * q'N ⟨0, by decide⟩ + q''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_one :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨1, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨1, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨1, by decide⟩ + 2 * q'N ⟨1, by decide⟩ + q''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_two :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨2, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨2, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨2, by decide⟩ + 2 * q'N ⟨2, by decide⟩ + q''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_three :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨3, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨3, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨3, by decide⟩ + 2 * q'N ⟨3, by decide⟩ + q''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_four :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨4, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨4, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨4, by decide⟩ + 2 * q'N ⟨4, by decide⟩ + q''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨5, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨5, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨6, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨6, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨7, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨7, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨8, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨8, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Heavy `k = 9` case (last past-`y` row) for `q''_obligation`. -/
private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨9, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨9, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 10` case (first past-`h·f` row, `β_s = 0`). Closes with
just `simp` — adding `norm_num` triggers "no goals to be solved". -/
private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨10, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨10, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨11, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨11, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨12, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨12, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨13, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨13, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨14, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨14, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨15, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨15, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_sixteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨16, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨16, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨16, by decide⟩ + 2 * q'N ⟨16, by decide⟩ + q''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seventeen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨17, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨17, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨17, by decide⟩ + 2 * q'N ⟨17, by decide⟩ + q''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eighteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨18, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨18, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨18, by decide⟩ + 2 * q'N ⟨18, by decide⟩ + q''N ⟨18, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nineteen :
    2 * (∑ j, adamsBashforth10.toGLM.B (⟨19, by decide⟩ : Fin 20) j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V (⟨19, by decide⟩ : Fin 20) l * q''N l =
      qN ⟨19, by decide⟩ + 2 * q'N ⟨19, by decide⟩ + q''N ⟨19, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth10, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 20) :
    2 * (∑ j, adamsBashforth10.toGLM.B k j *
          ((∑ i, adamsBashforth10.toGLM.A j i) +
            ∑ l, adamsBashforth10.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth10.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · exact q''_obligation_zero
  · exact q''_obligation_one
  · exact q''_obligation_two
  · exact q''_obligation_three
  · exact q''_obligation_four
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven
  · exact q''_obligation_twelve
  · exact q''_obligation_thirteen
  · exact q''_obligation_fourteen
  · exact q''_obligation_fifteen
  · exact q''_obligation_sixteen
  · exact q''_obligation_seventeen
  · exact q''_obligation_eighteen
  · exact q''_obligation_nineteen

end AB10GE2

theorem adamsBashforth10_toGLM_hasOrderGe2 :
    adamsBashforth10.toGLM.HasOrderGe2 := by
  refine ⟨AB10GE2.qN, AB10GE2.q'N, AB10GE2.q''N,
    ?_, ?_, AB10GE2.q'_obligation, AB10GE2.q''_obligation⟩
  · exact adamsBashforth10.toGLM_V_nordsieckQ_eq adamsBashforth10_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth10, Fin.addCases,
      Fin.sum_univ_succ, AB10GE2.qN]

theorem adamsBashforth10_toGLM_hasOrderGe1 :
    adamsBashforth10.toGLM.HasOrderGe1 :=
  adamsBashforth10_toGLM_hasOrderGe2.toHasOrderGe1
