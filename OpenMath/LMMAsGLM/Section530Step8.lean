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

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 8-step

`adamsBashforth8` (`s = 8`, sixteen GLM input slots `Fin 16`, explicit
with `β_s = 0`, classical order 8) embeds as a GLM of order ≥ 3 using
the `C = s² − 2 β_s · s = 64` Nordsieck shift (since `β_s = 0`,
`C = s² = 64`). Mirrors AB7GE3 (cycle 1168) with the substitution
`s = 7 → 8`. Helper-extraction recipe: nine `q''` helpers for k = 7..15
(boundary k = 8 closes with `simp` alone, others `simp + norm_num`), and
twelve `q'''` helpers for k = 4..15 (all `simp + norm_num`, including
the k = 8 boundary since `C = 64 ≠ 0`). -/

namespace AB8GE3

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
    (fun j : Fin 8 => ((j : ℕ) : ℝ) ^ 2 - 64)
    (fun j : Fin 8 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 8) k)

private noncomputable def q'''N : Fin (2 * 8) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 8 => ((j : ℕ) : ℝ) ^ 3 - 3 * 64 * ((j : ℕ) : ℝ))
    (fun j : Fin 8 => 3 * (((j : ℕ) : ℝ) ^ 2 - 64))
    (Fin.cast (Nat.two_mul 8) k)

private theorem q'_obligation (k : Fin 16) :
    (∑ j, adamsBashforth8.toGLM.B k j) +
        ∑ l, adamsBashforth8.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

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

private theorem q'''_obligation_four :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨4, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨4, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨5, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨5, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨6, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨6, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨7, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨7, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Boundary `k = 8` case (first past-`h·f` row, `β_s = 0`). Unlike the
analogous `q''` boundary row, the `C = 64` shift pulls a residual numeric
goal, so `norm_num` is required here. -/
private theorem q'''_obligation_eight :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨8, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨8, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨9, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨9, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨10, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨10, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨11, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨11, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_twelve :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨12, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨12, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨12, by decide⟩ + 3 * q'N ⟨12, by decide⟩ +
        3 * q''N ⟨12, by decide⟩ + q'''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_thirteen :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨13, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨13, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨13, by decide⟩ + 3 * q'N ⟨13, by decide⟩ +
        3 * q''N ⟨13, by decide⟩ + q'''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fourteen :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨14, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨14, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨14, by decide⟩ + 3 * q'N ⟨14, by decide⟩ +
        3 * q''N ⟨14, by decide⟩ + q'''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fifteen :
    6 * (∑ j, adamsBashforth8.toGLM.B (⟨15, by decide⟩ : Fin 16) j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V (⟨15, by decide⟩ : Fin 16) l * q'''N l =
      qN ⟨15, by decide⟩ + 3 * q'N ⟨15, by decide⟩ +
        3 * q''N ⟨15, by decide⟩ + q'''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 16) :
    6 * (∑ j, adamsBashforth8.toGLM.B k j *
            ((∑ i, adamsBashforth8.toGLM.A j i *
                ((∑ i', adamsBashforth8.toGLM.A i i') +
                  ∑ l, adamsBashforth8.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth8.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth8.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth8, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · exact q'''_obligation_five
  · exact q'''_obligation_six
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine
  · exact q'''_obligation_ten
  · exact q'''_obligation_eleven
  · exact q'''_obligation_twelve
  · exact q'''_obligation_thirteen
  · exact q'''_obligation_fourteen
  · exact q'''_obligation_fifteen

end AB8GE3

theorem adamsBashforth8_toGLM_hasOrderGe3 :
    adamsBashforth8.toGLM.HasOrderGe3 := by
  refine ⟨AB8GE3.qN, AB8GE3.q'N, AB8GE3.q''N, AB8GE3.q'''N,
    ?_, ?_, AB8GE3.q'_obligation, AB8GE3.q''_obligation,
    AB8GE3.q'''_obligation⟩
  · exact adamsBashforth8.toGLM_V_nordsieckQ_eq adamsBashforth8_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth8, Fin.addCases,
      Fin.sum_univ_succ, AB8GE3.qN]
