import OpenMath.LMMAsGLM.Section530

/-!
# Butcher §530 — LMM-as-GLM order witnesses, 7-step methods

Carved out of `OpenMath/LMMAsGLM/Section530.lean` (cycle 1168) to
keep both files under the 3000-line hard cap. Hosts the s = 7
order-≥ 3 (and any future s = 7) Nordsieck-shift witnesses.

Reference: J. C. Butcher, *Numerical Methods for Ordinary
Differential Equations*, 2nd ed., §530.
-/

open Finset Real

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 7-step

`adamsMoulton7` (`s = 7`, fourteen GLM input slots `Fin 14`, **implicit**
with `β_s = 36799/120960 ≠ 0`, classical order 7) embeds as a GLM of
order ≥ 2 using the unshifted natural Nordsieck vectors
`qN k = if k < s then 1 else 0`,
`q'N k = if k < s then j else 1`, and
`q''N k = if k < s then j² else 2 * j`. Same helper-extraction recipe
as AM6GE2 (cycle 1164) with helpers for `q''` rows k = 6..13 (eight
helpers) and inline `q''` rows k = 0..5. At order 2 the implicit
`β_s ≠ 0` does not require any Nordsieck shift `C`. -/

namespace AM7GE2

private noncomputable def qN : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 7 => (1 : ℝ)) (fun _ : Fin 7 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q'N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ)) (fun _ : Fin 7 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q''N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 7 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private theorem q'_obligation (k : Fin 14) :
    (∑ j, adamsMoulton7.toGLM.B k j) +
        ∑ l, adamsMoulton7.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 6` case (last past-`y` row) for `q''_obligation` —
factored as a private theorem so it gets a fresh heartbeat budget. -/
private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨6, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨6, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 7` case (first past-`h·f` row) — closes with `simp`
alone; appending `norm_num` triggers "no goals to be solved", matching
the AM6GE2 / AB7GE2 pattern. -/
private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨7, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨7, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨8, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨8, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨9, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨9, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨10, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨10, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨11, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨11, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨12, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨12, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨13, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨13, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 14) :
    2 * (∑ j, adamsMoulton7.toGLM.B k j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven
  · exact q''_obligation_twelve
  · exact q''_obligation_thirteen

end AM7GE2

theorem adamsMoulton7_toGLM_hasOrderGe2 :
    adamsMoulton7.toGLM.HasOrderGe2 := by
  refine ⟨AM7GE2.qN, AM7GE2.q'N, AM7GE2.q''N,
    ?_, ?_, AM7GE2.q'_obligation, AM7GE2.q''_obligation⟩
  · exact adamsMoulton7.toGLM_V_nordsieckQ_eq adamsMoulton7_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      AM7GE2.qN]

theorem adamsMoulton7_toGLM_hasOrderGe1 :
    adamsMoulton7.toGLM.HasOrderGe1 :=
  adamsMoulton7_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 7-step

`adamsBashforth7` (`s = 7`, fourteen GLM input slots `Fin 14`,
explicit with `β_s = 0`, classical order 7) embeds as a GLM of order
≥ 3 with the Nordsieck shift `C := s² − 2·β_s·s = 49`. Same
helper-extraction recipe as AB6GE3 (cycle 1162), with helpers for
`q''` rows k = 6..13 and `q'''` rows k = 4..13. The `k = 7` boundary
case (first past-`h·f` row) closes with just `simp` (no `norm_num`),
mirroring the AB7GE2 nuance from cycle 1166. -/

namespace AB7GE3

private noncomputable def qN : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 7 => (1 : ℝ)) (fun _ : Fin 7 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q'N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ)) (fun _ : Fin 7 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q''N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ) ^ 2 - 49)
    (fun j : Fin 7 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q'''N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ) ^ 3 - 3 * 49 * ((j : ℕ) : ℝ))
    (fun j : Fin 7 => 3 * (((j : ℕ) : ℝ) ^ 2 - 49))
    (Fin.cast (Nat.two_mul 7) k)

private theorem q'_obligation (k : Fin 14) :
    (∑ j, adamsBashforth7.toGLM.B k j) +
        ∑ l, adamsBashforth7.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨6, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨6, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 7` case (first past-`h·f` row, `β_s = 0`). Closes with
just `simp` — adding `norm_num` triggers "no goals to be solved". -/
private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨7, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨7, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨8, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨8, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨9, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨9, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨10, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨10, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨11, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨11, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨12, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨12, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsBashforth7.toGLM.B (⟨13, by decide⟩ : Fin 14) j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨13, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 14) :
    2 * (∑ j, adamsBashforth7.toGLM.B k j *
          ((∑ i, adamsBashforth7.toGLM.A j i) +
            ∑ l, adamsBashforth7.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth7.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven
  · exact q''_obligation_twelve
  · exact q''_obligation_thirteen

private theorem q'''_obligation_four :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨4, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨4, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨5, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨5, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨6, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨6, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Boundary `k = 7` case (first past-`h·f` row, `β_s = 0`). Unlike the
analogous `q''` boundary row, the `C = 49` shift pulls a residual numeric
goal `3 * (1 - 49) = 3 + -(3 * 49)`, so `norm_num` is required here. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨7, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨7, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨8, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨8, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨9, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨9, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨10, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨10, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨11, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨11, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_twelve :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨12, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨12, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨12, by decide⟩ + 3 * q'N ⟨12, by decide⟩ +
        3 * q''N ⟨12, by decide⟩ + q'''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_thirteen :
    6 * (∑ j, adamsBashforth7.toGLM.B (⟨13, by decide⟩ : Fin 14) j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V (⟨13, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨13, by decide⟩ + 3 * q'N ⟨13, by decide⟩ +
        3 * q''N ⟨13, by decide⟩ + q'''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 14) :
    6 * (∑ j, adamsBashforth7.toGLM.B k j *
            ((∑ i, adamsBashforth7.toGLM.A j i *
                ((∑ i', adamsBashforth7.toGLM.A i i') +
                  ∑ l, adamsBashforth7.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth7.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth7.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
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

end AB7GE3

theorem adamsBashforth7_toGLM_hasOrderGe3 :
    adamsBashforth7.toGLM.HasOrderGe3 := by
  refine ⟨AB7GE3.qN, AB7GE3.q'N, AB7GE3.q''N, AB7GE3.q'''N,
    ?_, ?_, AB7GE3.q'_obligation, AB7GE3.q''_obligation,
    AB7GE3.q'''_obligation⟩
  · exact adamsBashforth7.toGLM_V_nordsieckQ_eq adamsBashforth7_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth7, Fin.addCases,
      Fin.sum_univ_succ, AB7GE3.qN]

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 7-step

`adamsMoulton7` (`s = 7`, fourteen GLM input slots `Fin 14`,
**implicit** with `β_s = 36799/120960 ≠ 0`, classical order 7) embeds
as a GLM of order ≥ 3 using the Pascal-style Nordsieck shift
`C = s² − 2 β_s s = 49 − 14·(36799/120960) = 386561/8640`. Same
helper-extraction recipe as AB7GE3 (cycle 1168), with helpers for
`q''` rows k = 6..13 and `q'''` rows k = 4..13. The `k = 7` boundary
case for `q''` closes with just `simp` (no `norm_num`), mirroring the
AM7GE2 nuance from cycle 1170; for `q'''`, the non-zero `C` shift
requires `simp [...]; norm_num` (analogous to AB7GE3 cycle 1168). -/

namespace AM7GE3

private noncomputable def qN : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 7 => (1 : ℝ)) (fun _ : Fin 7 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q'N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ)) (fun _ : Fin 7 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q''N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 => ((j : ℕ) : ℝ) ^ 2 - 386561/8640)
    (fun j : Fin 7 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 7) k)

private noncomputable def q'''N : Fin (2 * 7) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 7 =>
      ((j : ℕ) : ℝ) ^ 3 - 3 * (386561/8640) * ((j : ℕ) : ℝ))
    (fun j : Fin 7 => 3 * (((j : ℕ) : ℝ) ^ 2 - 386561/8640))
    (Fin.cast (Nat.two_mul 7) k)

private theorem q'_obligation (k : Fin 14) :
    (∑ j, adamsMoulton7.toGLM.B k j) +
        ∑ l, adamsMoulton7.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨6, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨6, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 7` case (first past-`h·f` row). Past-`h·f` slot at
order 2 is unshifted (`2 j`), so this closes with just `simp` —
matching the AM7GE2 nuance from cycle 1170. -/
private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨7, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨7, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨8, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨8, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨9, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨9, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨10, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨10, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨11, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨11, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨12, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨12, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsMoulton7.toGLM.B (⟨13, by decide⟩ : Fin 14) j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨13, by decide⟩ : Fin 14) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 14) :
    2 * (∑ j, adamsMoulton7.toGLM.B k j *
          ((∑ i, adamsMoulton7.toGLM.A j i) +
            ∑ l, adamsMoulton7.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton7.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven
  · exact q''_obligation_twelve
  · exact q''_obligation_thirteen

private theorem q'''_obligation_four :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨4, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨4, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨5, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨5, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨6, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨6, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Boundary `k = 7` case (first past-`h·f` row). Non-zero shift
`C = 386561/8640` leaves a numeric residue that `simp` cannot close,
so `norm_num` is required (analogous to AB7GE3 cycle 1168). -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨7, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨7, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨8, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨8, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨9, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨9, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨10, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨10, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨11, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨11, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_twelve :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨12, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨12, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨12, by decide⟩ + 3 * q'N ⟨12, by decide⟩ +
        3 * q''N ⟨12, by decide⟩ + q'''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_thirteen :
    6 * (∑ j, adamsMoulton7.toGLM.B (⟨13, by decide⟩ : Fin 14) j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V (⟨13, by decide⟩ : Fin 14) l * q'''N l =
      qN ⟨13, by decide⟩ + 3 * q'N ⟨13, by decide⟩ +
        3 * q''N ⟨13, by decide⟩ + q'''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 14) :
    6 * (∑ j, adamsMoulton7.toGLM.B k j *
            ((∑ i, adamsMoulton7.toGLM.A j i *
                ((∑ i', adamsMoulton7.toGLM.A i i') +
                  ∑ l, adamsMoulton7.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton7.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton7.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton7, Fin.addCases, Fin.sum_univ_succ,
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

end AM7GE3

theorem adamsMoulton7_toGLM_hasOrderGe3 :
    adamsMoulton7.toGLM.HasOrderGe3 := by
  refine ⟨AM7GE3.qN, AM7GE3.q'N, AM7GE3.q''N, AM7GE3.q'''N,
    ?_, ?_, AM7GE3.q'_obligation, AM7GE3.q''_obligation,
    AM7GE3.q'''_obligation⟩
  · exact adamsMoulton7.toGLM_V_nordsieckQ_eq adamsMoulton7_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton7, Fin.addCases,
      Fin.sum_univ_succ, AM7GE3.qN]
