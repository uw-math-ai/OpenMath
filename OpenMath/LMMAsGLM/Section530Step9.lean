import OpenMath.LMMAsGLM.Section530

/-!
# Butcher §530 — LMM-as-GLM order witnesses, 9-step methods

Sibling leaf to `Section530Step8.lean` (cycle 1178/1180/1182). Hosts the
`s = 9` order-≥ 2 (and any future `s = 9`) Nordsieck-shift witnesses.

Reference: J. C. Butcher, *Numerical Methods for Ordinary
Differential Equations*, 2nd ed., §530.
-/

open Finset Real

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 9-step

`adamsBashforth9` (`s = 9`, eighteen GLM input slots `Fin 18`, explicit
with `β_s = 0`, classical order 9) embeds as a GLM of order ≥ 2 using
the unshifted natural Nordsieck vectors. Same helper-extraction recipe
as AB8GE2 (cycle 1178), with helpers for `q''` rows k = 9..17 (nine
helpers) and inline `q''` rows k = 0..8. The `k = 9` boundary case
(first past-`h·f` row, `β_s = 0`) closes with just `simp` (no
`norm_num`), mirroring the AB8GE2 nuance from cycle 1178. -/

namespace AB9GE2

private noncomputable def qN : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 9 => (1 : ℝ)) (fun _ : Fin 9 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ)) (fun _ : Fin 9 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 9 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private theorem q'_obligation (k : Fin 18) :
    (∑ j, adamsBashforth9.toGLM.B k j) +
        ∑ l, adamsBashforth9.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_zero :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨0, by decide⟩ + 2 * q'N ⟨0, by decide⟩ + q''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_one :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨1, by decide⟩ + 2 * q'N ⟨1, by decide⟩ + q''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_two :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨2, by decide⟩ + 2 * q'N ⟨2, by decide⟩ + q''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_three :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨3, by decide⟩ + 2 * q'N ⟨3, by decide⟩ + q''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_four :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨4, by decide⟩ + 2 * q'N ⟨4, by decide⟩ + q''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Heavy `k = 8` case (last past-`y` row) for `q''_obligation`. -/
private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row, `β_s = 0`). Closes with
just `simp` — adding `norm_num` triggers "no goals to be solved". -/
private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_sixteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨16, by decide⟩ + 2 * q'N ⟨16, by decide⟩ + q''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seventeen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨17, by decide⟩ + 2 * q'N ⟨17, by decide⟩ + q''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 18) :
    2 * (∑ j, adamsBashforth9.toGLM.B k j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V k l * q''N l =
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

end AB9GE2

theorem adamsBashforth9_toGLM_hasOrderGe2 :
    adamsBashforth9.toGLM.HasOrderGe2 := by
  refine ⟨AB9GE2.qN, AB9GE2.q'N, AB9GE2.q''N,
    ?_, ?_, AB9GE2.q'_obligation, AB9GE2.q''_obligation⟩
  · exact adamsBashforth9.toGLM_V_nordsieckQ_eq adamsBashforth9_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth9, Fin.addCases,
      Fin.sum_univ_succ, AB9GE2.qN]

theorem adamsBashforth9_toGLM_hasOrderGe1 :
    adamsBashforth9.toGLM.HasOrderGe1 :=
  adamsBashforth9_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 9-step

`adamsBashforth9` (`s = 9`, eighteen GLM input slots `Fin 18`, explicit
with `β_s = 0`, classical order 9) embeds as a GLM of order ≥ 3 using
the `C = s² − 2 β_s · s = 81` Nordsieck shift (since `β_s = 0`,
`C = s² = 81`). Mirrors AB8GE3 (cycle 1180) with `s = 8 → 9`. At Fin 18
the heartbeat budget forces **all eighteen rows** of `q''_obligation`
and `q'''_obligation` to be extracted as private helpers (lesson from
cycles 1178/1182/1184). Boundary nuance: `q''_obligation_zero` and
`q''_obligation_nine` (the first past-`h·f` row, `β_s = 0`) close with
`simp` alone (no `norm_num`); all other q'' rows and all q''' rows
close with `simp + norm_num`. -/

namespace AB9GE3

private noncomputable def qN : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 9 => (1 : ℝ)) (fun _ : Fin 9 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ)) (fun _ : Fin 9 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ) ^ 2 - 81)
    (fun j : Fin 9 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ) ^ 3 - 3 * 81 * ((j : ℕ) : ℝ))
    (fun j : Fin 9 => 3 * (((j : ℕ) : ℝ) ^ 2 - 81))
    (Fin.cast (Nat.two_mul 9) k)

private theorem q'_obligation (k : Fin 18) :
    (∑ j, adamsBashforth9.toGLM.B k j) +
        ∑ l, adamsBashforth9.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_zero :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨0, by decide⟩ + 2 * q'N ⟨0, by decide⟩ + q''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_one :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨1, by decide⟩ + 2 * q'N ⟨1, by decide⟩ + q''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_two :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨2, by decide⟩ + 2 * q'N ⟨2, by decide⟩ + q''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_three :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨3, by decide⟩ + 2 * q'N ⟨3, by decide⟩ + q''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_four :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨4, by decide⟩ + 2 * q'N ⟨4, by decide⟩ + q''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row, `β_s = 0`). Closes with
just `simp` — adding `norm_num` triggers "no goals to be solved". -/
private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_sixteen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨16, by decide⟩ + 2 * q'N ⟨16, by decide⟩ + q''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seventeen :
    2 * (∑ j, adamsBashforth9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨17, by decide⟩ + 2 * q'N ⟨17, by decide⟩ + q''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 18) :
    2 * (∑ j, adamsBashforth9.toGLM.B k j *
          ((∑ i, adamsBashforth9.toGLM.A j i) +
            ∑ l, adamsBashforth9.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth9.toGLM.V k l * q''N l =
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

private theorem q'''_obligation_zero :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨0, by decide⟩ + 3 * q'N ⟨0, by decide⟩ +
        3 * q''N ⟨0, by decide⟩ + q'''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_one :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨1, by decide⟩ + 3 * q'N ⟨1, by decide⟩ +
        3 * q''N ⟨1, by decide⟩ + q'''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_two :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨2, by decide⟩ + 3 * q'N ⟨2, by decide⟩ +
        3 * q''N ⟨2, by decide⟩ + q'''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_three :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨3, by decide⟩ + 3 * q'N ⟨3, by decide⟩ +
        3 * q''N ⟨3, by decide⟩ + q'''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_four :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row, `β_s = 0`). Unlike the
analogous `q''` boundary row, the `C = 81` shift pulls a residual numeric
goal, so `norm_num` is required here. -/
private theorem q'''_obligation_nine :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_twelve :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨12, by decide⟩ + 3 * q'N ⟨12, by decide⟩ +
        3 * q''N ⟨12, by decide⟩ + q'''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_thirteen :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨13, by decide⟩ + 3 * q'N ⟨13, by decide⟩ +
        3 * q''N ⟨13, by decide⟩ + q'''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fourteen :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨14, by decide⟩ + 3 * q'N ⟨14, by decide⟩ +
        3 * q''N ⟨14, by decide⟩ + q'''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fifteen :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨15, by decide⟩ + 3 * q'N ⟨15, by decide⟩ +
        3 * q''N ⟨15, by decide⟩ + q'''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_sixteen :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨16, by decide⟩ + 3 * q'N ⟨16, by decide⟩ +
        3 * q''N ⟨16, by decide⟩ + q'''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seventeen :
    6 * (∑ j, adamsBashforth9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨17, by decide⟩ + 3 * q'N ⟨17, by decide⟩ +
        3 * q''N ⟨17, by decide⟩ + q'''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 18) :
    6 * (∑ j, adamsBashforth9.toGLM.B k j *
            ((∑ i, adamsBashforth9.toGLM.A j i *
                ((∑ i', adamsBashforth9.toGLM.A i i') +
                  ∑ l, adamsBashforth9.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth9.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth9.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · exact q'''_obligation_zero
  · exact q'''_obligation_one
  · exact q'''_obligation_two
  · exact q'''_obligation_three
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
  · exact q'''_obligation_sixteen
  · exact q'''_obligation_seventeen

end AB9GE3

theorem adamsBashforth9_toGLM_hasOrderGe3 :
    adamsBashforth9.toGLM.HasOrderGe3 := by
  refine ⟨AB9GE3.qN, AB9GE3.q'N, AB9GE3.q''N, AB9GE3.q'''N,
    ?_, ?_, AB9GE3.q'_obligation, AB9GE3.q''_obligation,
    AB9GE3.q'''_obligation⟩
  · exact adamsBashforth9.toGLM_V_nordsieckQ_eq adamsBashforth9_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth9, Fin.addCases,
      Fin.sum_univ_succ, AB9GE3.qN]

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 9-step

`adamsMoulton9` (`s = 9`, eighteen GLM input slots `Fin 18`, **implicit**
with `β_s = 2082753/7257600 ≠ 0`, classical order 10) embeds as a GLM of
order ≥ 2 using the unshifted natural Nordsieck vectors. Mirrors AM8GE2
(cycle 1182) with `8 → 9`, `Fin 16 → Fin 18`, `adamsMoulton8 →
adamsMoulton9`. AM-family GE2 is unshifted (no Pascal `C` shift); the
boundary `k = 9` row (first past-`h·f`) closes with just `simp` (no
`norm_num`), matching the AM7GE2 / AM8GE2 boundary nuance. -/

namespace AM9GE2

private noncomputable def qN : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 9 => (1 : ℝ)) (fun _ : Fin 9 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ)) (fun _ : Fin 9 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 9 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private theorem q'_obligation (k : Fin 18) :
    (∑ j, adamsMoulton9.toGLM.B k j) +
        ∑ l, adamsMoulton9.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_zero :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨0, by decide⟩ + 2 * q'N ⟨0, by decide⟩ + q''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_one :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨1, by decide⟩ + 2 * q'N ⟨1, by decide⟩ + q''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_two :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨2, by decide⟩ + 2 * q'N ⟨2, by decide⟩ + q''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_three :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨3, by decide⟩ + 2 * q'N ⟨3, by decide⟩ + q''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_four :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨4, by decide⟩ + 2 * q'N ⟨4, by decide⟩ + q''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row). Closes with just
`simp` — adding `norm_num` triggers "no goals to be solved", matching
the AM-family boundary nuance (AM7 k = 7, AM8 k = 8). -/
private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_sixteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨16, by decide⟩ + 2 * q'N ⟨16, by decide⟩ + q''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seventeen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨17, by decide⟩ + 2 * q'N ⟨17, by decide⟩ + q''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 18) :
    2 * (∑ j, adamsMoulton9.toGLM.B k j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V k l * q''N l =
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

end AM9GE2

theorem adamsMoulton9_toGLM_hasOrderGe2 :
    adamsMoulton9.toGLM.HasOrderGe2 := by
  refine ⟨AM9GE2.qN, AM9GE2.q'N, AM9GE2.q''N,
    ?_, ?_, AM9GE2.q'_obligation, AM9GE2.q''_obligation⟩
  · exact adamsMoulton9.toGLM_V_nordsieckQ_eq adamsMoulton9_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton9, Fin.addCases,
      Fin.sum_univ_succ, AM9GE2.qN]

theorem adamsMoulton9_toGLM_hasOrderGe1 :
    adamsMoulton9.toGLM.HasOrderGe1 :=
  adamsMoulton9_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 9-step

`adamsMoulton9` (`s = 9`, eighteen GLM input slots `Fin 18`, **implicit**
with `β_s = 2082753/7257600 ≠ 0`, classical order 10) embeds as a GLM of
order ≥ 3 using the Pascal-shifted Nordsieck vectors with shift constant
`C = s² − 2 · β_s · s = 81 − 18 · (2082753/7257600) = 30576447/403200`.

Mirrors AB9GE3 with `adamsBashforth9 → adamsMoulton9`, `81 →
30576447/403200`. Eighteen per-row `q''` and `q'''` helpers needed at
`Fin 18` to fit the 200000-heartbeat cap. Boundary `k = 9` row for `q''`
closes with bare `simp` (AM-family nuance). -/

namespace AM9GE3

private noncomputable def qN : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 9 => (1 : ℝ)) (fun _ : Fin 9 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ)) (fun _ : Fin 9 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 => ((j : ℕ) : ℝ) ^ 2 - 30576447/403200)
    (fun j : Fin 9 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 9) k)

private noncomputable def q'''N : Fin (2 * 9) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 9 =>
      ((j : ℕ) : ℝ) ^ 3 - 3 * (30576447/403200) * ((j : ℕ) : ℝ))
    (fun j : Fin 9 => 3 * (((j : ℕ) : ℝ) ^ 2 - 30576447/403200))
    (Fin.cast (Nat.two_mul 9) k)

private theorem q'_obligation (k : Fin 18) :
    (∑ j, adamsMoulton9.toGLM.B k j) +
        ∑ l, adamsMoulton9.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_zero :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨0, by decide⟩ + 2 * q'N ⟨0, by decide⟩ + q''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_one :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨1, by decide⟩ + 2 * q'N ⟨1, by decide⟩ + q''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_two :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨2, by decide⟩ + 2 * q'N ⟨2, by decide⟩ + q''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_three :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨3, by decide⟩ + 2 * q'N ⟨3, by decide⟩ + q''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_four :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨4, by decide⟩ + 2 * q'N ⟨4, by decide⟩ + q''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row). AM-family q'' boundary
closes with `simp` alone — adding `norm_num` triggers "no goals to be
solved". -/
private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_twelve :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨12, by decide⟩ + 2 * q'N ⟨12, by decide⟩ + q''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_thirteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨13, by decide⟩ + 2 * q'N ⟨13, by decide⟩ + q''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fourteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨14, by decide⟩ + 2 * q'N ⟨14, by decide⟩ + q''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_fifteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨15, by decide⟩ + 2 * q'N ⟨15, by decide⟩ + q''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_sixteen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨16, by decide⟩ + 2 * q'N ⟨16, by decide⟩ + q''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_seventeen :
    2 * (∑ j, adamsMoulton9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q''N l =
      qN ⟨17, by decide⟩ + 2 * q'N ⟨17, by decide⟩ + q''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 18) :
    2 * (∑ j, adamsMoulton9.toGLM.B k j *
          ((∑ i, adamsMoulton9.toGLM.A j i) +
            ∑ l, adamsMoulton9.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton9.toGLM.V k l * q''N l =
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

private theorem q'''_obligation_zero :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨0, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨0, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨0, by decide⟩ + 3 * q'N ⟨0, by decide⟩ +
        3 * q''N ⟨0, by decide⟩ + q'''N ⟨0, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_one :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨1, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨1, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨1, by decide⟩ + 3 * q'N ⟨1, by decide⟩ +
        3 * q''N ⟨1, by decide⟩ + q'''N ⟨1, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_two :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨2, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨2, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨2, by decide⟩ + 3 * q'N ⟨2, by decide⟩ +
        3 * q''N ⟨2, by decide⟩ + q'''N ⟨2, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_three :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨3, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨3, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨3, by decide⟩ + 3 * q'N ⟨3, by decide⟩ +
        3 * q''N ⟨3, by decide⟩ + q'''N ⟨3, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_four :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨4, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨4, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨5, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨5, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨6, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨6, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨7, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨7, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨8, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨8, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Boundary `k = 9` case (first past-`h·f` row). The non-zero shift
`C = 30576447/403200` leaves a numeric residue that needs `norm_num`. -/
private theorem q'''_obligation_nine :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨9, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨9, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨10, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨10, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨11, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨11, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_twelve :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨12, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨12, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨12, by decide⟩ + 3 * q'N ⟨12, by decide⟩ +
        3 * q''N ⟨12, by decide⟩ + q'''N ⟨12, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_thirteen :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨13, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨13, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨13, by decide⟩ + 3 * q'N ⟨13, by decide⟩ +
        3 * q''N ⟨13, by decide⟩ + q'''N ⟨13, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fourteen :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨14, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨14, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨14, by decide⟩ + 3 * q'N ⟨14, by decide⟩ +
        3 * q''N ⟨14, by decide⟩ + q'''N ⟨14, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_fifteen :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨15, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨15, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨15, by decide⟩ + 3 * q'N ⟨15, by decide⟩ +
        3 * q''N ⟨15, by decide⟩ + q'''N ⟨15, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_sixteen :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨16, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨16, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨16, by decide⟩ + 3 * q'N ⟨16, by decide⟩ +
        3 * q''N ⟨16, by decide⟩ + q'''N ⟨16, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seventeen :
    6 * (∑ j, adamsMoulton9.toGLM.B (⟨17, by decide⟩ : Fin 18) j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V (⟨17, by decide⟩ : Fin 18) l * q'''N l =
      qN ⟨17, by decide⟩ + 3 * q'N ⟨17, by decide⟩ +
        3 * q''N ⟨17, by decide⟩ + q'''N ⟨17, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 18) :
    6 * (∑ j, adamsMoulton9.toGLM.B k j *
            ((∑ i, adamsMoulton9.toGLM.A j i *
                ((∑ i', adamsMoulton9.toGLM.A i i') +
                  ∑ l, adamsMoulton9.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton9.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton9.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · exact q'''_obligation_zero
  · exact q'''_obligation_one
  · exact q'''_obligation_two
  · exact q'''_obligation_three
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
  · exact q'''_obligation_sixteen
  · exact q'''_obligation_seventeen

end AM9GE3

theorem adamsMoulton9_toGLM_hasOrderGe3 :
    adamsMoulton9.toGLM.HasOrderGe3 := by
  refine ⟨AM9GE3.qN, AM9GE3.q'N, AM9GE3.q''N, AM9GE3.q'''N,
    ?_, ?_, AM9GE3.q'_obligation, AM9GE3.q''_obligation,
    AM9GE3.q'''_obligation⟩
  · exact adamsMoulton9.toGLM_V_nordsieckQ_eq adamsMoulton9_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton9, Fin.addCases, Fin.sum_univ_succ,
      AM9GE3.qN]
