import OpenMath.LMMAsGLM

/-!
# Butcher §530 — LMM-as-GLM order-≥ 2 and order-≥ 3 witnesses

Concrete `HasOrderGe2` and `HasOrderGe3` certificates for the
LMM-as-GLM embedding of named multistep methods. The order-≥ 1
witnesses (one-liners) live in `OpenMath/LMMAsGLM.lean`; this file
hosts the Nordsieck-shifted Taylor scaffolds.

Each method is wrapped in a private namespace `<name>GE<N>` carrying
local `qN / q'N / q''N / q'''N` Nordsieck input vectors and per-row
`q'''_obligation_*` helpers (cycle 800 helper-extraction recipe).

Extracted from `OpenMath/LMMAsGLM.lean` (cycle 1150) to keep the parent
file under the project's hard line cap.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §530.
-/

open Finset Real

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 5-step

`adamsBashforth5` (`s = 5`, ten GLM input slots `Fin 10`, explicit with
`β_s = 0`, order 5) embeds as a GLM of order ≥ 2. Cycle 786 noted that
inline `all_goals simp; all_goals norm_num` on the `Fin 10` q'-row
exceeds the 200 000 heartbeat ceiling; the cycle 800 helper-extraction
recipe (per-case `Fin 10` literals as private theorems) discharges
each branch on a fresh budget. Natural Nordsieck Taylor template
(no shift). -/
namespace AB5GE2

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private theorem q'_obligation (k : Fin 10) :
    (∑ j, adamsBashforth5.toGLM.B k j) +
        ∑ l, adamsBashforth5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, adamsBashforth5.toGLM.B k j *
          ((∑ i, adamsBashforth5.toGLM.A j i) +
            ∑ l, adamsBashforth5.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

end AB5GE2

theorem adamsBashforth5_toGLM_hasOrderGe2 :
    adamsBashforth5.toGLM.HasOrderGe2 := by
  refine ⟨AB5GE2.qN, AB5GE2.q'N, AB5GE2.q''N,
    ?_, ?_, AB5GE2.q'_obligation, AB5GE2.q''_obligation⟩
  · exact adamsBashforth5.toGLM_V_nordsieckQ_eq adamsBashforth5_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      AB5GE2.qN]

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 5-step

`adamsMoulton5` (`s = 5`, ten GLM input slots `Fin 10`, implicit with
`β_s = 475/1440 ≠ 0`, classical order 6) embeds as a GLM of order ≥ 2.
Same helper-extraction recipe as AB5GE2 (cycle 1140), with the AM3GE2
β_s ≠ 0 treatment of the U·𝟙 closure row (cycle 802 BDF3GE3 noted that
the implicit closure row may need `norm_num` after `simp`). Natural
Nordsieck Taylor template (no shift). -/
namespace AM5GE2

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private theorem q'_obligation (k : Fin 10) :
    (∑ j, adamsMoulton5.toGLM.B k j) +
        ∑ l, adamsMoulton5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, adamsMoulton5.toGLM.B k j *
          ((∑ i, adamsMoulton5.toGLM.A j i) +
            ∑ l, adamsMoulton5.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

end AM5GE2

theorem adamsMoulton5_toGLM_hasOrderGe2 :
    adamsMoulton5.toGLM.HasOrderGe2 := by
  refine ⟨AM5GE2.qN, AM5GE2.q'N, AM5GE2.q''N,
    ?_, ?_, AM5GE2.q'_obligation, AM5GE2.q''_obligation⟩
  · exact adamsMoulton5.toGLM_V_nordsieckQ_eq adamsMoulton5_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      AM5GE2.qN]

theorem adamsMoulton5_toGLM_hasOrderGe1 :
    adamsMoulton5.toGLM.HasOrderGe1 :=
  adamsMoulton5_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 5-step

`adamsBashforth5` (`s = 5`, ten GLM input slots `Fin 10`, explicit with
`β_s = 0`, classical order 5) embeds as a GLM of order ≥ 3. The shift
constant is `C := s² − 2 β_s s = 25 − 0 = 25`, matching the AB ladder
(AB2→1, AB3→9, AB4→16, AB5→25). Same helper-extraction recipe as
AB4GE3 / BDF4GE3 / AM4GE3, but on `Fin 10`: each case in the q'''
obligation gets its own `· simp; norm_num` block, with the heaviest
cases (`k = 4` last past-`y` row, `k = 9` last past-`h·f` row)
preemptively factored into separate private theorems for fresh
heartbeat budgets. -/
namespace AB5GE3

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2 - 25)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 3 - 3 * 25 * ((j : ℕ) : ℝ))
    (fun j : Fin 5 => 3 * (((j : ℕ) : ℝ) ^ 2 - 25))
    (Fin.cast (Nat.two_mul 5) k)

/-- q' obligation for AB5GE3 — extracted as a private theorem (fresh
heartbeat budget per `Fin 10` row); cycle 1140 verified this shape on
the unshifted AB5GE2 q'-row, and the AB5GE3 q'N is identical. -/
private theorem q'_obligation (k : Fin 10) :
    (∑ j, adamsBashforth5.toGLM.B k j) +
        ∑ l, adamsBashforth5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- q'' obligation for AB5GE3 — extracted as a private theorem (fresh
heartbeat budget); same shape as the cycle 1140 AB5GE2 q''-row but with
the shifted q''N (j² − 25 on past-`y`). -/
private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, adamsBashforth5.toGLM.B k j *
          ((∑ i, adamsBashforth5.toGLM.A j i) +
            ∑ l, adamsBashforth5.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

/-- Helper for the `k = 4` case (last past-`y` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_four :
    6 * (∑ j, adamsBashforth5.toGLM.B (⟨4, by decide⟩ : Fin 10) j *
            ((∑ i, adamsBashforth5.toGLM.A j i *
                ((∑ i', adamsBashforth5.toGLM.A i i') +
                  ∑ l, adamsBashforth5.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth5.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth5.toGLM.V (⟨4, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 7` case of `q'''_obligation`. Factored
into a private theorem so it gets a fresh heartbeat budget; the inline
`simp; norm_num` block exhausts the 200000 limit at this case on the
`Fin 10` AB5 row. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth5.toGLM.B (⟨7, by decide⟩ : Fin 10) j *
            ((∑ i, adamsBashforth5.toGLM.A j i *
                ((∑ i', adamsBashforth5.toGLM.A i i') +
                  ∑ l, adamsBashforth5.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth5.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth5.toGLM.V (⟨7, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 8` case of `q'''_obligation`. Factored into a
private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_eight :
    6 * (∑ j, adamsBashforth5.toGLM.B (⟨8, by decide⟩ : Fin 10) j *
            ((∑ i, adamsBashforth5.toGLM.A j i *
                ((∑ i', adamsBashforth5.toGLM.A i i') +
                  ∑ l, adamsBashforth5.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth5.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth5.toGLM.V (⟨8, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 9` case (last past-`h·f` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_nine :
    6 * (∑ j, adamsBashforth5.toGLM.B (⟨9, by decide⟩ : Fin 10) j *
            ((∑ i, adamsBashforth5.toGLM.A j i *
                ((∑ i', adamsBashforth5.toGLM.A i i') +
                  ∑ l, adamsBashforth5.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth5.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth5.toGLM.V (⟨9, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 10) :
    6 * (∑ j, adamsBashforth5.toGLM.B k j *
            ((∑ i, adamsBashforth5.toGLM.A j i *
                ((∑ i', adamsBashforth5.toGLM.A i i') +
                  ∑ l, adamsBashforth5.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth5.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth5.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine

end AB5GE3

theorem adamsBashforth5_toGLM_hasOrderGe3 :
    adamsBashforth5.toGLM.HasOrderGe3 := by
  refine ⟨AB5GE3.qN, AB5GE3.q'N, AB5GE3.q''N, AB5GE3.q'''N,
    ?_, ?_, AB5GE3.q'_obligation, AB5GE3.q''_obligation,
    AB5GE3.q'''_obligation⟩
  · exact adamsBashforth5.toGLM_V_nordsieckQ_eq adamsBashforth5_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth5, Fin.addCases,
      Fin.sum_univ_succ, AB5GE3.qN]

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 5-step

`adamsMoulton5` (`s = 5`, ten GLM input slots `Fin 10`, implicit with
`β_s = 475/1440 ≠ 0`, classical order 6) embeds as a GLM of order ≥ 3.
The shift constant is `C := s² − 2 β_s s = 25 − 2·(475/1440)·5 =
25 − 475/144 = 3125 / 144`. Same helper-extraction recipe as AB5GE3
(cycle 1142). -/
namespace AM5GE3

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2 - 3125 / 144)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 3 - 3 * (3125 / 144) * ((j : ℕ) : ℝ))
    (fun j : Fin 5 => 3 * (((j : ℕ) : ℝ) ^ 2 - 3125 / 144))
    (Fin.cast (Nat.two_mul 5) k)

/-- q' obligation for AM5GE3 — extracted as a private theorem (fresh
heartbeat budget per `Fin 10` row). -/
private theorem q'_obligation (k : Fin 10) :
    (∑ j, adamsMoulton5.toGLM.B k j) +
        ∑ l, adamsMoulton5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- q'' obligation for AM5GE3 — extracted as a private theorem (fresh
heartbeat budget); same shape as the AB5GE3 q''-row but with the
implicit AM5 weights and the shifted q''N (j² − 3125/144 on past-`y`). -/
private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, adamsMoulton5.toGLM.B k j *
          ((∑ i, adamsMoulton5.toGLM.A j i) +
            ∑ l, adamsMoulton5.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

/-- Helper for the `k = 4` case (last past-`y` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_four :
    6 * (∑ j, adamsMoulton5.toGLM.B (⟨4, by decide⟩ : Fin 10) j *
            ((∑ i, adamsMoulton5.toGLM.A j i *
                ((∑ i', adamsMoulton5.toGLM.A i i') +
                  ∑ l, adamsMoulton5.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton5.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton5.toGLM.V (⟨4, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 7` case of `q'''_obligation`. Factored
into a private theorem so it gets a fresh heartbeat budget; the inline
`simp; norm_num` block exhausts the 200000 limit at this case on the
`Fin 10` AM5 row. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsMoulton5.toGLM.B (⟨7, by decide⟩ : Fin 10) j *
            ((∑ i, adamsMoulton5.toGLM.A j i *
                ((∑ i', adamsMoulton5.toGLM.A i i') +
                  ∑ l, adamsMoulton5.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton5.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton5.toGLM.V (⟨7, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 8` case of `q'''_obligation`. Factored into a
private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_eight :
    6 * (∑ j, adamsMoulton5.toGLM.B (⟨8, by decide⟩ : Fin 10) j *
            ((∑ i, adamsMoulton5.toGLM.A j i *
                ((∑ i', adamsMoulton5.toGLM.A i i') +
                  ∑ l, adamsMoulton5.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton5.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton5.toGLM.V (⟨8, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 9` case (last past-`h·f` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_nine :
    6 * (∑ j, adamsMoulton5.toGLM.B (⟨9, by decide⟩ : Fin 10) j *
            ((∑ i, adamsMoulton5.toGLM.A j i *
                ((∑ i', adamsMoulton5.toGLM.A i i') +
                  ∑ l, adamsMoulton5.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton5.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton5.toGLM.V (⟨9, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 10) :
    6 * (∑ j, adamsMoulton5.toGLM.B k j *
            ((∑ i, adamsMoulton5.toGLM.A j i *
                ((∑ i', adamsMoulton5.toGLM.A i i') +
                  ∑ l, adamsMoulton5.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton5.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton5.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine

end AM5GE3

theorem adamsMoulton5_toGLM_hasOrderGe3 :
    adamsMoulton5.toGLM.HasOrderGe3 := by
  refine ⟨AM5GE3.qN, AM5GE3.q'N, AM5GE3.q''N, AM5GE3.q'''N,
    ?_, ?_, AM5GE3.q'_obligation, AM5GE3.q''_obligation,
    AM5GE3.q'''_obligation⟩
  · exact adamsMoulton5.toGLM_V_nordsieckQ_eq adamsMoulton5_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton5, Fin.addCases,
      Fin.sum_univ_succ, AM5GE3.qN]

/-! ### §530 LMM-as-GLM order-≥ 2 witness — trapezoidal rule

The trapezoidal rule (`s = 1`, two GLM input slots `Fin 2`) embeds as a
GLM of order ≥ 2. The witness uses `(q, q', q'')` with
`q = (1, 0)` (past-`y` indicator), `q' = (0, 1)` (Nordsieck `h·y'_n`
content), and `q'' = 0` — the second-derivative identity collapses to
`2 (B c) = q + 2 q'` because the trapezoid `B`-block already carries the
order-2 Taylor content directly (`B[0,0] = 1/2`, `B[1,0] = 1`,
`c_0 = 1`). -/
theorem trapezoidalRule_toGLM_hasOrderGe2 :
    trapezoidalRule.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 1) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 1) k),
    fun k : Fin (2 * 1) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 1 => ((j : ℕ) : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 1) k),
    fun _ : Fin (2 * 1) => (0 : ℝ),
    ?_, ?_, ?_, ?_⟩
  · -- V q = q. The witness is `LMM.nordsieckQ 1` definitionally; reuse the
    -- exposed cycle 614 lemma.
    exact trapezoidalRule.toGLM_V_nordsieckQ_eq trapezoidalRule_consistent
  · -- U q = 𝟙. Single stage; one obligation indexed by `i : Fin 1`.
    intro i; fin_cases i
    simp [LMM.toGLM, trapezoidalRule, Fin.addCases]
  · -- (B 𝟙) + V q' = q + q'. The trapezoid coefficients close both `Fin 2`
    -- cases by direct expansion.
    intro k; fin_cases k
    all_goals simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.sum_univ_two]
    all_goals norm_num
  · -- 2 (B c) + V q'' = q + 2 q' + q''. With `q'' ≡ 0` this collapses to
    -- `2 (B c) = q + 2 q'`; `c_0 = 1` for trapezoid and both rows verify.
    intro k; fin_cases k
    all_goals simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.sum_univ_two]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF2

BDF2 (`s = 2`, four GLM input slots `Fin 4`) embeds as a GLM of order ≥ 2.
The witness uses the Nordsieck Taylor-moment table:
`q' j = (j : ℝ)` on past-`y` and `1` on past-`h·f`,
`q'' j = (j : ℝ)²` on past-`y` and `2 (j : ℝ)` on past-`h·f`. For
BDF2 (s = 2) this gives `q'' = (0, 1, 0, 2)`, which matches the
constraint solution of the second-derivative compatibility identity. -/
theorem bdf2_toGLM_hasOrderGe2 :
    bdf2.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf2.toGLM_V_nordsieckQ_eq bdf2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 2-step

`adamsBashforth2` (`s = 2`, four GLM input slots `Fin 4`, explicit with
`β_s = 0`) embeds as a GLM of order ≥ 2. The witness uses the natural
Nordsieck Taylor template (no shift): `q' j = j` on past-`y` and `1`
on past-`h·f`, `q'' j = j²` on past-`y` and `2 j` on past-`h·f`.
Because AB2 is explicit, the implicit-row contribution (β_s · …)
vanishes, making this a strictly easier case than BDF2. -/
theorem adamsBashforth2_toGLM_hasOrderGe2 :
    adamsBashforth2.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth2.toGLM_V_nordsieckQ_eq adamsBashforth2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 3-step

`adamsBashforth3` (`s = 3`, six GLM input slots `Fin 6`, explicit with
`β_s = 0`, order 3) embeds as a GLM of order ≥ 2. The witness reuses the
cycle-782 AB2 natural Nordsieck Taylor template (no shift):
`q' j = j` on past-`y` and `1` on past-`h·f`, `q'' j = j²` on past-`y`
and `2 j` on past-`h·f`. Because AB3 is explicit (`β_s = 0`), the
implicit-row contributions vanish in every obligation. -/
theorem adamsBashforth3_toGLM_hasOrderGe2 :
    adamsBashforth3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth3.toGLM_V_nordsieckQ_eq adamsBashforth3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 3-step

`adamsMoulton3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 4)
embeds as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as
BDF2 (`q'' j = j²` on past-`y`, `2 j` on past-`h·f`); the
`(Uq'')_0`-shift used at HasOrderGe3 for AM2 is not needed at level 2. -/
theorem adamsMoulton3_toGLM_hasOrderGe2 :
    adamsMoulton3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton3.toGLM_V_nordsieckQ_eq adamsMoulton3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem adamsMoulton3_toGLM_hasOrderGe1 :
    adamsMoulton3.toGLM.HasOrderGe1 :=
  adamsMoulton3_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF3

`bdf3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 3) embeds
as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as BDF2.
HasOrderGe3 hits the heartbeat cap on the q''' obligation (cycle 780),
but HasOrderGe2 — only q'/q'' on `Fin 6` — closes within budget. -/
theorem bdf3_toGLM_hasOrderGe2 :
    bdf3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf3.toGLM_V_nordsieckQ_eq bdf3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem bdf3_toGLM_hasOrderGe1 :
    bdf3.toGLM.HasOrderGe1 :=
  bdf3_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 4-step

`adamsBashforth4` (`s = 4`, eight GLM input slots `Fin 8`, explicit with
`β_s = 0`, order 4) embeds as a GLM of order ≥ 2. Same natural Nordsieck
Taylor template as AB2/AB3 (no shift). -/
theorem adamsBashforth4_toGLM_hasOrderGe2 :
    adamsBashforth4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth4.toGLM_V_nordsieckQ_eq adamsBashforth4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 4-step

`adamsMoulton4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 5)
embeds as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as
AM3/BDF3. -/
theorem adamsMoulton4_toGLM_hasOrderGe2 :
    adamsMoulton4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton4.toGLM_V_nordsieckQ_eq adamsMoulton4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem adamsMoulton4_toGLM_hasOrderGe1 :
    adamsMoulton4.toGLM.HasOrderGe1 :=
  adamsMoulton4_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF4

`bdf4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 4) embeds
as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as BDF3. -/
theorem bdf4_toGLM_hasOrderGe2 :
    bdf4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf4.toGLM_V_nordsieckQ_eq bdf4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem bdf4_toGLM_hasOrderGe1 :
    bdf4.toGLM.HasOrderGe1 :=
  bdf4_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF5

`bdf5` (`s = 5`, ten GLM input slots `Fin 10`, implicit with
`β_s = 60/137 ≠ 0`, classical order 5) embeds as a GLM of order ≥ 2.
Same helper-extraction recipe as AM5GE2 (cycle 1144) and natural
Nordsieck Taylor template (no shift, matching BDF3GE2 / BDF4GE2). -/
namespace BDF5GE2

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private theorem q'_obligation (k : Fin 10) :
    (∑ j, bdf5.toGLM.B k j) +
        ∑ l, bdf5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, bdf5.toGLM.B k j *
          ((∑ i, bdf5.toGLM.A j i) +
            ∑ l, bdf5.toGLM.U j l * q'N l)) +
        ∑ l, bdf5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

end BDF5GE2

theorem bdf5_toGLM_hasOrderGe2 :
    bdf5.toGLM.HasOrderGe2 := by
  refine ⟨BDF5GE2.qN, BDF5GE2.q'N, BDF5GE2.q''N,
    ?_, ?_, BDF5GE2.q'_obligation, BDF5GE2.q''_obligation⟩
  · exact bdf5.toGLM_V_nordsieckQ_eq bdf5_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      BDF5GE2.qN]
    norm_num

theorem bdf5_toGLM_hasOrderGe1 :
    bdf5.toGLM.HasOrderGe1 :=
  bdf5_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF 5-step

`bdf5` (`s = 5`, ten GLM input slots `Fin 10`, implicit with
`β_s = 60/137 ≠ 0`, classical order 5) embeds as a GLM of order ≥ 3.
The shift constant is `C := s² − 2 β_s s = 25 − 2·(60/137)·5 =
25 − 600/137 = 2825 / 137`. Same helper-extraction recipe as AM5GE3
(cycle 1146). -/
namespace BDF5GE3

private noncomputable def qN : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 5 => (1 : ℝ)) (fun _ : Fin 5 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ)) (fun _ : Fin 5 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 2 - 2825/137)
    (fun j : Fin 5 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 5) k)

private noncomputable def q'''N : Fin (2 * 5) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 5 => ((j : ℕ) : ℝ) ^ 3 - 3 * (2825/137) * ((j : ℕ) : ℝ))
    (fun j : Fin 5 => 3 * (((j : ℕ) : ℝ) ^ 2 - 2825/137))
    (Fin.cast (Nat.two_mul 5) k)

/-- q' obligation for BDF5GE3 — extracted as a private theorem (fresh
heartbeat budget per `Fin 10` row). -/
private theorem q'_obligation (k : Fin 10) :
    (∑ j, bdf5.toGLM.B k j) +
        ∑ l, bdf5.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- q'' obligation for BDF5GE3 — extracted as a private theorem (fresh
heartbeat budget); same shape as the AM5GE3 q''-row but with the
implicit BDF5 weights and the shifted q''N (j² − 2825/137 on past-`y`). -/
private theorem q''_obligation (k : Fin 10) :
    2 * (∑ j, bdf5.toGLM.B k j *
          ((∑ i, bdf5.toGLM.A j i) +
            ∑ l, bdf5.toGLM.U j l * q'N l)) +
        ∑ l, bdf5.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]
  all_goals norm_num

/-- Helper for the `k = 4` case (last past-`y` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_four :
    6 * (∑ j, bdf5.toGLM.B (⟨4, by decide⟩ : Fin 10) j *
            ((∑ i, bdf5.toGLM.A j i *
                ((∑ i', bdf5.toGLM.A i i') +
                  ∑ l, bdf5.toGLM.U i l * q'N l)) +
              ∑ l, bdf5.toGLM.U j l * q''N l)) +
        ∑ l, bdf5.toGLM.V (⟨4, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 7` case of `q'''_obligation`. Factored
into a private theorem so it gets a fresh heartbeat budget; the inline
`simp; norm_num` block exhausts the 200000 limit at this case on the
`Fin 10` BDF5 row. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, bdf5.toGLM.B (⟨7, by decide⟩ : Fin 10) j *
            ((∑ i, bdf5.toGLM.A j i *
                ((∑ i', bdf5.toGLM.A i i') +
                  ∑ l, bdf5.toGLM.U i l * q'N l)) +
              ∑ l, bdf5.toGLM.U j l * q''N l)) +
        ∑ l, bdf5.toGLM.V (⟨7, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 8` case of `q'''_obligation`. Factored into a
private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_eight :
    6 * (∑ j, bdf5.toGLM.B (⟨8, by decide⟩ : Fin 10) j *
            ((∑ i, bdf5.toGLM.A j i *
                ((∑ i', bdf5.toGLM.A i i') +
                  ∑ l, bdf5.toGLM.U i l * q'N l)) +
              ∑ l, bdf5.toGLM.U j l * q''N l)) +
        ∑ l, bdf5.toGLM.V (⟨8, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

/-- Helper for the `k = 9` case (last past-`h·f` row) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_nine :
    6 * (∑ j, bdf5.toGLM.B (⟨9, by decide⟩ : Fin 10) j *
            ((∑ i, bdf5.toGLM.A j i *
                ((∑ i', bdf5.toGLM.A i i') +
                  ∑ l, bdf5.toGLM.U i l * q'N l)) +
              ∑ l, bdf5.toGLM.U j l * q''N l)) +
        ∑ l, bdf5.toGLM.V (⟨9, by decide⟩ : Fin 10) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 10) :
    6 * (∑ j, bdf5.toGLM.B k j *
            ((∑ i, bdf5.toGLM.A j i *
                ((∑ i', bdf5.toGLM.A i i') +
                  ∑ l, bdf5.toGLM.U i l * q'N l)) +
              ∑ l, bdf5.toGLM.U j l * q''N l)) +
        ∑ l, bdf5.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf5, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine

end BDF5GE3

theorem bdf5_toGLM_hasOrderGe3 :
    bdf5.toGLM.HasOrderGe3 := by
  refine ⟨BDF5GE3.qN, BDF5GE3.q'N, BDF5GE3.q''N, BDF5GE3.q'''N,
    ?_, ?_, BDF5GE3.q'_obligation, BDF5GE3.q''_obligation,
    BDF5GE3.q'''_obligation⟩
  · exact bdf5.toGLM_V_nordsieckQ_eq bdf5_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, bdf5, Fin.addCases,
      Fin.sum_univ_succ, BDF5GE3.qN]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 6-step

`adamsBashforth6` (`s = 6`, twelve GLM input slots `Fin 12`, explicit
with `β_s = 0`, classical order 6) embeds as a GLM of order ≥ 2. Same
helper-extraction recipe as AB5GE2 (cycle 1140), with `Fin 10 → Fin 12`
size bump. Natural Nordsieck Taylor template (no shift, since the GE2
obligations do not feel the `s² − 2 β_s s` constant — that enters at
GE3). -/
namespace AB6GE2

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, adamsBashforth6.toGLM.B k j) +
        ∑ l, adamsBashforth6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 5` case (last past-`y` row) for `q''_obligation` —
factored as a private theorem so it gets a fresh heartbeat budget.
At `Fin 12`, the inline `all_goals simp; all_goals norm_num` block in
the `q''_obligation` body exceeds the 200000 heartbeat ceiling on
this row (and the past-`h·f` rows below). -/
private theorem q''_obligation_five :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, adamsBashforth6.toGLM.B k j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

end AB6GE2

theorem adamsBashforth6_toGLM_hasOrderGe2 :
    adamsBashforth6.toGLM.HasOrderGe2 := by
  refine ⟨AB6GE2.qN, AB6GE2.q'N, AB6GE2.q''N,
    ?_, ?_, AB6GE2.q'_obligation, AB6GE2.q''_obligation⟩
  · exact adamsBashforth6.toGLM_V_nordsieckQ_eq adamsBashforth6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      AB6GE2.qN]

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 6-step

`adamsBashforth6` (`s = 6`, twelve GLM input slots `Fin 12`, explicit
with `β_s = 0`, classical order 6) embeds as a GLM of order ≥ 3. The
shift constant is `C := s² − 2·β_s·s = 36`. Same helper-extraction
recipe as AB5GE3 (cycle 1142), with `Fin 10 → Fin 12` size bump and the
heartbeat-driven per-row split from AB6GE2 (cycle 1154). -/
namespace AB6GE3

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2 - 36)
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 3 - 3 * 36 * ((j : ℕ) : ℝ))
    (fun j : Fin 6 => 3 * (((j : ℕ) : ℝ) ^ 2 - 36))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, adamsBashforth6.toGLM.B k j) +
        ∑ l, adamsBashforth6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsBashforth6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, adamsBashforth6.toGLM.B k j *
          ((∑ i, adamsBashforth6.toGLM.A j i) +
            ∑ l, adamsBashforth6.toGLM.U j l * q'N l)) +
        ∑ l, adamsBashforth6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

private theorem q'''_obligation_five :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_four :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨4, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨4, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsBashforth6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 12) :
    6 * (∑ j, adamsBashforth6.toGLM.B k j *
            ((∑ i, adamsBashforth6.toGLM.A j i *
                ((∑ i', adamsBashforth6.toGLM.A i i') +
                  ∑ l, adamsBashforth6.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth6.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth6.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · exact q'''_obligation_five
  · exact q'''_obligation_six
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine
  · exact q'''_obligation_ten
  · exact q'''_obligation_eleven

end AB6GE3

theorem adamsBashforth6_toGLM_hasOrderGe3 :
    adamsBashforth6.toGLM.HasOrderGe3 := by
  refine ⟨AB6GE3.qN, AB6GE3.q'N, AB6GE3.q''N, AB6GE3.q'''N,
    ?_, ?_, AB6GE3.q'_obligation, AB6GE3.q''_obligation,
    AB6GE3.q'''_obligation⟩
  · exact adamsBashforth6.toGLM_V_nordsieckQ_eq adamsBashforth6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth6, Fin.addCases,
      Fin.sum_univ_succ, AB6GE3.qN]

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 6-step

`adamsMoulton6` (`s = 6`, twelve GLM input slots `Fin 12`, implicit
with `β_s = 19087/60480`, classical order 7) embeds as a GLM of order
≥ 2. Same helper-extraction recipe as AB6GE2 (cycle 1154), with the
unshifted natural Nordsieck Taylor template (the GE2 obligations do not
feel the `s² − 2 β_s s` constant — that enters at GE3). -/
namespace AM6GE2

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, adamsMoulton6.toGLM.B k j) +
        ∑ l, adamsMoulton6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 5` case (last past-`y` row) for `q''_obligation` —
factored as a private theorem so it gets a fresh heartbeat budget. -/
private theorem q''_obligation_five :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, adamsMoulton6.toGLM.B k j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

end AM6GE2

theorem adamsMoulton6_toGLM_hasOrderGe2 :
    adamsMoulton6.toGLM.HasOrderGe2 := by
  refine ⟨AM6GE2.qN, AM6GE2.q'N, AM6GE2.q''N,
    ?_, ?_, AM6GE2.q'_obligation, AM6GE2.q''_obligation⟩
  · exact adamsMoulton6.toGLM_V_nordsieckQ_eq adamsMoulton6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      AM6GE2.qN]

theorem adamsMoulton6_toGLM_hasOrderGe1 :
    adamsMoulton6.toGLM.HasOrderGe1 :=
  adamsMoulton6_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF6

`bdf6` (`s = 6`, twelve GLM input slots `Fin 12`, implicit with
`β_s = 60/147 ≠ 0`, classical order 6) embeds as a GLM of order ≥ 2.
Same helper-extraction recipe as AB6GE2 (cycle 1154), with `Fin 10 →
Fin 12` size bump from BDF5GE2 (cycle 1148). Natural Nordsieck Taylor
template (no shift, since the GE2 obligations do not feel the
`s² − 2 β_s s` constant — that enters at GE3). -/
namespace BDF6GE2

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2)
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, bdf6.toGLM.B k j) +
        ∑ l, bdf6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 5` case (last past-`y` row) for `q''_obligation` —
factored as a private theorem so it gets a fresh heartbeat budget.
At `Fin 12`, the inline `all_goals simp; all_goals norm_num` block in
the `q''_obligation` body exceeds the 200000 heartbeat ceiling on
this row (and the past-`h·f` rows below). -/
private theorem q''_obligation_five :
    2 * (∑ j, bdf6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, bdf6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, bdf6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, bdf6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, bdf6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, bdf6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, bdf6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, bdf6.toGLM.B k j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

end BDF6GE2

theorem bdf6_toGLM_hasOrderGe2 :
    bdf6.toGLM.HasOrderGe2 := by
  refine ⟨BDF6GE2.qN, BDF6GE2.q'N, BDF6GE2.q''N,
    ?_, ?_, BDF6GE2.q'_obligation, BDF6GE2.q''_obligation⟩
  · exact bdf6.toGLM_V_nordsieckQ_eq bdf6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      BDF6GE2.qN]
    all_goals norm_num

theorem bdf6_toGLM_hasOrderGe1 :
    bdf6.toGLM.HasOrderGe1 :=
  bdf6_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF 6-step

`bdf6` (`s = 6`, twelve GLM input slots `Fin 12`, implicit with
`β_s = 60/147 = 20/49`, classical order 6) embeds as a GLM of order
≥ 3. Same helper-extraction recipe as BDF5GE3 (cycle 1152), with the
`s² − 2 β_s s` shift constant. For BDF6 (`s = 6, β_s = 20/49`)
this gives `C = 36 − 2·(20/49)·6 = 36 − 240/49 = 1524/49`. -/
namespace BDF6GE3

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2 - 1524/49)
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 3 - 3 * (1524/49) * ((j : ℕ) : ℝ))
    (fun j : Fin 6 => 3 * (((j : ℕ) : ℝ) ^ 2 - 1524/49))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, bdf6.toGLM.B k j) +
        ∑ l, bdf6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 5` row for `q''_obligation` (last past-`y` row) — extracted
for a fresh heartbeat budget at `Fin 12`. -/
private theorem q''_obligation_five :
    2 * (∑ j, bdf6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, bdf6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, bdf6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, bdf6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, bdf6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, bdf6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, bdf6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, bdf6.toGLM.B k j *
          ((∑ i, bdf6.toGLM.A j i) +
            ∑ l, bdf6.toGLM.U j l * q'N l)) +
        ∑ l, bdf6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

private theorem q'''_obligation_four :
    6 * (∑ j, bdf6.toGLM.B (⟨4, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨4, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_five :
    6 * (∑ j, bdf6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, bdf6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, bdf6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, bdf6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, bdf6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, bdf6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, bdf6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 12) :
    6 * (∑ j, bdf6.toGLM.B k j *
            ((∑ i, bdf6.toGLM.A j i *
                ((∑ i', bdf6.toGLM.A i i') +
                  ∑ l, bdf6.toGLM.U i l * q'N l)) +
              ∑ l, bdf6.toGLM.U j l * q''N l)) +
        ∑ l, bdf6.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · exact q'''_obligation_five
  · exact q'''_obligation_six
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine
  · exact q'''_obligation_ten
  · exact q'''_obligation_eleven

end BDF6GE3

theorem bdf6_toGLM_hasOrderGe3 :
    bdf6.toGLM.HasOrderGe3 := by
  refine ⟨BDF6GE3.qN, BDF6GE3.q'N, BDF6GE3.q''N, BDF6GE3.q'''N,
    ?_, ?_, BDF6GE3.q'_obligation, BDF6GE3.q''_obligation,
    BDF6GE3.q'''_obligation⟩
  · exact bdf6.toGLM_V_nordsieckQ_eq bdf6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, bdf6, Fin.addCases, Fin.sum_univ_succ,
      BDF6GE3.qN]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 6-step

`adamsMoulton6` (`s = 6`, twelve GLM input slots `Fin 12`, implicit
with `β_s = 19087/60480`, classical order 7) embeds as a GLM of order
≥ 3. Same helper-extraction recipe as AB6GE3 (cycle 1156), with the
`s² − 2 β_s s` shift constant. For AM6 (`s = 6, β_s = 19087/60480`)
this gives `C = 36 − 2·(19087/60480)·6 = 162353/5040`. -/
namespace AM6GE3

private noncomputable def qN : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 6 => (1 : ℝ)) (fun _ : Fin 6 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ)) (fun _ : Fin 6 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 2 - (162353/5040))
    (fun j : Fin 6 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 6) k)

private noncomputable def q'''N : Fin (2 * 6) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 6 => ((j : ℕ) : ℝ) ^ 3 - 3 * (162353/5040) * ((j : ℕ) : ℝ))
    (fun j : Fin 6 => 3 * (((j : ℕ) : ℝ) ^ 2 - (162353/5040)))
    (Fin.cast (Nat.two_mul 6) k)

private theorem q'_obligation (k : Fin 12) :
    (∑ j, adamsMoulton6.toGLM.B k j) +
        ∑ l, adamsMoulton6.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

private theorem q''_obligation_five :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨5, by decide⟩ + 2 * q'N ⟨5, by decide⟩ + q''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_six :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨6, by decide⟩ + 2 * q'N ⟨6, by decide⟩ + q''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]

private theorem q''_obligation_seven :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨7, by decide⟩ + 2 * q'N ⟨7, by decide⟩ + q''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eight :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨8, by decide⟩ + 2 * q'N ⟨8, by decide⟩ + q''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_nine :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨9, by decide⟩ + 2 * q'N ⟨9, by decide⟩ + q''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_ten :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨10, by decide⟩ + 2 * q'N ⟨10, by decide⟩ + q''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation_eleven :
    2 * (∑ j, adamsMoulton6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q''N l =
      qN ⟨11, by decide⟩ + 2 * q'N ⟨11, by decide⟩ + q''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N]; norm_num

private theorem q''_obligation (k : Fin 12) :
    2 * (∑ j, adamsMoulton6.toGLM.B k j *
          ((∑ i, adamsMoulton6.toGLM.A j i) +
            ∑ l, adamsMoulton6.toGLM.U j l * q'N l)) +
        ∑ l, adamsMoulton6.toGLM.V k l * q''N l =
      qN k + 2 * q'N k + q''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N]; norm_num
  · exact q''_obligation_five
  · exact q''_obligation_six
  · exact q''_obligation_seven
  · exact q''_obligation_eight
  · exact q''_obligation_nine
  · exact q''_obligation_ten
  · exact q''_obligation_eleven

private theorem q'''_obligation_five :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨5, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨5, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨5, by decide⟩ + 3 * q'N ⟨5, by decide⟩ +
        3 * q''N ⟨5, by decide⟩ + q'''N ⟨5, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_seven :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨7, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨7, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eight :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨8, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨8, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨8, by decide⟩ + 3 * q'N ⟨8, by decide⟩ +
        3 * q''N ⟨8, by decide⟩ + q'''N ⟨8, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_nine :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨9, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨9, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨9, by decide⟩ + 3 * q'N ⟨9, by decide⟩ +
        3 * q''N ⟨9, by decide⟩ + q'''N ⟨9, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_ten :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨10, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨10, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨10, by decide⟩ + 3 * q'N ⟨10, by decide⟩ +
        3 * q''N ⟨10, by decide⟩ + q'''N ⟨10, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_eleven :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨11, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨11, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨11, by decide⟩ + 3 * q'N ⟨11, by decide⟩ +
        3 * q''N ⟨11, by decide⟩ + q'''N ⟨11, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_four :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨4, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨4, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨4, by decide⟩ + 3 * q'N ⟨4, by decide⟩ +
        3 * q''N ⟨4, by decide⟩ + q'''N ⟨4, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation_six :
    6 * (∑ j, adamsMoulton6.toGLM.B (⟨6, by decide⟩ : Fin 12) j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V (⟨6, by decide⟩ : Fin 12) l * q'''N l =
      qN ⟨6, by decide⟩ + 3 * q'N ⟨6, by decide⟩ +
        3 * q''N ⟨6, by decide⟩ + q'''N ⟨6, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 12) :
    6 * (∑ j, adamsMoulton6.toGLM.B k j *
            ((∑ i, adamsMoulton6.toGLM.A j i *
                ((∑ i', adamsMoulton6.toGLM.A i i') +
                  ∑ l, adamsMoulton6.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton6.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton6.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton6, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_four
  · exact q'''_obligation_five
  · exact q'''_obligation_six
  · exact q'''_obligation_seven
  · exact q'''_obligation_eight
  · exact q'''_obligation_nine
  · exact q'''_obligation_ten
  · exact q'''_obligation_eleven

end AM6GE3

theorem adamsMoulton6_toGLM_hasOrderGe3 :
    adamsMoulton6.toGLM.HasOrderGe3 := by
  refine ⟨AM6GE3.qN, AM6GE3.q'N, AM6GE3.q''N, AM6GE3.q'''N,
    ?_, ?_, AM6GE3.q'_obligation, AM6GE3.q''_obligation,
    AM6GE3.q'''_obligation⟩
  · exact adamsMoulton6.toGLM_V_nordsieckQ_eq adamsMoulton6_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsMoulton6, Fin.addCases,
      Fin.sum_univ_succ, AM6GE3.qN]


/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 2-step

`adamsMoulton2` (`s = 2`, four GLM input slots `Fin 4`, order 3) embeds
as a GLM of order ≥ 3. The naive Nordsieck Taylor template
`q'' = j², 2j` and `q''' = j³, 3j²` does **not** satisfy
`HasOrderGe3` for any LMM with non-zero `(U q'')_0` because the
predicate's `m₂_j := (Ac)_j + (Uq'')_j` term hides an extra
`3 · (B (Uq''))_k` mismatch from the natural Taylor identity. The fix
is to shift `q''_{past-y}` by `-C` where
`C := s² - 2 · β_s · s = (Uq'')_0_natural`, which forces
`(Uq'')_0 = 0` and restores `m₂_0 = (Ac)_0 = β_s · c_0`. The
corresponding `q'''` shift is `q'''_{past-y j} := j³ - 3·C·j` and
`q'''_{past-f j} := 3·(j² - C)`. For AM2 (`s = 2, β_s = 5/12`) this
gives `C = 7/3`. -/
theorem adamsMoulton2_toGLM_hasOrderGe3 :
    adamsMoulton2.toGLM.HasOrderGe3 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2 - 7/3)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 3 - 7 * ((j : ℕ) : ℝ))
      (fun j : Fin 2 => 3 * (((j : ℕ) : ℝ) ^ 2 - 7/3))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton2.toGLM_V_nordsieckQ_eq adamsMoulton2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-- §530 projection — `adamsMoulton2.toGLM` has order ≥ 2 by dropping
the third-derivative obligation from `adamsMoulton2_toGLM_hasOrderGe3`. -/
theorem adamsMoulton2_toGLM_hasOrderGe2 :
    adamsMoulton2.toGLM.HasOrderGe2 :=
  adamsMoulton2_toGLM_hasOrderGe3.toHasOrderGe2

/-- §530 projection — `adamsMoulton2.toGLM` has order ≥ 1 by dropping
the second-derivative obligation. -/
theorem adamsMoulton2_toGLM_hasOrderGe1 :
    adamsMoulton2.toGLM.HasOrderGe1 :=
  adamsMoulton2_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 3-step

`adamsBashforth3` (`s = 3`, six GLM input slots `Fin 6`, explicit with
`β_s = 0`, order 3) embeds as a GLM of order ≥ 3. The naive Nordsieck
template `q'' = j², 2j` and `q''' = j³, 3j²` does **not** satisfy
`HasOrderGe3` for AB3: the third-derivative obligation at the
last past-`f` row `k = 5` reduces to `54 = 27`, off by `(U q'')_0 = 9`.

For AB3, `(U q'')_{0, natural}` evaluates to
`-α₂ · 2² + β₀ · 0 + β₁ · 2 + β₂ · 4 = 4 + 5 = 9` (matching the cycle
780 formula `s² − 2 β_s s = 9` with `β_s = 0`). The shift `C₂ = 9`
sets `q''_{past-y j} := j² − 9` and forces `(U q'')_0 = 0`, which
restores the q''' identity. Because `β_s = 0`, the q'' obligation has
no shift constraint at the closure row (the `β_s · c_0` term vanishes),
so any `C₂` is admissible at level 2; the constraint `C₂ = 9` comes
from the level-3 obligation at the past-`f` last row. The corresponding
`q'''` shift is `q'''_{past-y j} := j³ − 27 j` and
`q'''_{past-f j} := 3 (j² − 9)`.

Tactic structure: the q''' obligation lives on `Fin 6` and exhausts the
default `maxHeartbeats 200000` budget when discharged with a single
`all_goals simp [...]; all_goals norm_num` block (cycle 800 confirmed
the timeout at case `k = 3` even when split per `·` block in the parent
theorem). The fix is to factor the q''' obligation into its own private
helper theorem (`q'''_obligation`) so each `fin_cases k` branch gets a
fresh heartbeat budget. The four Nordsieck vectors are extracted as
`private noncomputable def`s in `namespace AB3GE3` for the same reason
— inlined `fun k => Fin.addCases ...` triggers extra elaboration work
inside the parent theorem. -/
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

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF3

`bdf3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 3) embeds
as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 9 − 36/11 = 63/11` for `β_s = 6/11`. Same
helper-extraction recipe as AB3GE3: the q''' obligation lives on `Fin 6`
and exhausts the heartbeat budget when discharged inline, so the four
Nordsieck vectors and the q''' obligation are factored as `private`
declarations inside `namespace BDF3GE3`. -/
namespace BDF3GE3

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
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 63/11)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 3 * (63/11) * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 63/11))
    (Fin.cast (Nat.two_mul 3) k)

private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, bdf3.toGLM.B k j *
            ((∑ i, bdf3.toGLM.A j i *
                ((∑ i', bdf3.toGLM.A i i') +
                  ∑ l, bdf3.toGLM.U i l * q'N l)) +
              ∑ l, bdf3.toGLM.U j l * q''N l)) +
        ∑ l, bdf3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end BDF3GE3

theorem bdf3_toGLM_hasOrderGe3 :
    bdf3.toGLM.HasOrderGe3 := by
  refine ⟨BDF3GE3.qN, BDF3GE3.q'N, BDF3GE3.q''N, BDF3GE3.q'''N,
    ?_, ?_, ?_, ?_, BDF3GE3.q'''_obligation⟩
  · exact bdf3.toGLM_V_nordsieckQ_eq bdf3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ, BDF3GE3.qN]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      BDF3GE3.qN, BDF3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      BDF3GE3.qN, BDF3GE3.q'N, BDF3GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — adamsMoulton3

`adamsMoulton3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 4)
embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 9 − 2·(3/8)·3 = 27/4` for `β_s = 9/24 = 3/8`.
Same helper-extraction recipe as AB3GE3 / BDF3GE3: the q''' obligation
lives on `Fin 6` and exhausts the heartbeat budget when discharged
inline, so the four Nordsieck vectors and the q''' obligation are
factored as `private` declarations inside `namespace AM3GE3`. -/
namespace AM3GE3

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
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 27/4)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 3 * (27/4) * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 27/4))
    (Fin.cast (Nat.two_mul 3) k)

private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, adamsMoulton3.toGLM.B k j *
            ((∑ i, adamsMoulton3.toGLM.A j i *
                ((∑ i', adamsMoulton3.toGLM.A i i') +
                  ∑ l, adamsMoulton3.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton3.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end AM3GE3

theorem adamsMoulton3_toGLM_hasOrderGe3 :
    adamsMoulton3.toGLM.HasOrderGe3 := by
  refine ⟨AM3GE3.qN, AM3GE3.q'N, AM3GE3.q''N, AM3GE3.q'''N,
    ?_, ?_, ?_, ?_, AM3GE3.q'''_obligation⟩
  · exact adamsMoulton3.toGLM_V_nordsieckQ_eq adamsMoulton3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ, AM3GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      AM3GE3.qN, AM3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      AM3GE3.qN, AM3GE3.q'N, AM3GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 4-step

`adamsBashforth4` (`s = 4`, eight GLM input slots `Fin 8`, explicit with
`β_s = 0`, order 4) embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 16 − 0 = 16`. Same helper-extraction recipe as
AB3GE3 / BDF3GE3 / AM3GE3: the q''' obligation lives on `Fin 8` and
exhausts the heartbeat budget when discharged inline, so the four
Nordsieck vectors and the q''' obligation are factored as `private`
declarations inside `namespace AB4GE3`. -/
namespace AB4GE3

private noncomputable def qN : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2 - 16)
    (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 3 - 3 * 16 * ((j : ℕ) : ℝ))
    (fun j : Fin 4 => 3 * (((j : ℕ) : ℝ) ^ 2 - 16))
    (Fin.cast (Nat.two_mul 4) k)

/-- Helper for the last `Fin 8` case (`k = 7`) of `q'''_obligation`. Factored
into its own private theorem so it gets a fresh heartbeat budget; the
inline `simp; norm_num` block consistently exhausts the 200000 limit at
this case. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth4.toGLM.B (⟨7, by decide⟩ : Fin 8) j *
            ((∑ i, adamsBashforth4.toGLM.A j i *
                ((∑ i', adamsBashforth4.toGLM.A i i') +
                  ∑ l, adamsBashforth4.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth4.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth4.toGLM.V (⟨7, by decide⟩ : Fin 8) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 8) :
    6 * (∑ j, adamsBashforth4.toGLM.B k j *
            ((∑ i, adamsBashforth4.toGLM.A j i *
                ((∑ i', adamsBashforth4.toGLM.A i i') +
                  ∑ l, adamsBashforth4.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth4.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth4.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven

end AB4GE3

theorem adamsBashforth4_toGLM_hasOrderGe3 :
    adamsBashforth4.toGLM.HasOrderGe3 := by
  refine ⟨AB4GE3.qN, AB4GE3.q'N, AB4GE3.q''N, AB4GE3.q'''N,
    ?_, ?_, ?_, ?_, AB4GE3.q'''_obligation⟩
  · exact adamsBashforth4.toGLM_V_nordsieckQ_eq adamsBashforth4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ, AB4GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      AB4GE3.qN, AB4GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      AB4GE3.qN, AB4GE3.q'N, AB4GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF 4-step

`bdf4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 4)
embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 16 − 2·(12/25)·4 = 304/25` for `β_s = 12/25`.
Same helper-extraction recipe as AB4GE3: each `Fin 8` case in the
q''' obligation gets its own block, and any cases that exceed the
heartbeat budget are factored into separate private theorems. -/
namespace BDF4GE3

private noncomputable def qN : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2 - 304/25)
    (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 3 - 3 * (304/25) * ((j : ℕ) : ℝ))
    (fun j : Fin 4 => 3 * (((j : ℕ) : ℝ) ^ 2 - 304/25))
    (Fin.cast (Nat.two_mul 4) k)

/-- Helper for the last `Fin 8` case (`k = 7`) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, bdf4.toGLM.B (⟨7, by decide⟩ : Fin 8) j *
            ((∑ i, bdf4.toGLM.A j i *
                ((∑ i', bdf4.toGLM.A i i') +
                  ∑ l, bdf4.toGLM.U i l * q'N l)) +
              ∑ l, bdf4.toGLM.U j l * q''N l)) +
        ∑ l, bdf4.toGLM.V (⟨7, by decide⟩ : Fin 8) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 8) :
    6 * (∑ j, bdf4.toGLM.B k j *
            ((∑ i, bdf4.toGLM.A j i *
                ((∑ i', bdf4.toGLM.A i i') +
                  ∑ l, bdf4.toGLM.U i l * q'N l)) +
              ∑ l, bdf4.toGLM.U j l * q''N l)) +
        ∑ l, bdf4.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven

end BDF4GE3

theorem bdf4_toGLM_hasOrderGe3 :
    bdf4.toGLM.HasOrderGe3 := by
  refine ⟨BDF4GE3.qN, BDF4GE3.q'N, BDF4GE3.q''N, BDF4GE3.q'''N,
    ?_, ?_, ?_, ?_, BDF4GE3.q'''_obligation⟩
  · exact bdf4.toGLM_V_nordsieckQ_eq bdf4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ, BDF4GE3.qN]
    norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      BDF4GE3.qN, BDF4GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      BDF4GE3.qN, BDF4GE3.q'N, BDF4GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 4-step

`adamsMoulton4` (`s = 4`, eight GLM input slots `Fin 8`, implicit with
`β_s = 251/720`, order 5) embeds as a GLM of order ≥ 3. The shift constant
is `C := s² − 2 β_s s = 16 − 2·(251/720)·4 = 1189/90`. Same
helper-extraction recipe as AB4GE3 / BDF4GE3: each `Fin 8` case in the
q''' obligation gets its own block, and any cases that exceed the
heartbeat budget are factored into separate private theorems. -/
namespace AM4GE3

private noncomputable def qN : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2 - 1189/90)
    (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 3 - 3 * (1189/90) * ((j : ℕ) : ℝ))
    (fun j : Fin 4 => 3 * (((j : ℕ) : ℝ) ^ 2 - 1189/90))
    (Fin.cast (Nat.two_mul 4) k)

/-- Helper for the last `Fin 8` case (`k = 7`) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsMoulton4.toGLM.B (⟨7, by decide⟩ : Fin 8) j *
            ((∑ i, adamsMoulton4.toGLM.A j i *
                ((∑ i', adamsMoulton4.toGLM.A i i') +
                  ∑ l, adamsMoulton4.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton4.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton4.toGLM.V (⟨7, by decide⟩ : Fin 8) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 8) :
    6 * (∑ j, adamsMoulton4.toGLM.B k j *
            ((∑ i, adamsMoulton4.toGLM.A j i *
                ((∑ i', adamsMoulton4.toGLM.A i i') +
                  ∑ l, adamsMoulton4.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton4.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton4.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven

end AM4GE3

theorem adamsMoulton4_toGLM_hasOrderGe3 :
    adamsMoulton4.toGLM.HasOrderGe3 := by
  refine ⟨AM4GE3.qN, AM4GE3.q'N, AM4GE3.q''N, AM4GE3.q'''N,
    ?_, ?_, ?_, ?_, AM4GE3.q'''_obligation⟩
  · exact adamsMoulton4.toGLM_V_nordsieckQ_eq adamsMoulton4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ, AM4GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      AM4GE3.qN, AM4GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
      AM4GE3.qN, AM4GE3.q'N, AM4GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 7-step

`adamsBashforth7` (`s = 7`, fourteen GLM input slots `Fin 14`, explicit
with `β_s = 0`, classical order 7) embeds as a GLM of order ≥ 2. Same
Nordsieck recipe as AB6GE2 (cycle 1154), with `Fin 12 → Fin 14` size
bump and per-row helper extraction for the heartbeat-heavy past-`y` and
past-`h·f` rows. -/
namespace AB7GE2

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
    (∑ j, adamsBashforth7.toGLM.B k j) +
        ∑ l, adamsBashforth7.toGLM.V k l * q'N l =
      qN k + q'N k := by
  fin_cases k
  all_goals simp [LMM.toGLM, adamsBashforth7, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N]
  all_goals norm_num

/-- Heavy `k = 6` case (last past-`y` row) for `q''_obligation`. -/
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
      qN, q'N, q''N]
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

end AB7GE2

theorem adamsBashforth7_toGLM_hasOrderGe2 :
    adamsBashforth7.toGLM.HasOrderGe2 := by
  refine ⟨AB7GE2.qN, AB7GE2.q'N, AB7GE2.q''N,
    ?_, ?_, AB7GE2.q'_obligation, AB7GE2.q''_obligation⟩
  · exact adamsBashforth7.toGLM_V_nordsieckQ_eq adamsBashforth7_consistent
  · intro i; fin_cases i
    all_goals simp [LMM.toGLM, adamsBashforth7, Fin.addCases,
      Fin.sum_univ_succ, AB7GE2.qN]

theorem adamsBashforth7_toGLM_hasOrderGe1 :
    adamsBashforth7.toGLM.HasOrderGe1 :=
  adamsBashforth7_toGLM_hasOrderGe2.toHasOrderGe1
