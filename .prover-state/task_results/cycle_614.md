# Cycle 614 Results

## Worked on
Butcher §510 LMM-side sanity check: `LMM.toGLM_isConsistent` in
`OpenMath/LMMAsGLM.lean`. The matching RK-side `ButcherTableau.toGLM_isConsistent`
landed in cycle 613; this cycle adds the LMM analogue using the Nordsieck-style
witnesses suggested by the strategy.

## Approach
Sorry-first scaffold with three `?_` subgoals. Witnesses:
* `q k = Fin.addCases (fun _ : Fin s => 1) (fun _ : Fin s => 0) (Fin.cast _ k)`
  — the past-y indicator.
* `q' k = Fin.addCases (fun j : Fin s => (j : ℝ)) (fun _ : Fin s => 1) (Fin.cast _ k)`
  — `j` on past-y slot `j`, `1` on every past-`h·f` slot.

For each subgoal:
1. **`V q = q`** — reindex `Fin (2*s) → Fin (s+s)` via `Fin.sum_congr'`;
   the past-`f` half drops because `q` is zero there. Then case-split on
   `Fin.cast (Nat.two_mul s) k` via `Fin.addCases`, and within each branch
   `by_cases hj : (j : ℕ) + 1 = s` to separate "last" rows from "shift" rows.
   Closing arithmetic uses `m.normalized` and `hm.sum_α_eq_zero` (rewritten
   via `m.rho_one` + `Fin.sum_univ_castSucc`).
2. **`U q = 𝟙`** — single equation since the GLM is one-stage. Same reindex
   + split; reduces to `-∑_{l < s} m.α (Fin.castSucc l) = 1`, again from
   `m.normalized` + `hm.sum_α_eq_zero`.
3. **`(B 𝟙_s) + V q' = q + q'`** — same case-split structure with
   four row shapes:
   * **shift-y** (`j+1 < s`, k = past-y row): `Finset.sum_eq_single` at
     `l = ⟨j+1, _⟩`.
   * **last-y** (`j+1 = s`): combines `m.normalized`, `hm.sum_α_eq_zero`,
     and `hm.deriv_match` (rewritten via `m.sigma_one` and
     `Fin.sum_univ_castSucc` to peel the `j = Fin.last s` term).
     Closing step uses `linarith` after normalising `(j : ℝ) = (s : ℝ) - 1`.
   * **shift-f** (`j+1 < s`, k = past-f row): `Finset.sum_eq_single` at
     `l = ⟨j+1, _⟩` of the past-`f` summand.
   * **last-f** (`j+1 = s`): both V-row contributions vanish; B contributes
     `1`.

The `Fin.cast (Nat.two_mul s)` reindexing pattern follows the existing
`toGLM_stageMap_eq` proof template.

## Result
SUCCESS. `LMM.toGLM_isConsistent` is now sorry-free. `lake env lean
OpenMath/LMMAsGLM.lean` is clean (no errors, no warnings). File size
657 lines, well under the cap.

## Dead ends
* First `Fin.sum_congr' _ (Nat.two_mul s)` invocation refused to unify the
  metavariable for the integrand. Fix: pass the `f` and `M := ℝ` explicitly.
* `simp` after `Fin.sum_univ_add` produced `x.addNat s` (via
  `Fin.natAdd_eq_addNat`) instead of `Fin.natAdd s x`, breaking
  `Fin.addCases_right`. Fix: use `simp only [..., Fin.addCases_right]`
  without the natAdd-eq-addNat normalization.
* `congr 1; omega` failed when normalising
  `if s + l.val = s + j.val + 1 then 1 else 0 = if l.val = j.val + 1 ...`
  because `omega` did not propagate the `Fin.cast` through the val.
  Fix: `by_cases hlj : (l : ℕ) = (j : ℕ) + 1` and rewrite both branches
  with `if_pos / if_neg`.
* `simp` after `Finset.sum_eq_single` rewrote the wrong sum (the
  identically-zero `∑ 0 · l`). Fix: collapse that sum explicitly with
  `show ... = 0 by simp` first, then apply `sum_eq_single` to the
  remaining indicator sum.
* `Fin.coe_castSucc` deprecated; switched to `Fin.val_castSucc`.

## Discovery
* `Fin.sum_congr' (M := ℝ) (f := …) (Nat.two_mul s)` is the right shape
  for the §503 Nordsieck reindexing.
* The `addCases`-on-`Fin.cast` motive trick (set `kc := Fin.cast _ k`,
  then `refine kc.addCases (motive := …) ?_ ?_ rfl`) is the cleanest way
  to case-split on past-y vs past-f rows without destructuring `k.val`.
* The §503 explicit row formula matters: a "shift" V-row really is a
  Kronecker delta at `l = ⟨j+1, _⟩`, so `Finset.sum_eq_single` closes
  every shift case in two lines.

## Suggested next approach
* Now that §510 has matching RK and LMM sanity checks, the natural next
  cycle is §520 (stability matrix `M(z) = V + zB(I − zA)⁻¹U`) — landing
  the definition and the structural specialisations to RK and LMM is
  another short, tractable seam in the same flavour as §502/§503 + §510.
* Alternatively the §512–§515 convergence chain (backlog item #1) is the
  larger payoff. §512 is the convergence definition itself (multi-step
  scalar limit as `h → 0`) — that should be a single-cycle definition
  drop, after which §513 (stability necessary) is roughly Dahlquist-style.
* §515 will eventually reuse the cycle 614 witnesses: the Nordsieck
  `q / q'` decomposition is what underwrites the linear part of the
  consistency-error analysis, so the lemma already lands real
  scaffolding for that future work.
* Do NOT restart §386Aug `forestSum_assoc` until a structured plan
  exists for `cut_assoc`.
