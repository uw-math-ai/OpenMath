# Cycle 120 Strategy — Land `aux_515D_iterated_V_bound` (Path A from issue file) and attempt geometric helper composition

## TL;DR

The single remaining sorry is `aux_515D_max_deviation_geometric_bound` at `OpenMath/Chapter5/Section515.lean:1888` (cycle 119 narrowing). Cycle 119 documented two structural blockers (the `0 ≤ M.glmAbscissae v` hypothesis for `aux_515D_construct_ell_U_phi_A`, and the iterated-V bound from `M.IsStable`). This cycle: **(i) Aristotle hygiene first**; **(ii) Land `aux_515D_iterated_V_bound` as the Path A helper** documented in `.prover-state/issues/aux_515D_iterated_V_bound.md` — this isolates the iterated-V piece into a focused signature using `Matrix.linfty_opNorm`; **(iii) If iterated-V helper closes, attempt body composition of `aux_515D_max_deviation_geometric_bound`** with the cycle 119 strategy's Path A approach (now backed by a real iterated-V lemma rather than an unverified `V_inf_norm ≤ C_stab` claim).

If both close: §515D capstone closes fully and `thm:515D` becomes axiom-clean.

If only iterated-V helper closes: net advance is +1 closed sub-helper, sorry remains in geometric helper but is now narrower (the `0 ≤ c` and per-step chain remain).

If iterated-V helper stalls: introduce ONE further narrower helper per the Backup plan below.

## Priority 0 — Aristotle hygiene

### Step 0a: Single poll of Job 2 and Job 3

Per CLAUDE.md "do not poll repeatedly", make ONE call each at the start of the cycle.

```
mcp__aristotle__get_status({project_id: "63045685-0543-4d65-91a4-8466337472bd"})  // Job 2 (cycle 117 vector signature)
mcp__aristotle__get_status({project_id: "e68b3d59-d608-42e1-9da2-413b3742c168"})  // Job 3 (cycle 118 narrowed scalar)
```

Decision matrix:

| Job 2 status | Action |
|---|---|
| `COMPLETED` with proof | Adapt the proof to cycle 117's vector-quantified `aux_515D_componentwise_deviation_tendsto_zero`. If it closes, the cycle 118 + cycle 119 narrowing chain becomes redundant — **delete `aux_515D_max_deviation_bound_tendsto_zero` and `aux_515D_max_deviation_geometric_bound`** along with cycle 118/119 compositional bodies. Skip Priority 1; verify §515D capstone. |
| `IN_PROGRESS` and progress (>22%) | Leave running. |
| `IN_PROGRESS` and stalled (≤22%, no movement since cycle 119) | Cancel via `mcp__aristotle__cancel_project` to free the slot. |
| `FAILED` | Mark as miss; cancel/free slot. |

| Job 3 status | Action |
|---|---|
| `COMPLETED` with proof | Adapt the proof to the cycle 118 helper signature (which is closed in cycle 119, but Aristotle's proof may bypass the cycle 119 narrowing). Replace cycle 119's compositional body with Aristotle's direct proof if cleaner; OR ignore if cycle 119's body is preferable. |
| `IN_PROGRESS` and progress (>11%) | Leave running. |
| `IN_PROGRESS` and stalled (≤11%, no movement since cycle 119) | Cancel via `mcp__aristotle__cancel_project`. |
| `FAILED` | Mark as miss. |

### Step 0b: Submit Aristotle Job 4 for `aux_515D_iterated_V_bound`

Build `.prover-state/aristotle_submissions/cycle_120/iterated_V_bound.lean` mirroring the cycle 116/118/119 abstract-axioms substitution pattern.

The target signature (matches the issue file's Path A recommendation):

```lean
import Mathlib

open Matrix Filter Topology

set_option maxHeartbeats 200000

theorem aux_515D_iterated_V_bound {r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ)
    (hStab : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖V ^ k‖ ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k : ℕ, ∀ x : Fin r → ℝ,
      [Nonempty (Fin r)] →
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |((V ^ k) *ᵥ x) i|)
      ≤ C' * Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |x i|) := by
  sorry
```

(Adjust the typeclass syntax as needed — `[Nonempty (Fin r)]` may need to be a regular hypothesis or a let-bound variant per Mathlib's conventions.)

This is a clean, self-contained matrix lemma with no GLM-specific hypotheses. Aristotle's premise selection should find `Matrix.linfty_opNorm`, `Matrix.linfty_opNorm_mulVec`, and bridges to Frobenius `‖·‖`. Submit immediately at cycle start.

## Priority 1 — Land `aux_515D_iterated_V_bound` as a new private helper

Per `.prover-state/issues/aux_515D_iterated_V_bound.md` "Recommended path: Path A".

### Step 1a: Insert helper signature with sorry body

Insert in `OpenMath/Chapter5/Section515.lean` immediately above `aux_515D_max_deviation_geometric_bound` (around line 1819, before its docstring). Do NOT change the signature of `aux_515D_max_deviation_geometric_bound` yet.

```lean
/-- **Iterated V bound from power-boundedness** (Path A from
`.prover-state/issues/aux_515D_iterated_V_bound.md`).

If `V` is power-bounded (`∃ C, ∀ k, ‖V^k‖ ≤ C`), then there exists a
constant `C' ≥ 0` such that for every `k` and every vector `x`,
`sup'_i |((V^k)·x) i| ≤ C' · sup'_i |x i|`. The constant `C'` is
`√r · C` via the Mathlib bridge between Frobenius norm and ∞-operator
norm.

This is the load-bearing lemma for `aux_515D_max_deviation_geometric_bound`
— it converts power-boundedness (the `M.IsStable` data) into the
sup'-form bound needed when chaining `aux_515D_per_step_recurrence`'s
geometric closed form. -/
private theorem aux_515D_iterated_V_bound {r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ)
    (hStab : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖V ^ k‖ ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k : ℕ, ∀ x : Fin r → ℝ,
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |((V ^ k) *ᵥ x) i|)
      ≤ C' * Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |x i|) := by
  sorry
```

The signature includes `[Nonempty (Fin r)]` only implicitly — `Finset.sup'` needs a non-empty witness, which we pass via the explicit `Finset.univ_nonempty`. **Verify with `lean_multi_attempt`** that the signature parses cleanly before proceeding.

If `Nonempty (Fin r)` is needed as a typeclass hypothesis, add it as `[Nonempty (Fin r)]` to the binder list. Cycle 119 successfully used this pattern in `aux_515D_max_deviation_geometric_bound`.

### Step 1b: Manual proof attempt

The proof structure (≤ 50 LOC):

```lean
  obtain ⟨C, hC_nn, hC⟩ := hStab
  -- Bridge from Frobenius `‖V^k‖` to ∞-operator-norm bound:
  -- For any matrix M and vector x, |((M *ᵥ x) i)| ≤ ‖M‖_∞ · ‖x‖_∞,
  -- where ‖M‖_∞ = max_i Σ_j |M i j| is the row-sum max.
  -- Mathlib has this as `Matrix.linfty_opNorm_mulVec` (or similar).
  -- Bridge ‖M‖_F ≥ ‖M‖_∞ via `Matrix.linfty_opNorm_le_*`.
  refine ⟨Real.sqrt r * C, ?_, ?_⟩  -- adjust if Mathlib bridge gives a different constant
  · positivity
  · intro k x
    have h_op_bound : ‖V ^ k‖ ≤ C := hC k
    -- ... use `Matrix.linfty_opNorm_mulVec` or `Matrix.norm_mulVec_le`
    sorry
```

**Search tools**:

```
lean_local_search "linfty_opNorm"
lean_loogle "Matrix _ _ _ → (_ → _) → ℝ"
lean_leansearch "matrix infinity norm bounds vector application"
```

Expected useful lemmas:
- `Matrix.linfty_opNorm_mulVec` — `‖A *ᵥ x‖_∞ ≤ ‖A‖_∞ · ‖x‖_∞`
- `Matrix.linfty_opNorm_le` — bridge from per-row sum to operator norm
- `Matrix.norm_mulVec_le` — generic Frobenius-vs-vector bound
- `Pi.norm_def` / `Pi.nnnorm_def` — `‖x‖_∞ = sup_i ‖x i‖`

### Step 1c: Aristotle Job 4 incorporation

If Aristotle Job 4 returns COMPLETED before manual proof finishes, adapt verbatim. The signature is small enough that Aristotle should be tractable.

### Step 1d: Compile + axiom check

```bash
lake build OpenMath.Chapter5.Section515
```

Expect 1 sorry warning at line ~1819 (the new helper) plus the existing 1 sorry warning at line 1888 (the cycle 119 helper). Two sorries total during this intermediate state — DO NOT panic.

## Priority 2 — Compose body of `aux_515D_max_deviation_geometric_bound`

Only attempt this if Priority 1 fully closes the iterated-V helper. Otherwise jump to Backup plan.

### Step 2a: Address the `0 ≤ c` blocker

`aux_515D_construct_ell_U_phi_A` (cycle 114) requires `0 ≤ M.glmAbscissae v` as a precondition. This cannot be derived from `IsConsistent` (cycle 119 confirmed: `glmAbscissae` can take arbitrary real values).

**Decision**: add `0 ≤ M.glmAbscissae v` as a hypothesis to `aux_515D_max_deviation_geometric_bound`'s signature. Document this as a faithfulness divergence in the docstring AND in `.prover-state/issues/aux_515D_iterated_V_bound.md`.

Rationale: Butcher's pre-§515 stage analysis tacitly assumes "ordinary" abscissae (typically `c ∈ [0, 1]^s`); see `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` for the precedent of surfacing such tacit assumptions as faithfulness divergences. The hypothesis must be propagated up to `aux_515D_max_deviation_bound_tendsto_zero` (cycle 118 helper, now closed), `aux_515D_componentwise_deviation_tendsto_zero` (cycle 117 helper), and ultimately to `aux_515D_output_tendsto` and the capstone — but only if Priority 2 succeeds.

### Step 2b: Body composition (~120 LOC)

Structure (per cycle 119 strategy Step 1–4 with iterated-V plumbing):

```lean
-- Setup
let Δx := x - x₀
let h_n : ℕ → ℝ := fun n => Δx / (n : ℝ)

-- M-matrix outputs (cycle 114 helper):
obtain ⟨ell_U, phi_A, h_ell_U_nn, h_phi_A_nn,
        h_ellU_eq, h_phiA_eq⟩ :=
  aux_515D_construct_ell_U_phi_A M.A M.U Δx (by linarith) L hL_nn
    (M.glmAbscissae v) hc_nn _h_norm

-- Iterated-V output (Priority 1 helper):
obtain ⟨C_V, hC_V_nn, hC_V⟩ := aux_515D_iterated_V_bound M.V _hStab

-- Constants α, β derived from ell_U, phi_A, M_bound:
let α : ℝ := L * (Finset.sup' Finset.univ Finset.univ_nonempty fun i =>
  ∑ j, |M.A i j| * ell_U j + ell_U i)  -- adjust to match recurrence shape
let β : ℝ := (L : ℝ)^2 * M_bound *
  (Finset.sup' Finset.univ Finset.univ_nonempty fun i => phi_A i)

-- δ_per_n n m := per-stage max-abs deviation at step m of the n-step run
let δ_per_n : ℕ → ℕ → ℝ := fun n m => Finset.sup' ...

-- Per-step recurrence via aux_515D_per_step_recurrence (cycle 113):
have h_recur : ∀ n m, m + 1 ≤ n →
    δ_per_n n (m+1) ≤ V_inf_norm · δ_per_n n m + α · h_n n · δ_per_n n m + β · (h_n n)^2 := ...

-- Closed-form via aux_515D_per_step_recurrence + aux_515D_iterated_V_bound:
have h_closed : ∀ n, 0 < n →
    δ_per_n n n ≤ C_V · (V_inf_norm + α · h_n n)^n · δ_per_n n 0
                 + β · (h_n n)^2 · ... := ...

-- Geometric sum bound + factor out:
refine ⟨C_init := C_V · Real.exp (α · Δx),
        C_lin := C_V · Real.exp (α · Δx) · β · Δx, ?_, ?_, ?_⟩
...
```

The exact constant shapes (`C_init`, `C_lin`) should be picked to match the helper's conclusion. The proof is a chain of `gcongr`, `Finset.le_sup'`, `Real.add_one_le_exp`, and ring/linarith manipulation.

### Step 2c: Faithfulness divergence — propagate `0 ≤ c`

If Step 2b closes:
1. Add `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to the signatures of `aux_515D_max_deviation_geometric_bound`, `aux_515D_max_deviation_bound_tendsto_zero` (cycle 118, already closed — body remains the same), `aux_515D_componentwise_deviation_tendsto_zero` (cycle 117), `aux_515D_output_tendsto`, and `stable_consistent_isConvergent`.
2. Document the divergence in:
   - `aux_515D_max_deviation_geometric_bound`'s docstring
   - `.prover-state/issues/aux_515D_iterated_V_bound.md` (under "Cycle 120 update")
   - `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` (add a "Cycle 120 update" section)
3. Update `lean_status.json`: `thm:515D` → `formalized` (cycle 120) IF axiom-clean. Otherwise leave `partial`.
4. Update `plan.md` `[~]` → `[x]` for `thm:515D` IF closed.

## Backup plan — if iterated-V helper or geometric helper stalls

### Backup B1: iterated-V helper stalls on Mathlib bridge

If the `Matrix.linfty_opNorm` ↔ Frobenius bridge proves elusive (no clean Mathlib lemma), introduce one MORE narrower helper:

```lean
private theorem aux_515D_frobenius_to_linfty_op {r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin r → ℝ,
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |(V *ᵥ x) i|)
      ≤ K * ‖V‖ * Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => |x i|) := by
  sorry
```

Then `aux_515D_iterated_V_bound`'s body composes this with `‖V^k‖ ≤ C`. The Mathlib bridge for `aux_515D_frobenius_to_linfty_op` becomes the focused goal for cycle 121.

### Backup B2: geometric helper stalls on per-step chain

If iterated-V helper closes but the per-step `localStepError_bound` chain (Step 2b) proves too long, introduce a sub-helper that encapsulates the chain:

```lean
private theorem aux_515D_per_step_chain {s r : ℕ}
    (M : GeneralLinearMethod s r) ... :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ ∀ n m, 0 < n → m + 1 ≤ n →
      Finset.sup' ... (fun i => |dev_{m+1} i|)
      ≤ V_inf_norm * Finset.sup' ... (fun i => |dev_m i|)
        + α * h_n n * Finset.sup' ... (fun i => |dev_m i|)
        + β * (h_n n)^2 := by
  sorry
```

Submit this to Aristotle (Job 5) with the strengthened cycle 116 `localStepError_bound` axiom. Manual proof if Aristotle stalls.

### Backup B3: propagate `0 ≤ c` blockage upward

If adding `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to `IsConvergent`'s signature breaks §513 / §514 cascades (similar to cycle 116 Phase 2's Frobenius propagation), DO NOT propagate — instead leave the geometric helper sorry'd with `_hc_nn` only as a local hypothesis, document the gap, and report partial closure. `thm:515D` row in `plan.md` stays `[~]`.

## What NOT to try

The following approaches have been documented as failed or non-viable in cycles 110–119; do NOT repeat:

1. **Direct manual closure of `aux_515D_max_deviation_geometric_bound` without the iterated-V helper.** Cycle 119 attempted this and identified two structural blockers (`0 ≤ c` and iterated-V bound). Without an `aux_515D_iterated_V_bound` lemma, the proof has no clean way to convert `M.IsStable`'s `‖V^k‖ ≤ C` to the `Finset.sup'`-form bound needed by `aux_515D_per_step_recurrence`'s output. See `.prover-state/issues/aux_515D_iterated_V_bound.md` "What was tried" §Cycle 119.

2. **Using `aux_515D_gronwall_bound` (sum-form Grönwall) for the iterated-V piece.** Cycle 118 stalled on the per-step → sum-form bridge for exactly this reason. The sum-form Grönwall requires `V_norm ≤ 1` (telescoping), which doesn't hold for general stable GLMs. Use `aux_515D_per_step_recurrence` (geometric closed form) instead.

3. **`Path B` from cycle 119 strategy (factor out `V_inf_norm^n` into the constant).** Cycle 119 strategy explicitly noted this fails when `V_inf_norm > 1` because `δ_seq n → 0` is not provable. Do not revisit.

4. **`unfold_let` tactic.** Not available in this Mathlib version; use `show ... ; rfl` instead (cycle 119 worked around this).

5. **Directly proving `0 ≤ M.glmAbscissae v` from `IsConsistent`.** Cycle 119 confirmed this is NOT derivable — `glmAbscissae` can take arbitrary real values in Butcher's formulation. Either add as a hypothesis (Step 2a) or work around.

6. **Schur form / Jordan canonical form for the iterated-V bound.** Path B from `.prover-state/issues/aux_515D_iterated_V_bound.md` is rejected — Mathlib's Jordan support is partial (see `jordan_canonical_form_missing.md`). Stick with Path A (`Matrix.linfty_opNorm`).

7. **M-matrix-style approach for V (Path C from issue file).** Documented as overkill; do not attempt.

8. **Re-polling Aristotle Jobs 2/3 mid-cycle.** Per CLAUDE.md, single-poll only. The end-of-cycle check is the only allowed re-poll.

9. **Modifying `scripts/autonomous_loop.py` or any loop infrastructure.** Out of worker scope.

10. **Raising `maxHeartbeats` above 200000.** Per CLAUDE.md, decompose instead.

## Time budget

- Priority 0 (Aristotle hygiene + Job 4 submission): 15 min.
- Priority 1 (iterated-V helper signature + manual proof): 1.5–2 hours.
  - 30 min: signature + Mathlib search via `lean_local_search`, `lean_loogle`, `lean_leansearch`.
  - 60–90 min: manual proof using `Matrix.linfty_opNorm_mulVec` + `‖V^k‖ ≤ C`.
- Priority 2 (geometric helper composition): 2–3 hours if Priority 1 succeeds.
- Backup plans: trigger if exceeding 4 hours total without progress.
- End-of-cycle: single Aristotle poll, write task results, commit.

**Total target: 3.5–5 hours.** If exceeding 5 hours without sub-step closure, execute Backup B1 (introduce `aux_515D_frobenius_to_linfty_op` with sorry body, commit, end cycle).

## Pre-commit faithfulness checklist

Per CLAUDE.md Pre-Commit Faithfulness Checklist, for any new `def` / `structure` / `theorem` introduced this cycle:

### For `aux_515D_iterated_V_bound` (new private theorem, expected this cycle)

- [ ] **Tautology check**: conclusion (`∃ C', 0 ≤ C' ∧ ∀ k x, sup'_i |(V^k *ᵥ x) i| ≤ C' · sup'_i |x i|`) does NOT appear verbatim as a hypothesis. The hypothesis is `∃ C, 0 ≤ C ∧ ∀ k, ‖V^k‖ ≤ C` (norm-of-power bound, not the sup'-form vector application bound). Genuine bridge.
- [ ] **Identity check**: proof is NOT `exact h_x`; it composes `Matrix.linfty_opNorm_mulVec` with the power-boundedness hypothesis. Real bridge work.
- [ ] **Hypothesis strength**: the hypothesis is exactly `M.IsStable`'s data, no stronger.
- [ ] **Absent theorem**: helper exists in the file; not just promised.

### For `aux_515D_max_deviation_geometric_bound` body (closure attempt, Priority 2)

If Priority 2 closes the body, the helper itself is not new (cycle 119 introduced its signature). The body composition consumes `aux_515D_iterated_V_bound`, `aux_515D_construct_ell_U_phi_A`, `aux_515D_per_step_recurrence`, `aux_515D_one_add_pow_le_exp`, and `localStepError_bound`. No new entities.

If `_hc_nn` is added to the signature (Step 2c), document the divergence per CLAUDE.md.

### Faithfulness escalation

If at any point a new private helper's conclusion equals one of its hypotheses, escalate per CLAUDE.md "Escalate immediately" — write an issue file in `.prover-state/issues/` describing the pattern.

## Post-commit deliverables

Cycle 120's `.prover-state/task_results/cycle_120.md` must include:

* **Worked on**: `aux_515D_iterated_V_bound` (new helper from `.prover-state/issues/aux_515D_iterated_V_bound.md` Path A) + optional Priority 2 attempt on `aux_515D_max_deviation_geometric_bound`.
* **Approach**: Path A from issue file (Mathlib `Matrix.linfty_opNorm` bridge) + per-cycle 119 strategy Step 4 Path A for the geometric composition.
* **Result**: SUCCESS / PARTIAL / FAILED with explicit before/after sorry counts. Build status. `#print axioms` check on `stable_consistent_isConvergent`.
* **Faithfulness check**: per the checklist above for each new entity.
* **Dead ends**: enumerate any failed Mathlib lemma lookups, unsuccessful tactic chains, etc.
* **Suggested next approach** for cycle 121.

Update:
* `.prover-state/issues/aux_515D_iterated_V_bound.md` — mark Path A as IN-PROGRESS or CLOSED.
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` — append "Cycle 120 update" with the sorry-count delta.
* `extraction/formalization_data/lean_status.json` — bump `thm:515D` cycle reference; `formalized` only if axiom-clean.
* `plan.md` — `[~]` → `[x]` for `thm:515D` only if axiom-clean.

## Pointer summary

* Sorry to close (or narrow): `OpenMath/Chapter5/Section515.lean:1888` (`aux_515D_max_deviation_geometric_bound`).
* New helper to introduce: `aux_515D_iterated_V_bound` per `.prover-state/issues/aux_515D_iterated_V_bound.md` Path A.
* Mathlib bridge target: `Matrix.linfty_opNorm_mulVec` and friends.
* Aristotle Jobs running: 2 (`63045685-...`), 3 (`e68b3d59-...`); submit Job 4 for iterated-V helper.
* Backup plans documented above (B1 Frobenius bridge, B2 per-step chain, B3 propagation freeze).

Final shot: focused single-helper landing with a clean Mathlib-backed proof, plus best-effort attempt on the next layer of composition. This continues the Backup B1 cascade pattern that has worked across cycles 117–119, with the goal of either fully closing §515D or further narrowing toward closure.
