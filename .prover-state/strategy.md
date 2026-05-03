# Cycle 107 Strategy — Close `aux_515B_eta_contraction` (the last §515 sorry)

## Status snapshot

* **Sorry count in `OpenMath/`: 1** (`Section515.lean:995`).
* **Cycle 106 landed**: `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  (Neumann-series inverse-positivity) and
  `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`
  (M-matrix comparison principle). Both clean axioms, in
  `OpenMath/Chapter5/MMatrix.lean`.
* **Aristotle**: do **not** poll either project. `8e9eec37-…`
  (cycle 105 batch) is now redundant — Priority 1+2 closed manually
  in cycle 106. `4688b630-…` (cycle 103 η-contraction batch) is >50
  hours old at 6 % and effectively dead; you may cancel it via
  `mcp__aristotle__cancel_project` if you want the slot, but a
  cancellation is **optional housekeeping** not a priority.
* **Plan posture**: `lem:515B` is `[~]` in plan.md — closing this
  sorry promotes it to `[x]`, closes §515, and unblocks
  `thm:515D` ("Stability and consistency imply convergence") for
  cycle 108+.

## Priority 1 — Close `aux_515B_eta_contraction` (REQUIRED)

This is the **sole priority** of cycle 107. The Mathlib infrastructure
is in place; the remaining work is purely the *application*.

**Where**: `OpenMath/Chapter5/Section515.lean:973-995`.

**Required signature change**: add the hypothesis

```lean
(h_norm : ‖((h₀ * L) • M.A.map (|·|) : Matrix (Fin s) (Fin s) ℝ)‖ < 1)
```

(or whichever spelling matches the `Matrix.map` / `SMul` API after
`open scoped Matrix.Norms.Frobenius` is added at the top of the
section). The norm here **must** be the same scope used in
`MMatrix.lean` (Frobenius), so the `EntrywiseNonneg.inv_one_sub_…`
and `EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` lemmas apply
directly without scope juggling.

This is a **faithfulness divergence**: the textbook tacitly assumes
"h₀ small enough"; we surface the precise condition. Document in the
docstring with one line and a `see also` pointer to
`.prover-state/issues/lem_515B_eta_contraction_deferred.md`.

**Update the unique downstream consumer**: `localStepError_bound`
at `OpenMath/Chapter5/Section515.lean:1042` invokes
`aux_515B_eta_contraction` once at line 1150. Either:

1. Add the same `h_norm` hypothesis to `localStepError_bound`'s
   signature (preferred — propagates the assumption upward to
   `lem:515B`'s signature, where it belongs), OR
2. If the matrix `(h₀ L) • |M.A|` provably satisfies `‖·‖ < 1` from
   any existing hypothesis of `localStepError_bound`, derive it
   inline (DO NOT do this without verifying — the existing
   hypotheses are bounds on `f, yex` and on `ell_U / phi_A`, none of
   which constrain `‖A‖`).

Pick option (1). Verify nothing else imports `aux_515B_eta_contraction`
(`grep -n aux_515B_eta_contraction OpenMath/`); it is `private`, so
the only call site is `localStepError_bound`.

**Proof plan** (translate Section §B "Mathematical argument" of
`lem_515B_eta_contraction_deferred.md` into Lean — the proof is
purely linear-algebraic, no analysis):

```text
Let M_pos := (h₀ * L) • A.map (fun x => |x|).
Let target : Fin s → ℝ := fun j => ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j.
Goal: ∀ j, |η j| ≤ target j.

Step 1. Triangle on _hcontraction + _hδ_max:
    ∀ j, |η j| ≤ ∑_k |U j k| · δ_max
                + h * L * ∑_k |A j k| · |η k|
                + h² L² M_bound · (½ c_j² + ∑_k |A j k · c k|)

Step 2. Rewrite RHS using _hellU_eq and _hphiA_eq, which say
    ell_U j - h₀L Σ_k|A_jk| ell_U k = Σ_k|U_jk|
    phi_A j - h₀L Σ_k|A_jk| phi_A k = ½c_j² + Σ_k|A_jk c_k|
  to identify the RHS as
    (target j) - h₀ * L * ∑_k |A j k| · target k
  i.e. ((1 - M_pos) *ᵥ target) j.
  This is a per-row linear-combination identity; the algebra is
  routine (`ring_nf` + `Finset.mul_sum` + the two side equations).

Step 3. From Step 1 + Step 2:
    ∀ j, |η j| - h * L * ∑_k |A j k| · |η k|
         ≤ ((1 - M_pos) *ᵥ target) j

Step 4. Use h ≤ h₀ + non-negativity to upgrade hL → h₀L on the LHS:
    h * L * ∑_k |A j k| · |η k| ≤ h₀ * L * ∑_k |A j k| · |η k|
    so
    |η j| - h₀ * L * ∑_k |A j k| · |η k|
        ≤ |η j| - h * L * ∑_k |A j k| · |η k|
        ≤ ((1 - M_pos) *ᵥ target) j
  i.e. ((1 - M_pos) *ᵥ |η|) j ≤ ((1 - M_pos) *ᵥ target) j
  (recognising ((1 - M_pos) *ᵥ x) j = x j - h₀L Σ |A_jk| x_k).

Step 5. Therefore ((1 - M_pos) *ᵥ (target - |η|)) j ≥ 0.

Step 6. Verify M_pos.EntrywiseNonneg from h₀_pos, hL, abs_nonneg.

Step 7. Apply
    Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
        hM_pos h_norm h_step5
  to conclude (target - |η|) j ≥ 0 entrywise, i.e. |η j| ≤ target j.
```

**Concrete Lean tactical guidance for the trickiest step (Step 2)**:

The identity to prove per row `j`:
```
∑_k |U j k| * δ_max + h^2*L^2*M_bound * (½ c_j² + ∑_k |A_jk c_k|)
  = (ell_U j * δ_max + h^2*L^2*M_bound * phi_A j)
    - h₀ * L * ∑_k |A j k| * (ell_U k * δ_max + h^2*L^2*M_bound * phi_A k)
```

Strategy:
1. `rw [_hellU_eq j]` and `rw [_hphiA_eq j]` to expose the side-equation
   form on the RHS — but you'll need them as `Σ|U jk| = ell_U j - h₀L Σ|A_jk|·ell_U k`.
   Use `linarith` or manual algebraic manipulation.
2. Expand `Finset.mul_sum` on the `h₀ L (Σ |A_jk| · target_k)` term to
   get `h₀ L Σ |A_jk| ell_U_k · δ_max + h₀ L Σ |A_jk| · h²L²M phi_A_k`.
3. `Finset.sum_add_distrib` and `ring_nf` to align summands, then
   close with the rewritten side equations.

If `ring_nf` doesn't close the final form, try
`linear_combination (δ_max) * (_hellU_eq j) + (h^2*L^2*M_bound) * (_hphiA_eq j)`
— that's the canonical incantation for "RHS minus LHS equals a known
linear combination of side equations".

**Concrete tactical guidance for Step 4 / Step 7 (the inequality lift)**:

For the comparison principle, you need
`(((1 : Matrix _ _ ℝ) - M_pos) *ᵥ (target - fun j => |η j|)) j ≥ 0`.
Three options:

* **(a) Subtraction form**: prove `((1 - M_pos) *ᵥ |η|) j ≤ ((1 - M_pos) *ᵥ target) j`
  (Step 4 directly), then expand `(target - |η|)` linearly, then apply
  the comparison principle. This is the cleanest.
* **(b) Direct entrywise expansion**: unfold `((1 - M_pos) *ᵥ v) j = v j - h₀L Σ|A_jk| v_k`
  using `Matrix.sub_mulVec` (or `Matrix.one_mulVec` + `Matrix.smul_mulVec`),
  reduce to `(target j - |η j|) - h₀L Σ|A_jk|·(target k - |η k|) ≥ 0`, and
  rearrange. This avoids the `Matrix.mulVec` distributivity dance.

Pick (a). The infrastructure lemma
`Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` takes
`∀ i, 0 ≤ ((1 - M_pos) *ᵥ v) i` and yields `∀ i, 0 ≤ v i`. Set
`v := target - |η|` (componentwise) and feed Step 5.

**Hard ceiling**: 90 minutes / ~120 LOC. If the algebra of Step 2
explodes beyond ~50 LOC, factor it out as a private helper lemma
`aux_515B_target_identity` rather than inlining.

## Priority 2 — Housekeeping (REQUIRED, post-closure)

After Priority 1 lands, do these in order:

1. **`lake build OpenMath.Chapter5.Section515`** (NOT `lake env lean` —
   that doesn't update `.olean`, per the cycle 072 lesson).
2. **Axiom check** on the closed theorem and on `localStepError_bound`:
   ```bash
   echo '#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStepError_bound' \
     | lake env lean --stdin /dev/stdin
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`.
3. **Update `plan.md`**: change `[~] lem:515B` to `[x] lem:515B` and
   bump the progress counter (currently "64 / 175"; this cycle pushes
   to 65 / 175 since `lem:515B` flips from partial to formalized).
4. **Update `extraction/formalization_data/lean_status.json`** for
   `lem:515B`: set `lean_status` to `formalized`, populate
   `lean_files` with `OpenMath/Chapter5/Section515.lean`.
5. **Update `.prover-state/issues/lem_515B_eta_contraction_deferred.md`**:
   add a "Status (cycle 107) — RESOLVED" header at top with one
   sentence describing the closure (e.g. "Closed via M-matrix
   comparison principle from cycle 106 plus an explicit
   `‖h₀L|A|‖ < 1` hypothesis (faithfulness divergence documented)").
6. **Write `.prover-state/task_results/cycle_107.md`** per the
   CLAUDE.md template.
7. (Optional) Cancel Aristotle project `4688b630-…` to free the
   slot for cycle 108 — **only** if you intend to submit a cycle 108
   batch this week.

## What NOT to try (explicitly)

* **Do NOT introduce ANY new sorry to `OpenMath/`.** Cycle 107 is a
  net `−1` sorry cycle; anything else is a regression and the
  supervisor will revert.
* **Do NOT poll or re-submit Aristotle batches** for `aux_515B_eta_contraction`.
  The cycle 103 batch is dead; the cycle 105 batch is now superseded
  by cycle 106's manual closures. The cycle-104 task results already
  identified Aristotle as "likely too hard" for the η-contraction;
  manual proof is the only path.
* **Do NOT generalize `M_pos` beyond `(h₀ * L) • A.map (|·|)`.**
  Stay scalar-real, Frobenius norm. The MMatrix.lean infrastructure
  is scoped exactly to this case.
* **Do NOT use `Matrix.PosSemidef`.** Wrong notion (spectral, not
  entrywise). The cycle 105 docstring documents this.
* **Do NOT use `Matrix.inv` / `Matrix.nonsing_inv`.** The Mathlib
  Neumann-series API uses `Ring.inverse`, and the comparison
  principle in `MMatrix.lean` accepts that form. Bridging to the
  determinant-based `Matrix.inv` is unnecessary churn.
* **Do NOT raise `maxHeartbeats`** above 200000. If Step 2's algebra
  is slow, factor out `aux_515B_target_identity` as suggested.
* **Do NOT freelance an alternate proof bypassing the comparison
  principle** (Picard iteration, ad-hoc induction on `s`, etc.).
  Cycle 106's strategy already enumerated dead ends; the comparison
  principle is the canonical M-matrix argument and exactly matches
  the deferred-issue-file's "Mathematical argument" block.
* **Do NOT pivot to `thm:515D`** this cycle. `thm:515D` is a
  multi-cycle target (per `entities/thm_515D.json`) and will get its
  own sorry-first scaffold cycle 108 once `lem:515B` is fully
  closed.
* **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer
  territory.
* **Do NOT modify `OpenMath/Chapter5/MMatrix.lean`** — cycle 106's
  infrastructure is the load-bearing dependency and must stay
  stable. If a missing lemma surfaces, add it as a NEW lemma at the
  bottom of the file, do not edit existing ones.

## Build commands (for reference)

```bash
# Verify Section515 still compiles (preferred during iteration):
lake env lean OpenMath/Chapter5/Section515.lean

# Update .olean cache (REQUIRED before #print axioms):
lake build OpenMath.Chapter5.Section515

# Final axiom check:
echo '#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStepError_bound' \
  | lake env lean --stdin /dev/stdin
```

## Success criteria

* **Minimum (score 0)**: Cycle 107 lands the signature change on
  `aux_515B_eta_contraction` and `localStepError_bound`, but
  Step 2 / Step 4 do not close. Sorry count stays at 1; net 0 cycle.
  This outcome is undesirable but acceptable if you discover a
  genuine Mathlib gap (file an issue immediately).
* **Good (score +1)**: `aux_515B_eta_contraction` closes; sorry
  count drops to 0; clean axioms; `localStepError_bound` updated
  with the new hypothesis; housekeeping done.
* **Excellent (score +2)**: All of "Good", plus `lem:515B` marked
  `[x]` in plan.md, lean_status.json updated, deferred-issue file
  updated to RESOLVED. This is the expected outcome.
* **Outstanding (score +3, very unlikely)**: All of "Excellent",
  plus a sorry-first scaffold for `thm:515D` opened with
  ≤2 sorries (well below the cycle 103 ceiling). Only attempt this
  if you finish Priority 1+2 with >2 hours remaining; if `thm:515D`
  scaffolding starts going wrong, ABORT and revert to "Excellent" —
  do NOT commit a half-finished `thm:515D` scaffold.

## Cycle-108 preview (so cycle 107 doesn't over-scope)

Cycle 108 opens `thm:515D` ("Stability and consistency imply
convergence", §515) with a sorry-first scaffold. This is the direct
downstream consumer of `lem:515B` and unblocks the entire §515
cluster. Per `entities/thm_515D.json`, expect 3–5 cycles of work
(the textbook proof composes `lem:515B`'s local-step bound with a
discrete-Grönwall argument, mirroring §406D's structure for LMMs).
Cycle 107's scope is strictly limited to closing `lem:515B` and the
housekeeping; do **not** preempt cycle 108 by sketching `thm:515D`
work this cycle.
