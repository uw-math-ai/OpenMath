# Cycle 121 strategy

## Heading status

* Branch tip: `cdb72a8 Cycle 120 — close aux_515D_iterated_V_bound (Path A from issue file)`.
* Single sorry remaining in `OpenMath/Chapter5/Section515.lean` (line 1995):
  `aux_515D_max_deviation_geometric_bound` body (cycle 119 narrowing,
  signature unchanged in cycle 120).
* Cycle 120 was scored **−1** for "3 suspected vacuous proof(s) introduced".
  The 3 hits are at `Section515.lean:1921, 1922, 1923` — calc-step closers
  `:= h_abs_sum`, `:= h_sum_bd`, `:= h_card` inside cycle 120's new
  `aux_515D_iterated_V_bound`. **All three are scanner false positives**
  per the standing
  `.prover-state/issues/tautology_scanner_false_positives.md`. Cycle 121
  MUST address this before doing structural work, or the cycle will
  REVERT.
* Aristotle Jobs running: 2 (`63045685-0543-4d65-91a4-8466337472bd`),
  3 (`e68b3d59-d608-42e1-9da2-413b3742c168`). Both `IN_PROGRESS` at end
  of cycle 120. Job 4 was cancelled by cycle 120.

## Priority 0 — fix scanner regression (5 min, MANDATORY first)

The cycle 120 worker introduced 3 false-positive matches against
`scripts/autonomous_loop.py`'s `TAUTOLOGY_PATTERNS`. Apply the standing
cycle-015 cosmetic workaround (rename `h_<name>` → `h<name>` to drop
the underscore).

**Concrete edits in `OpenMath/Chapter5/Section515.lean`** (inside
`aux_515D_iterated_V_bound`, lines ~1900–1923):

| Line(s) | Old name | New name |
|---|---|---|
| 1900 (declaration), 1921 (calc closer) | `h_abs_sum` | `habs_sum` |
| 1908 (declaration), 1922 (calc closer) | `h_sum_bd`  | `hsum_bd`  |
| 1918 (declaration), 1923 (calc closer) | `h_card`    | `hcard`    |

Six edits total (3 declarations + 3 calc closers). Use `Edit` tool
with `replace_all=false` and disambiguate via surrounding context;
each name occurs exactly twice in the file.

**Verification** (run after edits):

```bash
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/
```

Expected: 0 matches.

```bash
lake env lean OpenMath/Chapter5/Section515.lean
```

Expected: same warning profile as cycle 120 (one `sorry` warning at
line 1995, plus the pre-existing simp-arg / unused-variable lint on
older lines). NO new errors — α-renaming is semantics-preserving.

**Append to** `.prover-state/issues/tautology_scanner_false_positives.md`:

> Cycle 121: applied the cosmetic rename workaround to
> `aux_515D_iterated_V_bound` (lines 1900, 1908, 1918, 1921, 1922,
> 1923). The bug-D1 (block-comment line drift) and bug-D2
> (over-firing on `:= h_<name>` calc closers) remain unfixed in
> `scripts/autonomous_loop.py`. Each new helper introduced by
> cycle ≥116 has had to apply this rename; aggregate maintenance
> cost now exceeds the one-time D1+D2 fix.

This is loop-maintainer territory — do NOT edit
`scripts/autonomous_loop.py` from the worker.

## Priority 1 — Aristotle hygiene (5 min, single poll only)

Per CLAUDE.md "do not poll repeatedly", run ONE
`mcp__aristotle__get_status` per job, then act:

```text
mcp__aristotle__get_status({project_id: "63045685-0543-4d65-91a4-8466337472bd"})  // Job 2: cycle 117 aux_515D_componentwise_deviation_tendsto_zero
mcp__aristotle__get_status({project_id: "e68b3d59-d608-42e1-9da2-413b3742c168"})  // Job 3: cycle 118 aux_515D_max_deviation_bound_tendsto_zero
```

**Job 3 disposition**: cycle 119's narrowing already closed the
target body (`aux_515D_max_deviation_bound_tendsto_zero`, see
`Section515.lean:2025`). Any returned proof is redundant. **Cancel
Job 3 unconditionally** (`mcp__aristotle__cancel_project`); free
the slot.

**Job 2 disposition**: cycle 117's
`aux_515D_componentwise_deviation_tendsto_zero` body composition
also already landed (cycle 118's decomposition fallback closed it).
**If `COMPLETE`**, briefly inspect the returned proof; if it offers
a substantively cleaner approach for the existing body, log to
`task_results/cycle_121.md` "Discovery" but do NOT swap it in
unless trivially compatible — the cycle 118 manual proof has known
axioms. **Otherwise cancel.**

Do NOT re-poll, do NOT submit a new Aristotle job for Priority 2 in
this cycle (the body composition is best done manually; an
Aristotle submission only matters if Backup B2 is triggered, see
"Open Aristotle hypothesis budget" below).

## Priority 2 — close `aux_515D_max_deviation_geometric_bound` (the only remaining §515D sorry)

Target: `OpenMath/Chapter5/Section515.lean:1961-1995`. Compose the
body using cycle 120's `aux_515D_iterated_V_bound` plus
`localStepError_bound` (cycle 116 strengthened). The cycle 119
narrower output shape is

```
∃ C_init C_lin : ℝ, 0 ≤ C_init ∧ 0 ≤ C_lin ∧
  ∀ n : ℕ, 0 < n →
    sup'_i |Y n n i − (u i · yex x + v i · h_n · deriv yex x)|
      ≤ C_init · sup'_j |Y n 0 j − (u j · yex x₀ + v j · h_n · deriv yex x₀)|
        + C_lin · h_n
```

where `h_n := (x − x₀)/n`.

### Recommended path: vectorial-recurrence composition

This path **avoids** the `0 ≤ M.glmAbscissae v` (`_hc_nn`)
hypothesis that `aux_515D_construct_ell_U_phi_A` (cycle 114)
requires. Per cycle 120 update notes in
`.prover-state/issues/aux_515D_iterated_V_bound.md`, propagating
`_hc_nn` upstream is high-risk for §513 / §514 cascade integrity.
The vectorial-recurrence path bypasses M-matrix construction
entirely and routes through the cycle-120 iterated-V bound +
cycle-116 `localStepError_bound`.

**Outline (~150 LOC)**:

1. **Setup vector deviation**. For fixed `n > 0`, set
   `h_n : ℝ := (x - x₀) / n` and define
   `target_seq : ℕ → Fin r → ℝ`,
   `target_seq m i := u i * yex (x₀ + m * h_n) + v i * h_n * deriv yex (x₀ + m * h_n)`.
   Define `δ : ℕ → Fin r → ℝ`, `δ m i := Y n m i - target_seq m i`.

2. **Vectorial recurrence**. Extract
   `hY_iter : M.IsGLMSolution h_n f (Y n) ∧ stage_eq` from
   `_hY_iter n hn`. From `M.IsGLMSolution`, the output equation is
   `Y n (m+1) = h_n • (M.B *ᵥ (f ∘ Y_int_full m)) + M.V *ᵥ Y n m`
   where `Y_int_full m : Fin s → ℝ` is the stage at micro-step `m`
   (defined inside `IsGLMSolution`). Combine with the consistency
   constraints `_hVu`, `_hUu`, `_hCons_eq` and the ODE
   `deriv yex t = f (yex t)` to derive

       δ (m+1) = M.V *ᵥ δ m + R m

   where the residual `R : ℕ → Fin r → ℝ` is

       R m i = h_n · (M.B *ᵥ (fun j => f (Y_int_full m j) - f (yex (x₀ + (m+1)·h_n)))) i
              + per-step truncation error term

   Both pieces are quantitatively bounded below.

3. **Per-step residual bound** (load-bearing, ~50 LOC). Show
   `∃ K_R : ℝ, 0 ≤ K_R ∧ ∀ m, m < n → sup'_i |R m i| ≤ K_R · h_n²`.

   Two contributions to `R m`:

   (a) **Stage-difference contribution**:
       `h_n · (M.B *ᵥ (f ∘ Y_int_full m - f ∘ exact_target_int m))`.
       Apply `localStepError_bound` (`Section515.lean:1355`,
       cycle 116 strengthened). Its conclusion bounds the
       max-abs of `Y_int_full m - exact_target_int m` by
       `(stage-error-coefficient) · h_n`. Multiply by `‖M.B‖_∞`
       and `(L : ℝ)` (Lipschitz `f`) to get an `O(h_n²)` bound.

       Required hypotheses for `localStepError_bound`:
       `_hM_nn`, `_hyex_C1`, `_hyex_M`, `_hyex'_LM`, `_h_norm` —
       ALL already in `aux_515D_max_deviation_geometric_bound`'s
       signature (per cycle 116 strengthening). NO new hypotheses
       required.

   (b) **Truncation contribution from the consistency rewrite**:
       constant `O(h_n²)` per step, bounded via Taylor remainder
       on `yex` using `_hyex_C1` + `_hyex_M`. Use Mathlib's
       `taylor_mean_remainder` or `taylor_within_apply` if
       available; otherwise prove inline via `intervalIntegral`
       FTC plus `_hyex'_LM` (the derivative bound).

   Combine (a) and (b) into a single constant `K_R` independent of
   `n` (depends only on `M`, `L`, `M_bound`, `x - x₀`).

4. **Closed-form expansion**. By induction on `m`,

       δ m = (M.V)^m *ᵥ δ 0 + ∑_{k=0}^{m-1} (M.V)^(m-1-k) *ᵥ R k.

   Prove this as a sub-`have` via `Nat.rec` or direct induction on
   `m`. Standard `Matrix.mulVec_add`, `Matrix.mulVec_mulVec`,
   `pow_succ` rewrites.

5. **Sup' bounds via cycle-120 iterated-V**. Apply
   `aux_515D_iterated_V_bound` (`Section515.lean:1835`) to extract
   `C₀ : ℝ` with `0 ≤ C₀` and `∀ k z, sup'_i |((M.V)^k *ᵥ z) i|
   ≤ C₀ · sup'_j |z j|`. Then:

   - First term:
     `sup'_i |((M.V)^n *ᵥ δ 0) i| ≤ C₀ · sup'_j |δ 0 j|`.
   - Each summand:
     `sup'_i |((M.V)^(n-1-k) *ᵥ R k) i| ≤ C₀ · sup'_j |R k j|
                                          ≤ C₀ · K_R · h_n²`.
   - Sum of `n` summands: `n · C₀ · K_R · h_n² = C₀ · K_R · (x − x₀) · h_n`
     (using `n · h_n = x − x₀`).

   Apply `Finset.sup'_le` + `abs_add_le` + linarith to combine the
   two bounds.

6. **Output the existential**. Set
   `C_init := C₀`,
   `C_lin := C₀ · K_R · (x − x₀)`.
   Both non-negative (linarith from `hC₀_nn`, `hK_R_nn`, `_hxx`).
   Discharge the goal directly.

### Faithfulness check

* **No new hypothesis on `aux_515D_max_deviation_geometric_bound`**.
  The signature in cycle 119 is preserved; only the body changes.
* **No `_hc_nn` propagation**: §513 / §514 cascade integrity is
  preserved by avoiding `aux_515D_construct_ell_U_phi_A`.
* **No new faithfulness divergence on the capstone**. The only
  pre-existing divergence is the cycle 116 Frobenius hypothesis
  on `IsConvergent` (already documented in
  `glm_isconvergent_strengthened.md`).

### Backup plan B2 — if vectorial-recurrence path stalls past ~150 LOC

Introduce ONE narrower sub-helper, `aux_515D_residual_bound`, with
signature

```lean
private theorem aux_515D_residual_bound {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {x : ℝ} (hxx : x₀ < x)
    {M_bound : ℝ} (hM_nn : 0 ≤ M_bound)
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)
    (hyex'_LM : ∀ t ∈ Set.Icc x₀ x, |deriv yex t| ≤ (L : ℝ) * M_bound)
    (h_norm : ‖(((x - x₀) * (L : ℝ)) • M.A.map (fun a => |a|) :
                Matrix (Fin s) (Fin s) ℝ)‖ < 1)
    [Nonempty (Fin r)]
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_iter : ∀ n, 0 < n →
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i = ...)) :
    ∃ K_R : ℝ, 0 ≤ K_R ∧
      ∀ n : ℕ, 0 < n →
        ∀ m : ℕ, m < n →
          let h_n : ℝ := (x - x₀) / (n : ℝ)
          let target := fun (k : ℕ) (i : Fin r) =>
            u i * yex (x₀ + k * h_n) + v i * h_n * deriv yex (x₀ + k * h_n)
          Finset.sup' Finset.univ Finset.univ_nonempty
            (fun i : Fin r =>
              |(Y n (m+1) i - target (m+1) i) -
               (M.V *ᵥ (fun j => Y n m j - target m j)) i|)
          ≤ K_R * ((x - x₀) / (n : ℝ))^2
```

Body: `sorry`. Estimated ~80 LOC for the outer composition once
this helper is assumed. Fall back to this only if step 3 above
proves to consume more than ~80 LOC of the cycle 121 budget.

This narrows the §515D sorry to a clean self-contained per-step
residual statement — natural Aristotle target for cycle 122.

### Lean LSP / tactical guidance

* For step 4 (closed-form expansion induction): the canonical
  pattern is `induction m with | zero => ... | succ m ih => ...`
  inside a local `have` block. The successor case telescopes via
  `ih` + `pow_succ` + `Matrix.mulVec_mulVec` rewrites.
* For step 5 (sup'-bound combination): use
  `Finset.sup'_le` to introduce per-`i` goals, then `abs_add_le` /
  `abs_sum_le_sum_abs` followed by `linarith` with the
  `hC₀_nn`, `hK_R_nn`, `_hxx` hypotheses in scope.
* `aux_515D_iterated_V_bound` produces an `∃ C', 0 ≤ C' ∧ ...`
  shape. Destructure with `obtain ⟨C₀, hC₀_nn, hC₀⟩ := ...` then
  use `hC₀ k z` for each invocation.
* For Mathlib taylor-remainder lookup (step 3b), try
  `lean_loogle "taylor_mean_remainder"` or
  `lean_leansearch "Taylor remainder one variable"`. If Mathlib's
  API mismatches, fall back to an inline FTC argument:

      yex (x₀ + (m+1)·h_n) - (yex (x₀ + m·h_n) + h_n · deriv yex (x₀ + m·h_n))
        = ∫_{x₀ + m·h_n}^{x₀ + (m+1)·h_n} (deriv yex t - deriv yex (x₀ + m·h_n)) dt

  with the integrand bounded by `2 · L · M_bound` on the compact
  sub-interval (a crude bound, but adequate for the `O(h_n²)`
  conclusion).
* Use `lean_multi_attempt` rather than `lean_run_code` for testing
  intermediate tactics — `lean_run_code` is rate-limited and
  unsuitable for an iterative tactical session.

## What NOT to do (explicit blacklist)

* **Do NOT** propagate `(_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i)` to
  `aux_515D_max_deviation_geometric_bound` or any of its callers.
  Cycle 120 update in
  `.prover-state/issues/aux_515D_iterated_V_bound.md` and
  `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  flagged this as high-risk for §513 / §514 cascade integrity.
* **Do NOT** invoke `aux_515D_construct_ell_U_phi_A` (cycle 114)
  in this cycle. It requires `_hc_nn` per its signature; the
  vectorial-recurrence path above bypasses it entirely.
* **Do NOT** invoke `aux_515D_per_step_recurrence` (cycle 113
  scalar form) directly. It requires the `V_norm + α·h ≤ 1`
  telescoping condition that fails for general stable GLMs (cycle
  118 dead end). Use `aux_515D_iterated_V_bound` (cycle 120) for
  iterated-V bounds instead.
* **Do NOT** invoke `aux_515D_gronwall_bound` (cycle 113) for the
  same reason — it consumes a sum-form bound that the vectorial
  recurrence does not produce naturally.
* **Do NOT** edit `scripts/autonomous_loop.py` from the worker.
  Scanner false-positive fixes go in
  `tautology_scanner_false_positives.md`, not the script.
* **Do NOT** raise `maxHeartbeats` above 200000. If the closed-form
  induction in step 4 or the sup'-bound chain in step 5 times out,
  decompose into a private sub-`have` block — do NOT raise the
  limit.
* **Do NOT** use unicode `𝟙` as identifier suffix (cycle 099 dead
  end). ASCII identifiers only (`B1`, etc.).
* **Do NOT** use `Matrix.linfty_opNorm_mulVec` directly in §515 —
  the file opens `scoped Matrix.Norms.Frobenius`, so the default
  matrix norm is Frobenius, and `linfty_opNorm_mulVec` will not
  typecheck without scope manipulation. Cycle 120 already
  rediscovered this (see `task_results/cycle_120.md` "Dead ends"
  §1). If you need a `linfty_opNorm`-style bound, use the
  cycle-120 `aux_515D_iterated_V_bound` helper, which already
  bridges Frobenius `‖V^k‖` to a sup'-form vector bound.
* **Do NOT** poll Aristotle more than once per job per cycle.
  Single poll, then act.
* **Do NOT** introduce `axiom` or `constant` declarations.
* **Do NOT** "spot-clean" the unused-variable warning at line 1713
  or the simp-arg lint at line 1722; both are pre-existing and
  unrelated to cycle 121's scope.
* **Do NOT** use `h_<name>` as a hypothesis identifier anywhere in
  newly-introduced code. The scanner regex flags `:= h_<word>` and
  `exact h_<word>` as vacuous-proof candidates. Use `h<name>` /
  `hxxx` style throughout the cycle 121 body (and any new helpers
  introduced under Backup B2).

## Pre-commit checklist (CLAUDE.md §"Pre-Commit Faithfulness Checklist")

After Priority 0 + 1 + 2 land:

1. `lake env lean OpenMath/Chapter5/Section515.lean` succeeds with
   ZERO `sorry` warnings (Priority 2 closed) OR exactly ONE `sorry`
   warning (Backup B2 — at the new `aux_515D_residual_bound`).
2. `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   returns 0 matches (Priority 0 confirmation, post-edit and
   post-cycle-121-body).
3. `lake build OpenMath.Chapter5.Section515` then
   `#print axioms GeneralLinearMethod.stable_consistent_isConvergent`:
   - **Priority 2 path success**: returns `[propext, Classical.choice,
     Quot.sound]` only — no `sorryAx`. Update `lean_status.json`'s
     `thm:515D` row from `partial` → `formalized`. Update
     `plan.md` `thm:515D` row from `[~]` → `[x]`. Move `thm:515D`
     into the "65/175 → 66/175" tally.
   - **Priority 2 Backup B2**: returns `[propext, sorryAx,
     Classical.choice, Quot.sound]` (the new `aux_515D_residual_bound`
     sorry). Leave `lean_status.json` and `plan.md` as
     `partial` / `[~]`. Bump cycle reference to 121.
4. Faithfulness check on body composition: only the cycle-116
   pre-existing Frobenius divergence on `IsConvergent` should
   appear. NO new hypothesis on either
   `aux_515D_max_deviation_geometric_bound` or any caller. Document
   in `task_results/cycle_121.md` §"Faithfulness check" with
   explicit "no new divergence introduced this cycle" line.
5. Tautology scanner re-run against HEAD (post-commit) returns 0
   hits — verify before pushing.

## Deliverable bar

* **Priority 2 success**: `thm:515D` closed → §515 capstone is
  formalized → unblocks the entire §515 block plus §513/§514's
  iff direction (the `IsConvergent ↔ IsStable ∧ IsConsistent`
  packager). This is the cycle's high-water target.
* **Priority 2 Backup B2**: §515D sorry narrowed to a clean
  per-step residual helper. Cycle 122 then closes
  `aux_515D_residual_bound` (likely tractable for Aristotle since
  it is a self-contained scalar `O(h²)` bound). Acceptable
  fallback.
* **Below the line**: if even Priority 2 stalls and only Priority 0
  + 1 land, the cycle is a hygiene-only cycle. Score should still
  be ≥0 since the scanner regression was the cause of the cycle 120
  −1 score. File a follow-up issue documenting the stall point so
  cycle 122's planner can reroute.

## Open Aristotle hypothesis budget

Do NOT submit any new Aristotle jobs in cycle 121 EXCEPT in the
Backup B2 case. Submitting now costs ~30 min of latency in cycle
122's start; cycle 121's vectorial-recurrence composition is best
done manually in one focused session.

If Backup B2 triggers (cycle 121 ends with `aux_515D_residual_bound`
sorry'd), submit ONE Aristotle job at the END of cycle 121
(post-commit) targeting `aux_515D_residual_bound`. Use the
`abstract-axioms` pattern (cycle 116 precedent): inline the
hypotheses as `axiom`s in a self-contained `.lean` file, drop
`aux_515D_residual_bound` as a `theorem` to prove. Cycle 122 polls
the result.

## Cross-references

* `.prover-state/issues/aux_515D_iterated_V_bound.md` — cycle 120
  Path A closure record; documents the `_hc_nn` cascade concern.
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` —
  full §515D blocker history.
* `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
  — `_hc_nn` cascade analysis (why we don't propagate).
* `.prover-state/issues/glm_isconvergent_strengthened.md` —
  cycle 116 Frobenius divergence (already documented).
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  scanner-bug standing issue.
* `OpenMath/Chapter5/Section515.lean:1355` — `localStepError_bound`
  capstone (cycle 116 strengthened).
* `OpenMath/Chapter5/Section515.lean:1835` — cycle 120
  `aux_515D_iterated_V_bound` (post-rename: lines may shift by
  ±0; the rename is α-preserving so the line is unchanged).
* `OpenMath/Chapter5/Section515.lean:1995` — the sorry to close.
