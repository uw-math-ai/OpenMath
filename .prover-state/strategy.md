# Cycle 056 Strategy — Integrate cycle-055 Aristotle results + add `b/c` Tendsto helpers

**Active target**: `thm:406D` — `LinearMultistepMethod.stable_consistent_isConvergent`
(line 2735 of `OpenMath/Chapter4/Section404.lean`, body `sorry` at line 2739).

**Phase**: outer-assembly helper construction. The autonomous closed-form
bound `globalError_closed_form_autonomous` (line 2686) is already proved.
The cycle-055 helpers `yPrime_sum_abs_tendsto_zero` (line 1886) and
`Cbase_tendsto_at_zero` (line 1982) are already in place. **Do NOT
attempt to close the main `sorry` at line 2739 this cycle** — it still
needs ~3–5 helper lemmas before the outer squeeze can land.

---

## Priority 1 — Integrate the 5 closed Aristotle proofs (MANDATORY first)

Cycle 055 submitted a batch of 5 forward-looking helpers and **all 5
returned closed proofs**, stored in
`.prover-state/aristotle_results/cycle_055/<name>_aristotle/<name>.lean`.
They were deliberately not integrated last cycle. Integrate them now,
each as a **`private` lemma** in `OpenMath/Chapter4/Section404.lean`.

### Where to place the new helpers

Insert the five new helpers **immediately after** the existing
`Cbase_tendsto_at_zero` at line 2008 (i.e. right before the
`recentSum_swap_bound` block at line 2024). Keep them as a contiguous
"§406D Tendsto helpers" cluster — a single comment header `-- §406D
outer-assembly Tendsto helpers (cycle 055 Aristotle batch)` is fine.

### Helpers to integrate (in this order)

1. **`Dbase_tendsto_at_zero`** — sibling of `Cbase_tendsto_at_zero`.
   The Aristotle proof uses `α β : Fin (k+1) → ℝ` parameters; **rewrite
   it to use `M : LinearMultistepMethod k`** to match the existing
   `Cbase_tendsto_at_zero` signature. The proof body the Aristotle run
   produced is:
   ```lean
   convert Filter.Tendsto.div ( tendsto_const_nhds )
     ( tendsto_const_nhds.sub ( Filter.Tendsto.mul
       ( Filter.tendsto_id.mul_const L ) tendsto_const_nhds ) ) _
     using 2 <;> norm_num
   ```
   That should still work after re-parameterisation since `M.α i.succ`
   and `M.β i.succ` behave the same way as the loose `α β` arguments.
   If `convert` is finicky, fall back to the long-form proof structure
   used in `Cbase_tendsto_at_zero` (line 1992–2008) — `set N := …`,
   prove `h_denom`, prove `h_num`, combine via `Tendsto.div`.

   Target signature (mirroring `Cbase_tendsto_at_zero`):
   ```lean
   private lemma Dbase_tendsto_at_zero
       {k : ℕ} (M : LinearMultistepMethod k) (L M_bound : ℝ) :
       Filter.Tendsto
         (fun h : ℝ =>
           ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
             + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
           * L * M_bound / (1 - h * L * |M.β 0|))
         (nhds 0)
         (nhds (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
                 + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
               * L * M_bound)) := by
     …
   ```

2. **`tendsto_const_div_one_sub_mul`** — generic `c / (1 - h · a) → c`.
   Copy as-is (no parameter changes). Aristotle proof:
   ```lean
   exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub
     ( Filter.tendsto_id.mul tendsto_const_nhds ) ) ( by norm_num ) )
     ( by norm_num )
   ```
   **Sanity-check this compiles** — `le_trans` here looks suspicious
   for a `Filter.Tendsto` goal; if it fails, replace with a direct
   `Tendsto.div tendsto_const_nhds h_denom (by norm_num)` plus a
   `simpa` to reduce `c / 1 = c`. Concretely:
   ```lean
   have h_denom : Filter.Tendsto (fun h : ℝ => 1 - h * a) (nhds 0) (nhds 1) := by
     have := (tendsto_const_nhds.sub (Filter.tendsto_id.mul tendsto_const_nhds)
       : Filter.Tendsto (fun h : ℝ => 1 - h * a) (nhds 0) (nhds (1 - 0 * a)))
     simpa using this
   simpa using (tendsto_const_nhds (x := c)).div h_denom (by norm_num)
   ```

3. **`tendsto_h_squared_zero`** — `h^2 → 0`. Copy as-is:
   ```lean
   exact Continuous.tendsto' (continuous_pow 2) _ _ (by norm_num)
   ```

4. **`tendsto_finset_sum_abs_zero`** — `Σ |f h i| → 0` if each
   `f h i → 0`. Copy as-is:
   ```lean
   simpa using tendsto_finset_sum _ fun i hi => Filter.Tendsto.abs (hf i hi)
   ```
   Note: the precondition is per-component `f h i → 0`, not
   `|f h i| → 0`. The `Tendsto.abs` lift gives `|f h i| → |0| = 0`,
   so the `simpa` reduces `|0|` to `0` and `∑ _, 0 = 0`.

5. **`tendsto_real_exp_at`** — `Real.exp` continuous at any point.
   Copy as-is:
   ```lean
   exact Real.continuous_exp.tendsto c
   ```

### Verification after integration

* `lake env lean OpenMath/Chapter4/Section404.lean` — must compile clean.
* `#print axioms Dbase_tendsto_at_zero` etc. (add a temporary
  in-file probe; remove before commit, since the helpers are
  `private` and probes from other files cannot reach them).
  Each must be `[propext, Classical.choice, Quot.sound]`.
* `lake build OpenMath.Chapter4.Section404` — must succeed.

---

## Priority 2 — Add 2 new derived helpers needed for the squeeze

After Priority 1, build these on top of the now-integrated Aristotle
helpers. Place them **after** the cycle-055 batch (i.e. after the
new `tendsto_real_exp_at`) but before `recentSum_swap_bound`.

### Helper P2.1 — `b_tendsto_at_zero` (the `b` constant in `globalError_recurrence_form`)

Recall `b = (Θ + 1) * Cbase + 1` from line 2292. As `h → 0`,
`Cbase → L * (|β 0| · Σ|α(i+1)| + Σ|β(i+1)|)` (call this `Cbase∞`)
by the cycle-055 `Cbase_tendsto_at_zero`. So
`b → (Θ + 1) * Cbase∞ + 1`.

Target signature:
```lean
private lemma b_tendsto_at_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L : ℝ) :
    Filter.Tendsto
      (fun h : ℝ =>
        (Θ + 1) *
          (L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L * |M.β 0|))
        + 1)
      (nhds 0)
      (nhds ((Θ + 1) *
              (L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                    + ∑ i : Fin k, |M.β i.succ|))
            + 1)) := by
  exact ((Cbase_tendsto_at_zero M L).const_mul (Θ + 1)).add_const 1
```

(`Tendsto.const_mul` and `Tendsto.add_const` are the relevant Mathlib
combinators — verify exact names with `lean_local_search` if they fail.
If `add_const` doesn't exist, use `.add tendsto_const_nhds` and
`simpa` to reduce.)

### Helper P2.2 — `c_tendsto_at_zero` (the `c` constant)

Recall `c = (Θ + 1) * Dbase` from line 2293. By
`Dbase_tendsto_at_zero` (Priority 1.1) plus `Tendsto.const_mul`:

```lean
private lemma c_tendsto_at_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L M_bound : ℝ) :
    Filter.Tendsto
      (fun h : ℝ =>
        (Θ + 1) *
          (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
              + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
            * L * M_bound / (1 - h * L * |M.β 0|)))
      (nhds 0)
      (nhds ((Θ + 1) *
              (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
                  + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
                * L * M_bound))) := by
  exact (Dbase_tendsto_at_zero M L M_bound).const_mul (Θ + 1)
```

---

## Priority 3 (stretch only) — One more derived helper if Priority 1+2 land cleanly

Only attempt this if Priority 1 + 2 finish in the first ~45 minutes
of the cycle and `lake build` is clean.

### Helper P3.1 — `c_h_h_squared_tendsto_zero`

The bound `c · h² · n` appears in `globalError_closed_form_autonomous`'s
exponential factor expansion (the `c · h / (b · k)` term inside the
`(exp(b · k · n · h) − 1)` factor; multiplied by `n` it becomes
`c · h² · n / (b · k)` after rearranging). For the squeeze, we
need the *individual* shape `c_h * h² → 0` (with the `n` factor
handled separately by `m · h_m = x − x₀` constancy).

Target signature:
```lean
private lemma c_h_h_squared_tendsto_zero
    {k : ℕ} (M : LinearMultistepMethod k) (Θ L M_bound : ℝ) :
    Filter.Tendsto
      (fun h : ℝ =>
        ((Θ + 1) *
          (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
              + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
            * L * M_bound / (1 - h * L * |M.β 0|)))
        * h^2)
      (nhds 0) (nhds 0) := by
  have h1 := c_tendsto_at_zero M Θ L M_bound
  have h2 : Filter.Tendsto (fun h : ℝ => h^2) (nhds 0) (nhds 0) :=
    tendsto_h_squared_zero
  have hmul := h1.mul h2  -- product Tendsto, target = c∞ * 0 = 0
  simpa using hmul
```

If this works, it slots cleanly into the cycle 057+ squeeze argument.

---

## DO NOT attempt this cycle

* **DO NOT** try to close the main `sorry` at line 2739
  (`stable_consistent_isConvergent`). The squeeze argument requires
  a full chain of `m · h_m = x − x₀` constancy plus `exp(b · k · m · h_m)`
  uniform bound plus `a_m → 0` lifted through the `IsConvergent`
  predicate's structure. This is at least 2–3 more cycles of helper
  work; cycle 056 is purely about adding the next layer of helpers.

* **DO NOT** introduce any closer matching `:= h_<name>` or
  `exact h_<name>` (regex patterns the loop's tautology scanner flags
  as "vacuous"). The scanner has known false positives — see
  `.prover-state/issues/tautology_scanner_false_positives.md`. Use
  `hinner`, `hresult`, `hclose`, `hmul` (no underscore prefix),
  `convert ... using N`, or inline the proof. **Any new `h_<name>`
  closer will cause cycle 056 to be scored −2 even if all the math
  is correct** — this happened in cycles 053, 054, and 055.

* **DO NOT** refactor the cycle-053 `globalError_recurrence_form`
  (line 2236) or cycle-053 `globalError_closed_form_autonomous`
  (line 2686). They are stable; touching them risks cascading
  failures.

* **DO NOT** generalise the autonomous helpers to non-autonomous
  `f : ℝ → ℝ → ℝ` this cycle. That is the cycle 057+ job, after the
  autonomous Tendsto theorem lands.

* **DO NOT** raise `maxHeartbeats` above 200000.

* **DO NOT** introduce any new `axiom` or `constant`.

* **DO NOT** modify `scripts/autonomous_loop.py` or any
  `.prover-state/` file outside `task_results/cycle_056.md` and
  `aristotle_submissions/cycle_056/` (if you submit anything new).

* **DO NOT** repeat the cycle-053/054/055 mistake of leaving a
  `sorry`-bodied stub theorem in the file just to advance scaffolding;
  if you cannot close a helper this cycle, **do not include it at
  all** — the sorry count must stay at exactly 1 (the line-2739
  stub).

---

## Aristotle this cycle

**Optional**. The cycle-055 Aristotle batch closed all 5 jobs. Cycle
056's main work is integration (mechanical), so a fresh batch is not
required. If Priority 1 + 2 land in under 30 minutes, optionally
batch-submit the following 3 forward-looking helpers for cycle 057+:

1. **`m_h_constancy`** — for the discrete step parameter, `(m : ℝ) · h_m = x − x₀`
   when `h_m := (x − x₀)/m` and `m > 0`. Pure arithmetic; should
   close trivially with `field_simp` / `linarith`.
2. **`exp_b_k_m_h_bounded`** — `Real.exp(b_h · k · m · h_m)` is bounded
   uniformly in `m` for `h` near 0, given that `b_h → b∞` and
   `m · h_m = x − x₀` (constant). This is the closed-form's
   exponential-factor stability lemma.
3. **`a_m_tendsto_zero`** — `a_m := (Θ + (Θ + 1) · Cbase · h · k + 1) · y'sum_m → 0`
   (combines `yPrime_sum_abs_tendsto_zero` with `Cbase_tendsto_at_zero`).

If Aristotle is busy or you don't have time to write the submission
files cleanly, **skip the batch** — the cycle-056 deliverable is
already substantial.

If you do submit, place files in
`.prover-state/aristotle_submissions/cycle_056/<name>.lean`, record
project IDs in `project_ids.txt`, then **do NOT poll Aristotle this
cycle**. Cycle 057 will check status once.

---

## Pre-commit checklist (MANDATORY before commit)

In addition to the standard CLAUDE.md "Pre-Commit Faithfulness
Checklist":

- [ ] All 5 Aristotle helpers integrated as `private lemma`s.
- [ ] Both Priority-2 helpers `b_tendsto_at_zero` and `c_tendsto_at_zero`
      land.
- [ ] `lake env lean OpenMath/Chapter4/Section404.lean` clean.
- [ ] `lake build OpenMath.Chapter4.Section404` succeeds.
- [ ] **Sorry count check**: count of `^[ ]*sorry$` lines in
      `OpenMath/Chapter4/Section404.lean` is still **1** (the line-2739
      stub). It must NOT increase. Run:
      `grep -nE '^[[:space:]]*sorry[[:space:]]*$' OpenMath/Chapter4/Section404.lean`
      and confirm exactly one hit.
- [ ] **Tautology scanner check**: run
      `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`.
      Output must be **empty**. If any line matches, rename the
      offending hypothesis (drop the underscore: `h_x → hx`) before
      committing — see the cycle-014 / cycle-015 consultant precedent.
- [ ] Push to remote (`git push`) and verify
      `git rev-parse HEAD == git rev-parse origin/Main/Experiments`.
      The cycle-008/035/052 phantom commit-not-reaching-repo failures
      should be checked against actual `git log` state.

---

## What to write in `task_results/cycle_056.md`

Standard CLAUDE.md template plus, in the **Faithfulness check**
section, an explicit note that none of the new helpers are
top-level Butcher entities — they are private analytic infrastructure
toward `thm:406D`. Confirm in the **Result** section that:

* sorry count: 1 → 1 (unchanged; the stub at 2739 stays).
* axiom check on every new helper: clean.
* the 5 Aristotle proofs landed (with adapted parameters where noted).

In the **Suggested next approach** section, set up cycle 057's
target as the `m_h_constancy` + `exp_b_k_m_h_bounded` + `a_m_tendsto_zero`
chain (whether or not those were submitted to Aristotle this cycle).

---

## Cross-references

* `.prover-state/aristotle_results/cycle_055/` — the 5 closed proofs
  to integrate this cycle.
* `.prover-state/aristotle_submissions/cycle_055/Dbase_tendsto_at_zero.lean`
  — the Aristotle submission file using `α β : Fin (k+1) → ℝ`
  parameters; remember to re-parameterise to `M : LinearMultistepMethod k`.
* `OpenMath/Chapter4/Section404.lean:1982–2008` — the
  `Cbase_tendsto_at_zero` template to mirror for `Dbase_tendsto_at_zero`.
* `OpenMath/Chapter4/Section404.lean:2236–2304` — the
  `globalError_recurrence_form` `set` block, which fixes the canonical
  spellings of `Cbase`, `Dbase`, `b`, `c` you must match in the new
  helpers.
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  standing scanner-bug issue; explains the `h_<name>` rename
  workaround.
* `.prover-state/task_results/cycle_055.md` — the cycle-055 result
  document, especially the "Suggested next approach" section which
  outlines the multi-cycle plan toward `stable_consistent_isConvergent`.
