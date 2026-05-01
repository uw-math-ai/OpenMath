# Strategy — Cycle 043

## Status entering this cycle

- `lem:406B` sub-lemmas A, B, C, D, E **all closed** (axiom-clean:
  `[propext, Classical.choice, Quot.sound]`).
- The single remaining `sorry` in the entire `OpenMath/` tree is the
  main theorem `LinearMultistepMethod.localTruncationError_bound` at
  `OpenMath/Chapter4/Section404.lean:882–896`. This is the terminal
  target for `lem:406B`.
- Aristotle project `53d674e4-20e3-43e8-9600-0b189c62c8f5` was last
  observed at 4% IN_PROGRESS at the close of cycle 042 (no progress
  since cycle 040). It is now several days old.

## Aristotle: poll ONCE then stop

At the very start of the cycle, run `mcp__aristotle__get_status`
**exactly once** for project `53d674e4-20e3-43e8-9600-0b189c62c8f5`.
Three branches:

1. **DONE / partial proofs returned for sub-lemmas A–E.** All five
   are already manually proved in the file. Do NOT replace any of
   them — the manual proofs are clean and well-tested. Just record
   what Aristotle returned in `task_results/cycle_043.md` for
   bookkeeping, then proceed.
2. **DONE / proof returned for the main `localTruncationError_bound`.**
   Use `mcp__aristotle__download_result` + `extract_result`. If the
   returned proof compiles and the axiom check is clean, use it
   directly (this is the cycle's primary target). If it is partial
   or fails, salvage what you can and proceed manually.
3. **Still IN_PROGRESS or FAILED.** Cancel the project via
   `mcp__aristotle__cancel_project` to free quota — it has had three
   full cycles and is clearly stuck. Then proceed manually below.

**Do NOT poll Aristotle a second time this cycle.** CLAUDE.md is
explicit: "one check after 30 min is enough". The project has had
its full window.

## Primary target: prove `localTruncationError_bound`

Goal at `OpenMath/Chapter4/Section404.lean:882`:

```lean
theorem LinearMultistepMethod.localTruncationError_bound {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M.localTruncationError y x h|
      ≤ ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2
```

### Ingredients already on hand

- `M.localTruncationError_decomposition hcons y x h` (sub-lemma E,
  line 792): rewrites `M.localTruncationError y x h` as
  `(α-sum) + h * (β-sum)` where the residuals are exactly the
  arguments of sub-lemmas C and D.
- `residual_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound i x h hh`
  (sub-lemma C, around line 559): bounds
  `|y x − y (x − i·h) − i·h · y'(x)| ≤ (1/2) · i² · h² · L · M`.
- `deriv_diff_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound i x h hh`
  (sub-lemma D, line 748): bounds
  `|y'(x) − y'(x − i·h)| ≤ i · h · L · M`.

### Decomposed proof plan

To avoid `maxHeartbeats` blowups in a single ring-style assembly,
**factor the proof into two helper lemmas plus the main combiner**.
The decomposition mirrors the cycle 040 consultant note §D.5 sketch.

**Helper 1 — α-sum bound** (place above the main theorem, in the
same namespace):

```lean
lemma localTruncationError_α_sum_bound {k : ℕ}
    (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |∑ i : Fin k, M.α i.succ
        * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
           - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x)|
      ≤ (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
        * ((1/2) * h^2 * L * M_bound) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [show (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          * ((1/2) * h^2 * L * M_bound)
        = ∑ i : Fin k,
            (((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
              * ((1/2) * h^2 * L * M_bound) from
        by rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  -- Goal: |M.α i.succ| * |residual| ≤ ((i+1)² * |M.α i.succ|) * ((1/2) * h² * L * M)
  have hC := residual_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound
               (i.val + 1) x h hh
  -- hC : |y x - y (x - ((i.val+1):ℝ)*h) - ((i.val+1):ℝ)*h*deriv y x|
  --        ≤ (1/2) * ((i.val+1):ℝ)² * h² * L * M_bound
  calc |M.α i.succ|
        * |y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
            - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x|
      ≤ |M.α i.succ|
          * ((1/2) * ((i.val + 1 : ℕ) : ℝ)^2 * h^2 * L * M_bound) :=
        mul_le_mul_of_nonneg_left hC (abs_nonneg _)
    _ = (((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          * ((1/2) * h^2 * L * M_bound) := by ring
```

**Caution on the `residual_bound` index.** Re-check `residual_bound`'s
signature at line ~559 with `lean_hover_info`: it takes the index as
a `(i : ℕ)` and produces the bound at the cast `(i : ℝ)`. The α-sum
residuals in sub-lemma E use `((i.val + 1 : ℕ) : ℝ)` (cast of
`i.val + 1`). So pass `(i.val + 1)` as the `ℕ`-argument; the
resulting real number will be exactly `((i.val + 1 : ℕ) : ℝ)`. If
the cast bridge complains anywhere, insert a `push_cast` rewrite
before the calc step (this is the standard MEMORY.md
`SatisfiesEq404b cast bridging` pattern).

**Helper 2 — β-sum bound**:

```lean
lemma localTruncationError_β_sum_bound {k : ℕ}
    (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |∑ i : Fin k, M.β i.succ
        * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))|
      ≤ (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * (h * L * M_bound) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [show (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
          * (h * L * M_bound)
        = ∑ i : Fin k,
            (((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|) * (h * L * M_bound) from
        by rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hD := deriv_diff_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound
               (i.val + 1) x h hh
  calc |M.β i.succ|
        * |deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)|
      ≤ |M.β i.succ| * (((i.val + 1 : ℕ) : ℝ) * h * L * M_bound) :=
        mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    _ = (((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|) * (h * L * M_bound) := by ring
```

**Main combiner**:

```lean
theorem LinearMultistepMethod.localTruncationError_bound ... := by
  rw [M.localTruncationError_decomposition hcons y x h]
  refine (abs_add _ _).trans ?_
  have hα := localTruncationError_α_sum_bound M hL hM hf_lip
               hy_C1 hy_ode hf_y_bound x h hh
  have hβ := localTruncationError_β_sum_bound M hL hM hf_lip
               hy_C1 hy_ode hf_y_bound x h hh
  -- hα : |α-sum| ≤ A * ((1/2) * h² * L * M)        where A = ∑ (i+1)² |α|
  -- hβ : |β-sum| ≤ B * (h * L * M)                 where B = ∑ (i+1) |β|
  -- Goal: |α-sum| + |h * β-sum| ≤ ((1/2)*A + B) * L * M * h²
  have habs_h : |h * (∑ i : Fin k, M.β i.succ
                  * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)))|
                = h * |∑ i : Fin k, M.β i.succ
                  * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))| := by
    rw [abs_mul, abs_of_nonneg hh]
  rw [habs_h]
  refine le_trans (add_le_add hα (mul_le_mul_of_nonneg_left hβ hh)) ?_
  -- Final algebra: A * ((1/2)*h²*L*M) + h * (B * (h*L*M))
  --              = ((1/2) * A + B) * L * M * h²
  apply le_of_eq
  ring
```

### Things that may go wrong, and how to handle them

1. **Cast bridge mismatch.** `residual_bound` /
   `deriv_diff_bound` produce expressions involving `(↑(i.val+1) : ℝ)`;
   sub-lemma E's decomposition emits `((i.val + 1 : ℕ) : ℝ)`. Usually
   definitionally equal, but if `mul_le_mul_of_nonneg_left` complains,
   insert a `have heq : ... = ... := by push_cast; ring` before the
   calc step, or `simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]`.
2. **`ring` does not close the final algebra.** Two sides are equal
   after normalisation (both expand to
   `(1/2)*A*L*M*h² + B*L*M*h²`). If `ring` chokes, distribute first
   via `Finset.sum_mul`/`Finset.mul_sum`, then `ring`.
3. **`abs_add` shape mismatch.** Should fire on `|α-sum + h * β-sum|`.
   If parenthesisation is off, use `abs_add _ _` with explicit
   placeholders.
4. **A single-step `ring` blowup** (>15s). Decompose further:
   pull the pure arithmetic step into a separate `final_assembly`
   helper proved by `ring`, then apply it. Do NOT bump
   `maxHeartbeats`.
5. **Strategy ceiling.** Per CLAUDE.md the cycle ceiling is "main
   theorem closed + faithfulness check"; this is exactly what we're
   doing. Do not branch into `thm:406C` / `thm:243A` even if the
   main theorem closes early — leave those for cycle 044 (but see
   stretch goal below for a sorry-first scaffold of `thm:406C`).

### Search budget

Use `lean_local_search`, `lean_loogle`, and `lean_hover_info`
liberally to verify lemma names and signatures (especially for
`Finset.abs_sum_le_sum_abs`, `Finset.sum_mul`, `Finset.sum_le_sum`,
`abs_mul`, `abs_add`, `mul_le_mul_of_nonneg_left`). Prefer local
search; the rate-limited `lean_state_search` /
`lean_hammer_premise` are unnecessary for this assembly cycle.

## Pre-commit checklist (MANDATORY)

Before committing, re-run the §404 file's faithfulness checks
against `extraction/formalization_data/entities/lem_406B.json`:

- [ ] **Tautology check.** The conclusion of
  `localTruncationError_bound` is an inequality with non-trivial
  RHS (the textbook bound, with the corrected coefficient list);
  no hypothesis contains this inequality. Clean.
- [ ] **Identity check.** The proof is a calc/le_trans chain through
  three lemmas, not a single `exact`. Clean.
- [ ] **Hypothesis strength check.** `ContDiff ℝ 1 y` is the
  pre-existing strengthening (already documented in the §406 block
  header and the cycle 041 task results). No new hypotheses
  introduced this cycle.
- [ ] **Definition smuggling check.** N/A — this is a theorem.
- [ ] **Faithfulness vs. textbook.** The bound coefficient is
  `(1/2 ∑ (i+1)² |α_{i+1}| + ∑ (i+1) |β_{i+1}|) L M h²`, **NOT**
  Butcher's stated `∑ i |i α_i − β_i|` form. The Lean docstring at
  line 879–881 already documents this divergence and points to
  `.prover-state/issues/lem_406B_textbook_check.md`. Verify the
  docstring is unchanged.
- [ ] `lake env lean OpenMath/Chapter4/Section404.lean` succeeds.
- [ ] `lake build OpenMath.Chapter4.Section404` succeeds (rebuild
  the `.olean` so `#print axioms` reports against current source —
  per cycle 042 discovery, `#print axioms` reads cached `.olean`).
- [ ] After rebuild, `#print axioms
  OpenMath.Chapter4.Section404.LinearMultistepMethod.localTruncationError_bound`
  shows `[propext, Classical.choice, Quot.sound]` ONLY (no `sorryAx`).
- [ ] Same axiom check for the two new helper lemmas.
- [ ] `extraction/formalization_data/lean_status.json`: bump
  `lem:406B` from `partial` to `formalized`, update `lean_file` and
  `notes` fields.
- [ ] Update `plan.md`: `[~] lem:406B` → `[x] lem:406B`, increment
  the progress count by 1 (`39 / 175` → `40 / 175`).
- [ ] Write `.prover-state/task_results/cycle_043.md` with the
  full faithfulness check, results, and suggested next approach
  (likely `thm:406C` next).

## Stretch goal (only if main theorem closes by ~midpoint of cycle)

If `localTruncationError_bound` closes cleanly with time remaining:

- Open `thm:406C` (Global error bound for linear multistep methods)
  via a sorry-first scaffold. Read
  `extraction/formalization_data/entities/thm_406C.json` for the
  textbook statement first. Do **not** attempt to close any of the
  scaffold's `sorry`s this cycle — leave them for cycle 044.
  Faithfulness check on the scaffold: confirm the structure /
  predicate matches the textbook before writing any proof body.
  Verify the scaffold compiles standalone with sorry's.

If the main theorem does **not** close:
- Commit whatever helper sub-lemmas did close (e.g.
  `localTruncationError_α_sum_bound` alone if the β version blocks).
  Reduce sorry count by however much you can. Document the blocker
  in a structured issue file at
  `.prover-state/issues/lem_406B_main_assembly_blocker.md` with
  specific details (which step failed, what the goal state was,
  what was tried).

## What NOT to try

- Do **NOT** poll Aristotle more than once. Per CLAUDE.md.
- Do **NOT** raise `maxHeartbeats` above 200000. If the final
  algebra step is slow, decompose into more helpers.
- Do **NOT** revert to Butcher's textbook coefficient
  `∑ i |i α_i − β_i|`. The β_i form has been independently
  verified twice (cycle 040 worker and cycle 040 consultant); the
  textbook has a typo. The current Lean RHS is correct.
- Do **NOT** introduce `axiom` / `constant` to bypass the cast
  bridge or the algebraic assembly. Use `push_cast` + `ring`.
- Do **NOT** modify or re-prove sub-lemmas A, B, C, D, E. They are
  axiom-clean and stable; they support the cycle's primary goal
  exactly as written.
- Do **NOT** weaken the hypotheses of `localTruncationError_bound`
  (e.g. dropping `ContDiff ℝ 1 y` for `Differentiable ℝ y`). The
  C¹ hypothesis is required by sub-lemma A's continuity-of-`f∘y`
  step, transitively by sub-lemmas B, C, D.
- Do **NOT** generalise to vector-valued `y : ℝ → ℝ^N`. Stay scalar.
  Cross-chapter generalisation is a separate cycle.
- Do **NOT** edit `scripts/autonomous_loop.py`. Per
  `.prover-state/issues/tautology_scanner_false_positives.md`,
  scanner bugs are loop-maintainer territory.
- Do **NOT** treat any "stuck on" / "commit not reaching repo" /
  "semantic sorry count increased" framing in the prompt at face
  value if it conflicts with the actual git state. Verify with
  `git log -1 --format='%H %s'` and
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
  per the cycle 040 consultant note §A.
- Do **NOT** spend more than ~10 minutes on the Aristotle status
  check. One call, decision tree, move on.
- Do **NOT** start `thm:243A` (the Ch.2 cross-chapter deferral) yet.
  It depends on `thm:406C` / `thm:406D` which are not closed.

## Reference: Mathlib lemmas (verify with `lean_local_search` before use)

| Goal | Lemma |
|---|---|
| `\|∑ a_i\| ≤ ∑ \|a_i\|` | `Finset.abs_sum_le_sum_abs` |
| Sum monotonicity | `Finset.sum_le_sum` |
| `(∑ a) * c = ∑ (a * c)` | `Finset.sum_mul` |
| `c * (∑ a) = ∑ (c * a)` | `Finset.mul_sum` |
| `\|a · b\| = \|a\| · \|b\|` | `abs_mul` |
| `\|a + b\| ≤ \|a\| + \|b\|` | `abs_add` |
| `\|a\| = a` for `a ≥ 0` | `abs_of_nonneg` |
| `0 ≤ a → b ≤ c → a*b ≤ a*c` | `mul_le_mul_of_nonneg_left` |
| `0 ≤ \|a\|` | `abs_nonneg` |
| Cast `((n+1 : ℕ) : ℝ) = (n:ℝ) + 1` | `push_cast` (tactic) |
| Equality from inequality after `ring` | `le_of_eq` then `ring` |

## Cross-references

- `.prover-state/issues/lem_406B_textbook_check.md` — Butcher typo
  diagnosis (β_i form vs. (iα_i − β_i) form).
- `.prover-state/issues/consultant_advice_cycle_040.md` §D.5 —
  consultant sketch of the main combiner (precursor to the plan
  above).
- `.prover-state/task_results/cycle_042.md` — sub-lemma B/C close
  details, including the `integral_id` namespace gotcha and the
  `.olean` cache lag warning.
- `extraction/formalization_data/entities/lem_406B.json` — textbook
  statement.
- `OpenMath/Chapter4/Section404.lean:516–870` — sub-lemmas A–E (all
  proved); :882–896 — the remaining `sorry` target.
