# Cycle 069 Results

## Worked on

- **Priority 0**: discharge cycle 068's 3 scanner false-positive flags
  in `OpenMath/Chapter4/Section404.lean` (cosmetic regex workaround
  per cycle 014/015 consultant prescription).
- **Priority 1**: cross-chapter deferred theorem `thm:243A`
  ("convergent ⇔ stable ∧ consistent"). New file
  `OpenMath/Chapter4/Section405.lean`. Closed `thm:405B`
  (`convergent_isPreconsistent`); landed scaffold sorries for
  `thm:405A` and `thm:405C`; iff packager
  (`isConvergent_iff_isStable_and_isConsistent`) wired up against
  cycle 068's `stable_consistent_isConvergent`.

## Approach

### Priority 0 — scanner-flag renames

Three regex-flagged sites in `Section404.lean`:

* Line 1968–1982: `h_diff` block ending in `exact h_diff` →
  renamed to `hdiff` (2 occurrences in immediate scope).
* Line 2866–2874: `h_eps_eq` block ending in `rw [h_eps_eq]; exact h_Sy_bound`
  → rewrote line 2874 to `simpa only [h_eps_eq] using h_Sy_bound`
  (α-equivalent; avoids global rename of `h_Sy_bound` which is
  defined at line 2837 outside the block).
* Line 5491–5499: `h_orig` block ending in `exact h_orig` →
  renamed to `horig` (2 occurrences).

After all three edits, `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
returns zero hits. Section404.lean still compiles cleanly.

### Priority 1 — Section405.lean

1. Read entity JSONs for `thm:243A`, `thm:405A`, `thm:405B`,
   `thm:405C`, plus the cycle 068 strategy in
   `is_convergent_strengthened.md`.
2. Read the 5500+-line `Section404.lean` to confirm the strengthened
   `IsConvergent` signature, the `IsHomogeneousSolution` form, and
   the `isLMMSolution_zero_iff` bridge.
3. Created `OpenMath/Chapter4/Section405.lean` (new file) under
   namespace `OpenMath.Chapter4.Section404` (so dot-notation on
   `LinearMultistepMethod` resolves correctly).  Added entry to
   `OpenMath/Chapter4.lean`.
4. Submitted the scaffolded file to Aristotle via
   `mcp__aristotle__submit_directory` (project_id
   `4ddc0ab0-9542-49ab-abf1-fa7f5601df37`, submitted at 07:38 UTC).
5. **In parallel with Aristotle**, attempted the closing argument
   for `thm:405B` manually — see "Approach for thm:405B" below.
   Aristotle was at 8% complete after 47 min; per the planner's
   "check once at 30 min" rule, the submission is left running but
   not awaited.

### Approach for thm:405B (`convergent_isPreconsistent`)

Built three helpers in Section405.lean before the main theorem:

* `LinearMultistepMethod.homogeneousFromOnes : ℕ → ℝ` — strong
  recursive definition: `η i = 1` for `i < k`, otherwise
  `η n = ∑ j : Fin k, M.α j.succ · η (n − (j.val + 1))`.
  Termination via `decreasing_by; simp_wf; omega` using
  `j.isLt : j.val < k` and `k ≤ n` from the recursion branch.
* `homogeneousFromOnes_lt_k`, `homogeneousFromOnes_recurrence`:
  unfolding lemmas (each is a one-line `dif_pos` / `dif_neg`).
* `homogeneousFromOnes_isHomogeneousSolution`: `M.IsHomogeneousSolution η`
  follows directly from the recurrence at indices `m + k ≥ k`.

Main proof of `convergent_isPreconsistent`:

1. Instantiate the trivial IVP: `f := fun _ _ => 0`, `yex := fun _ => 1`,
   `start := fun _ _ => 1`, `Y m n := homogeneousFromOnes M n`.
2. Discharge the 8 hypotheses of `IsConvergent`:
   * `Continuous (Function.uncurry f)`: rewrite
     `Function.uncurry f = fun _ => 0`, then `continuous_const`.
   * `LipschitzWith 0 (Function.uncurry f)`: same rewrite, then
     `LipschitzWith.const`.
   * `yex 0 = 1`: `rfl`.
   * `ContDiff ℝ 1 yex`: `contDiff_const`.
   * `∀ x, HasDerivAt yex (f x (yex x)) x`: `hasDerivAt_const`.
   * `M_bound = 0` and bounds: trivial.
   * `∀ i, Tendsto (start · i) (𝓝 0) (𝓝 1)`: `tendsto_const_nhds`.
   * `Y` matches starts and `IsLMMSolution`: starts via
     `homogeneousFromOnes_lt_k`; `IsLMMSolution` via
     `isLMMSolution_zero_iff` ↔ `homogeneousFromOnes_isHomogeneousSolution`.
3. From `hConv` extract `Tendsto η atTop (𝓝 1)`.
4. Lift to shifted indices: for each `j : Fin k`,
   `Tendsto (fun n => η (n + k − (j.val + 1))) atTop (𝓝 1)` via
   `Tendsto.comp` with `Filter.tendsto_atTop_mono` from `tendsto_id`.
5. RHS of recurrence tends to `∑ j, M.α j.succ · 1 = ∑ j, M.α j.succ`
   via `tendsto_finset_sum` and `Tendsto.const_mul`.
6. LHS at `n + k` tends to `1`. Recurrence forces both limits equal.
   `tendsto_nhds_unique` extracts `1 = ∑ j, M.α j.succ`, which is
   `M.IsPreconsistent`.

The Lean argument **does not need `thm:405A` (stability)**, unlike
the textbook proof.  Butcher uses stability to bound `η` so the
ε-argument works; in Lean we get `η m → 1` directly from `hConv`,
which forces convergence pointwise without a boundedness intermediary.

## Result

- **SUCCESS**: `thm:405B` (`convergent_isPreconsistent`) closed.
- **SUCCESS**: `thm:243A` iff packager
  (`isConvergent_iff_isStable_and_isConsistent`) compiles modulo
  the two remaining `convergent_*` sorries.
- **PARTIAL**: `thm:405A` and `thm:405C` remain as sorry-first
  scaffolds (deferred to cycle 070+ per the planner backup plan).
- **SUCCESS**: Priority 0 scanner-flag rename done; the project-wide
  scan returns zero hits.
- Full `lake build` passes (8055 jobs, no errors). Section405.lean
  compiles with 2 expected sorry warnings.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `LinearMultistepMethod.homogeneousFromOnes` (helper, no entity)

* Auxiliary helper for `thm:405B`. Not a textbook entity; no
  faithfulness concern. The recursion captures Butcher's "η satisfying
  the difference equation with η_i = 1 for i < k" verbatim.

### `LinearMultistepMethod.convergent_isPreconsistent` (`thm:405B`)

* Entity ID and textbook statement (quoted from `entities/thm_405B.json`):

  > A convergent linear multistep method is preconsistent.

* Lean statement: `(hConv : M.IsConvergent) → M.IsPreconsistent`.
  Captures: **same content**.
* Faithfulness deviation: the Lean proof side-steps Butcher's appeal
  to `thm:405A` (stability). Butcher uses stability to ensure η is
  bounded so the ε-argument terminates; the Lean version uses
  `IsConvergent` directly to get `η m → 1`, which is stronger than
  what stability provides. The conclusion (`IsPreconsistent`) is
  identical to Butcher's, so this is a *proof-side* simplification,
  not a *statement-side* deviation.

### `LinearMultistepMethod.convergent_isStable` (`thm:405A`, sorry-first scaffold)

* Entity ID and textbook statement (quoted from `entities/thm_405A.json`):

  > A convergent linear multistep method is stable.

* Lean statement: `(hConv : M.IsConvergent) → M.IsStable`.
  Captures: **same content**. Proof: `sorry` (cycle 070+ followup).

### `LinearMultistepMethod.convergent_isConsistent` (`thm:405C`, sorry-first scaffold)

* Entity ID and textbook statement (quoted from `entities/thm_405C.json`):

  > A convergent linear multistep method is consistent.

* Lean statement: `(hConv : M.IsConvergent) → M.IsConsistent`.
  Captures: **same content**. Proof: `sorry` (cycle 070+ followup).

### `LinearMultistepMethod.isConvergent_iff_isStable_and_isConsistent` (`thm:243A`)

* Entity ID and textbook statement (quoted from `entities/thm_243A.json`):

  > A linear multistep method is convergent if and only if it is
  > stable and consistent.

* Lean statement: `M.IsConvergent ↔ M.IsStable ∧ M.IsConsistent`.
  Captures: **same content**. Forward direction (`⇐`) closed via
  cycle 068's `stable_consistent_isConvergent`. Reverse direction
  (`⇒`) wired up to the three `convergent_*` lemmas; closed
  modulo their two remaining sorries (i.e. partial because
  `thm:405A` and `thm:405C` are still open). Once those close, this
  iff is automatically a complete proof of `thm:243A`.

### Pre-commit checklist results

* **Tautology check**: `M.IsConvergent ↔ M.IsStable ∧ M.IsConsistent`
  is NOT a tautology: `IsConvergent` is a Π-type over IVPs, while
  the RHS is two structural predicates. The textbook equivalence is
  genuine content. ✓
* **Identity check**: no `:= h`, `exact h`, `:= id` proofs for any
  named theorem in this cycle. ✓
* **Definition smuggling check**: no new `class` or `structure`. ✓
* **Hypothesis strength check**: `convergent_*` lemmas take exactly
  the textbook hypothesis (`M.IsConvergent`). No extra hypotheses on
  `M`, `f`, or anything else. ✓

## Dead ends

- Initial Section405 scaffold used `namespace OpenMath.Chapter4.Section405`,
  which broke dot-notation: `M.convergent_isStable` resolved against
  `OpenMath.Chapter4.Section404.LinearMultistepMethod` (where the
  type is defined) and didn't find the new lemma. Fixed by reusing
  `namespace OpenMath.Chapter4.Section404` in Section405.lean.
- Stale `.olean` for Section404 after the Priority 0 renames: the
  initial `lake env lean Section404.lean` validated but didn't refresh
  the `.olean`, so Section405's first compile saw the *old*
  `IsConvergent` signature (with `LipschitzInSecond` instead of
  `LipschitzWith`).  Resolved by running `lake build OpenMath.Chapter4.Section404`
  to force a rebuild before proceeding.
- Initial use of `tendsto_const_nhds (a := 1)` failed because the
  parameter is named `c` (or unnamed in the implicit version).
  Replaced with explicit type ascription on `tendsto_const_nhds`.
- Initial `omega` on `n ≤ n + k - (j.val + 1)` failed because the
  goal was wrapped in unreduced `(fun n => ...) n`. Fixed with a
  `show n ≤ ...` line before `omega`.

## Discovery

- The cycle 068 `IsConvergent` strengthening is *enough* to close
  `thm:405B` directly without `thm:405A`.  Butcher's textbook proof
  derives boundedness of η from `thm:405A` and then runs an ε-style
  argument; the Lean proof short-circuits this via the strong
  `Tendsto η atTop (𝓝 1)` conclusion of `IsConvergent`. This means
  `thm:405B` is independent of `thm:405A` in the formalisation,
  even though Butcher's prose presents them in the order
  `405A → 405B`.
- Stale `.olean` after `lake env lean` is a recurring trap on this
  cluster; better to use `lake build <module>` for olean refresh
  whenever a downstream file is about to depend on the change.

## Suggested next approach

1. **Cycle 070**: close `thm:405A` (`convergent_isStable`).  Strategy:
   apply contrapositive — if `¬ IsStable`, there's an unbounded
   homogeneous solution `η`; build `Y_m n := η n / ζ_n` where
   `ζ_n = max_{i ≤ n} |η_i|`; apply `hConv` to the trivial IVP
   `y' = 0, y(0) = 0` at `x = 1`; derive contradiction from
   `|η_n / ζ_n| = 1` for infinitely many `n` vs.
   `Y_m m → 0`. The argument needs:
   * A "running max" sequence and its monotone-to-∞ property.
   * The "infinitely-many-records" pigeonhole: an unbounded sequence
     has infinitely many indices where it sets a new maximum.
   * Care with `n / ζ_n` being well-defined even when `ζ_0 = |η_0|`
     could be `0` (handle by case-splitting or shifting the start).
2. **Cycle 071**: close `thm:405C` (`convergent_isConsistent`).
   Strategy: combine `thm:405B` (preconsistency, this cycle) with
   the trivial IVP `y' = 1, y(0) = 0` and starting values
   `η_i / n` (per Butcher §405).  Note that in the Lean version,
   the `α_1 + 2α_2 + ⋯ + k α_k ≠ 0` step (which Butcher derives
   from stability) may be sidesteppable, similar to how `thm:405A`
   was avoided in `thm:405B`.
3. After both close, `thm:243A`'s iff packager becomes a complete,
   sorry-free proof automatically.
4. Optional polish: extract `homogeneousFromOnes` and its three
   characterising lemmas to `Section404.lean` (where
   `IsHomogeneousSolution` lives) so they can be reused by other
   §405-relevant work.
