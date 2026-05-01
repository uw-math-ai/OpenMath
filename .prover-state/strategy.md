# Strategy — Cycle 049

## Snapshot

* Sorry count: **1** — `OpenMath/Chapter4/Section404.lean:1823`
  (`thm:406D` scaffold, `LinearMultistepMethod.stable_consistent_isConvergent`).
* Last cycle: 048 closed `sum_theta_psi_contraction` (the Σ θψ
  contraction inequality). +1 axiom-clean lemma, sorry count
  unchanged at 1.
* Aristotle: **none pending**. Do not poll Aristotle this cycle —
  none of the lemmas below are large or high-leverage enough to
  justify a 30-minute submission/wait window. Manual proofs are
  ~30 lines each, well-suited to direct work.
* Cycle 047 trap reminder: `discrete_gronwall_exp_bound` was
  authored cycle 046 but committed only in cycle 047 because the
  cycle-046 commit landed without it. **Always run
  `git diff HEAD~1 HEAD -- OpenMath/` and `lake build` after
  committing this cycle**, before treating the cycle as complete.

## Primary deliverable: `starting_error_each_tendsto_zero` (φ(h) → 0, per index)

This is the cycle-048 task-result's "Cycle 049" target. It is a
pure `Filter.Tendsto` analysis with **no LMM-specific content**.
The goal is a helper lemma that the cycle-050 outer assembly will
consume to drive the limit through `discrete_gronwall_exp_bound`'s
exponential bound.

### Placement

Place the new lemma immediately after `sum_theta_psi_contraction`
(currently ends at line 1795) and immediately before the docstring
for `LinearMultistepMethod.stable_consistent_isConvergent`
(currently begins at line 1797). Both `sum_theta_psi_contraction`
and the new lemma are private helpers used only by `thm:406D`'s
scaffold; group them together.

### Lean signature (draft)

```lean
/-- **Butcher §406D's φ(h) → 0 helper, per index.**
For each `i : Fin k`, the per-index "starting error"
`|yex(x₀ + i·h) - start h i|` tends to 0 as `h → 0`.

Proof: continuity of `yex` at `x₀` (from differentiability) plus
the starting-method limit hypothesis (`start h i → y₀`). Compose
with `Filter.Tendsto.sub` and `Filter.Tendsto.abs`.

Used by: cycle 050's outer-assembly proof of `thm:406D`. -/
private lemma starting_error_each_tendsto_zero
    {k : ℕ} {f : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hy0 : yex x₀ = y₀)
    (hyex_diff : ∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) :
    ∀ i : Fin k,
      Filter.Tendsto
        (fun h : ℝ => |yex (x₀ + (i.val : ℝ) * h) - start h i|)
        (nhds 0) (nhds 0) := by
  intro i
  -- Step 1: yex is continuous at x₀ (from HasDerivAt at x₀, since x₀ ≥ x₀).
  have hyex_cont_x₀ : ContinuousAt yex x₀ :=
    (hyex_diff x₀ le_rfl).continuousAt
  -- Step 2: the curve h ↦ x₀ + i·h is continuous and sends 0 ↦ x₀.
  have h_curve : Filter.Tendsto (fun h : ℝ => x₀ + (i.val : ℝ) * h)
                                 (nhds 0) (nhds x₀) := by
    have h0 : Filter.Tendsto (fun h : ℝ => x₀ + (i.val : ℝ) * h)
                             (nhds 0)
                             (nhds (x₀ + (i.val : ℝ) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    simpa using h0
  -- Step 3: yex (x₀ + i·h) → yex x₀ = y₀.
  have h_yex_curve :
      Filter.Tendsto (fun h : ℝ => yex (x₀ + (i.val : ℝ) * h))
                     (nhds 0) (nhds y₀) := by
    have := hyex_cont_x₀.tendsto.comp h_curve
    simpa [hy0] using this
  -- Step 4: yex(x₀ + i·h) - start h i → y₀ - y₀ = 0.
  have h_diff :
      Filter.Tendsto (fun h : ℝ => yex (x₀ + (i.val : ℝ) * h) - start h i)
                     (nhds 0) (nhds 0) := by
    have := h_yex_curve.sub (hstart i)
    simpa using this
  -- Step 5: lift to abs.
  have := h_diff.abs
  simpa [abs_zero] using this
```

If `(hyex_diff x₀ le_rfl).continuousAt` fails because Lean cannot
unify `x₀ ≥ x₀` with `le_rfl`, swap to `(hyex_diff x₀ (le_refl x₀))`
or `(hyex_diff x₀ (by linarith))`. The `Step 5` `simpa` may need
`abs_zero` removed if the goal is already `Tendsto … (nhds 0) (nhds 0)`
without a residual `|0|`.

### Mathlib lemmas (verified to exist as of pinned Mathlib v4.28.0)

| Goal | Lemma |
|---|---|
| `HasDerivAt → ContinuousAt` | `HasDerivAt.continuousAt` |
| `f` continuous at `a`, `g h → a` ⇒ `f ∘ g h → f a` | `ContinuousAt.tendsto`, `Filter.Tendsto.comp` |
| Constant + linear continuous | `tendsto_const_nhds`, `tendsto_id`, `Filter.Tendsto.add`, `Filter.Tendsto.mul` |
| Tendsto subtraction | `Filter.Tendsto.sub` |
| Tendsto absolute value | `Filter.Tendsto.abs` |
| `\|0\| = 0` | `abs_zero` |

If any name has drifted, run `lean_local_search` first (don't burn
heartbeats on a name search inside `lake build`).

## Stretch deliverable (only if primary lands cleanly): sum form

Cycle 050 will need either a max form or a sum form to feed
`discrete_gronwall_exp_bound`. The **sum form is preferred** because
the Grönwall closed-form bounds a sum of recent errors, not a max.

```lean
/-- **Butcher §406D's φ(h) → 0 helper, sum form.**
The sum over `Fin k` of starting errors tends to 0 as `h → 0`.

Used by: cycle 050's outer assembly to bound the "starting block"
contribution to the global error. -/
private lemma starting_error_sum_tendsto_zero
    {k : ℕ} {f : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hy0 : yex x₀ = y₀)
    (hyex_diff : ∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) :
    Filter.Tendsto
      (fun h : ℝ =>
        ∑ i : Fin k, |yex (x₀ + (i.val : ℝ) * h) - start h i|)
      (nhds 0) (nhds 0) := by
  have h_each := starting_error_each_tendsto_zero hy0 hyex_diff hstart
  have h_sum :
      Filter.Tendsto
        (fun h : ℝ =>
          ∑ i : Fin k, |yex (x₀ + (i.val : ℝ) * h) - start h i|)
        (nhds 0)
        (nhds (∑ _i : Fin k, (0 : ℝ))) :=
    tendsto_finset_sum _ (fun i _ => h_each i)
  simpa using h_sum
```

`tendsto_finset_sum` lives in `Mathlib/Topology/Algebra/Group/Basic.lean`
(or `…/InfiniteSum/Basic.lean` — verify with `lean_local_search
"tendsto_finset_sum"` first). It takes per-index `Tendsto f_i (nhds 0)
(nhds c_i)` and returns `Tendsto (Σ_i f_i ·) (nhds 0) (nhds (Σ_i c_i))`.

If `tendsto_finset_sum` is misnamed or absent, fall back to induction
on `(Finset.univ : Finset (Fin k))` with `Finset.sum_insert` +
`Filter.Tendsto.add`. Don't burn the cycle on a name hunt — if 5
minutes of search doesn't find it, defer the sum form to cycle 050
and ship the per-index lemma alone.

## What NOT to do this cycle

* Do **NOT** attempt the cycle 050 outer assembly
  (`stable_consistent_isConvergent`'s body). It needs all four pieces
  (cycle 045 ψ-bound + cycle 048 contraction + cycle 049 φ(h) → 0 +
  cycle 046 Grönwall) plus matching `idx`/`Sε` shapes, which is the
  cycle 050 audit work the cycle 048 task-result flagged. Keep this
  cycle scoped to the φ(h) → 0 helper.
* Do **NOT** add a `0 < k` hypothesis to `starting_error_each_tendsto_zero`.
  When `k = 0`, the `Fin 0` quantification is vacuous, so the lemma
  is true with no constraint. Adding `0 < k` would force a degenerate
  branch in cycle 050. (Contrast with `theta_isHomogeneousSolution`
  and `theta_bounded_of_isStable`, which genuinely need `0 < k` —
  this lemma does not.)
* Do **NOT** weaken `(∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)` to
  `ContinuousAt yex x₀` in the signature. Match the existing
  `IsConvergent` definition's hypothesis shape (line 313) exactly,
  even though only the `x = x₀` instance is used here. This avoids a
  signature mismatch at the cycle 050 call site.
* Do **NOT** rename `start`, `yex`, `x₀`, `y₀`, or `k` to non-Butcher
  names. They match `IsConvergent` line-for-line; cycle 050 will
  destructure `IsConvergent`'s hypotheses and feed them directly.
* Do **NOT** introduce a `max`-form variant of the lemma. It is
  algebraically more complex (`Finset.sup'` requires a non-empty
  proof) and not the shape `discrete_gronwall_exp_bound` wants.
  If cycle 050 ends up needing a max form, build it then; for now,
  ship the per-index and (optionally) sum forms.
* Do **NOT** raise `maxHeartbeats`. The lemma should compile in
  default budget; if it doesn't, decompose into two helpers (e.g.
  factor "yex(x₀ + i·h) → y₀" out as a named `have`).
* Do **NOT** use `Filter.Tendsto.const_smul` or vector-spaces
  machinery. The `i.val * h` here is plain real-number multiplication;
  `Tendsto.mul` with `tendsto_id` and `tendsto_const_nhds` is the
  right shape and matches the rest of `Section404.lean`.
* Do **NOT** add Aristotle submissions this cycle. The lemma is
  ~25 lines; manual proof is faster than the 30-minute Aristotle
  cycle. (Reserve Aristotle compute for cycle 050's outer assembly
  if any of its sub-goals balloon.)
* Do **NOT** repeat the cycle-048 dead-end of writing `ring` to close
  a `≤` goal that simplifies to `lhs = rhs`. Use `apply le_of_eq; ring`
  or `linarith`. (Not directly relevant to this cycle's `Tendsto`
  proof, but preserved here as a `Section404.lean` idiom reminder.)

## Pre-commit checklist (worker, run before commit)

1. `lake env lean OpenMath/Chapter4/Section404.lean` — clean.
   Expected warnings: the existing 3 unused-variable warnings
   (lines 568, 627, 1204) and the documented `sorry` warning at
   line 1823. New warnings are acceptable only if they are
   unused-variable for `_`-prefixed names.
2. `#print axioms OpenMath.Chapter4.Section404.starting_error_each_tendsto_zero`
   in-place (then revert) → expect `[propext, Classical.choice, Quot.sound]`.
   If `sorryAx` shows up, the proof has a hidden gap — debug before
   committing.
3. Same axiom check for the sum form if shipped.
4. Sorry-count check: `rg '\bsorry\b' OpenMath/` — expect exactly
   1 hit, at `Section404.lean:1823` (the cycle 047 scaffold).
   Doc-string occurrences at lines 548 and 1816 are not Lean
   tokens — `rg '\bsorry\b'` already excludes them by word-boundary,
   but verify.
5. **Repo-state guard (cycle 047 trap mitigation).** After
   `git commit`, run:
   ```bash
   git log -1 --format='%H %s'
   git diff HEAD~1 HEAD --stat
   git rev-parse HEAD
   git rev-parse origin/Main/Experiments  # after push
   ```
   `HEAD == origin/Main/Experiments` and the diff shows the new
   lemma in `OpenMath/Chapter4/Section404.lean`. If the diff is
   empty or origin diverges, **fix before the cycle ends** — do
   not propagate a stale-attempts.md verdict to cycle 050.
6. **Faithfulness checklist** (CLAUDE.md):
   - `starting_error_each_tendsto_zero` is internal infrastructure,
     not a Butcher entity. Document inline.
   - Tautology check: conclusion `Tendsto … (nhds 0) (nhds 0)` is
     not in any hypothesis. Pass.
   - Identity check: 5-step proof, real content. Pass.
   - Hypothesis-strength check: `hyex_diff` is stronger than
     strictly necessary (only `x = x₀` is used), but matches
     `IsConvergent`'s shape — documented as intentional.

## Estimated cost

* Primary lemma: ~25 lines, ~30 min including Mathlib name search.
* Stretch sum form: ~10 lines, ~10 min.
* Cycle total: ~1 hour, well within budget.

## Suggested post-cycle followups for the planner

* **Cycle 050 (outer assembly)**: combine cycle 045 (ψ-bound),
  cycle 046 (Grönwall), cycle 048 (Σ θψ contraction), cycle 049
  (this cycle's φ(h) → 0). The biggest risk is matching `idx` and
  `Sε` shapes between cycles 045 and 048 — cycle 050's planner
  should audit cycle 045's exact ψ-bound shape (around line 1331
  in `Section404.lean`) and pick the `Sε` instantiation in cycle
  048 to match.
* **`thm:406D` post-mortem**: once the scaffold's sorry is closed,
  audit whether the proof needs `0 < k` (inherited from
  `theta_isHomogeneousSolution` and `theta_bounded_of_isStable`).
  If yes, push it up to the theorem statement; if not (e.g. the
  `k = 0` case is trivial), handle it as a separate branch.
* After `thm:406D` is closed, the natural next target is `thm:243A`
  (the Ch.2 → Ch.4 cross-chapter deferral). Its `def:404B`
  dependency is already in place. The planner should sequence
  `thm:243A` to immediately follow `thm:406D` rather than picking
  up Ch.4 leaves.
