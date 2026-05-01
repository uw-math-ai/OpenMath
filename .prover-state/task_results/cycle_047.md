# Cycle 047 Results

## Worked on

(a) **Priority 0 — recovered cycle 046's orphan**: committed
    `discrete_gronwall_exp_bound` (and helpers `_v_geom`,
    `_one_add_pow_le_exp`) as a fresh commit on top of `99c7b6f`.
    Pushed to origin.
(b) **Priority 1 — `thm:406D` scaffold**:
    `LinearMultistepMethod.stable_consistent_isConvergent` with
    `sorry`. Lean signature:
    `(M : LinearMultistepMethod k) (hstab : M.IsStable)
     (hcons : M.IsConsistent) : M.IsConvergent` — exactly the
    textbook hypotheses, no extras.
(c) **Priority 2 — Θ-extraction connectors** (closed in full,
    no sorry):
    * `theta_isHomogeneousSolution` — bridges
      `Section141.theta` to `Section404.IsHomogeneousSolution`.
    * `theta_bounded_of_isStable` — extracts `Θ ≥ 0` from
      `IsStable` via the `max ⬝ 0` trick.

## Approach

**Priority 0.** Verified `git diff` matched expected helpers, ran
`lake env lean OpenMath/Chapter4/Section404.lean` (clean), and
axiom-checked `discrete_gronwall_exp_bound` (in-place
`#print axioms` then revert) → `[propext, Classical.choice, Quot.sound]`.
Created a new commit (no amend), pushed.

**Priority 2.** `theta_isHomogeneousSolution` uses
`obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1` to refine `k = k' + 1`
syntactically (so `m + k = (m + k') + 1` is `rfl`-equal). Then
`theta_succ` applies directly, the conditional `j.val ≤ m + k'`
fires for every `j : Fin (k' + 1)` (because `j.val < k' + 1 ≤
m + k' + 1`), and the index identity `m + k' - j.val =
m + (k' + 1) - (j.val + 1)` is closed by `omega`.
`theta_bounded_of_isStable` is 4 lines: pull `C` out of `IsStable`,
take `max C 0`, transitivity.

**Priority 3 batch (skipped).** The two batch items targeting
connector helpers (items 1 and 2) were redundant — both connectors
closed manually in <30 lines. The remaining batch items (3, 4, 5)
target sub-lemmas of the still-`sorry` outer proof and are out of
scope per the strategy's stretch-goal guard. Skipping Aristotle was
the right call — the cycle 018 trap was the dominant risk and this
keeps the deliverable tight.

## Result

**SUCCESS** — both Priority 0 (orphan recovery) and Priority 1+2
(scaffold + connectors) shipped.

* `lake env lean OpenMath/Chapter4/Section404.lean` → clean
  (sorry warning on `stable_consistent_isConvergent` only).
* `lake build` → green.
* Axiom check (in-place, then reverted):
  - `theta_isHomogeneousSolution` → `[propext, Classical.choice, Quot.sound]`
  - `theta_bounded_of_isStable` → `[propext, Classical.choice, Quot.sound]`
  - `stable_consistent_isConvergent` → `[propext, sorryAx, ...]` (expected)
* Sorry count for `OpenMath/`: 0 → 1 (the documented scaffold sorry).

## Faithfulness check

### `theta_isHomogeneousSolution`

* **Connector helper, no Butcher entity.** Documented inline.
* **Tautology check**: conclusion `M.IsHomogeneousSolution …` does
  NOT appear as a hypothesis. Pass.
* **Identity check**: real proof content (index manipulation +
  conditional discharge). Not vacuous. Pass.
* **Hypothesis-strength check** — *deviation from strategy*:
  added `(hk : 0 < k)`. The strategy author claimed the `k = 0`
  case would collapse to `Fintype.sum_empty`, but the LHS
  `theta 0 _ m` does NOT collapse — `theta 0 _ 0 = 1` by
  `theta_zero`, while the RHS sum (over `Fin 0`) is `0`. So the
  claim is FALSE for `k = 0` and the hypothesis is mathematically
  necessary, not a smuggled strengthening. Documented in the
  docstring with a "why this hypothesis exists" paragraph.
  Butcher §141 implicitly assumes `k ≥ 1` (otherwise no
  recurrence).

### `theta_bounded_of_isStable`

* **Connector helper, no Butcher entity.** Documented inline.
* **Tautology check**: conclusion `∃ Θ ≥ 0, …` is genuinely stronger
  than `IsStable`'s `∃ C, …` (the `0 ≤ Θ` clause is derived).
  Pass.
* **Identity check**: 4-line proof, but the `0 ≤ Θ` derivation is
  real work. Pass.
* **Hypothesis-strength check**: requires `(hk : 0 < k)` (inherited
  from `theta_isHomogeneousSolution`). Same justification.

### `LinearMultistepMethod.stable_consistent_isConvergent`

* **Entity ID**: `thm:406D`.
* **Textbook statement** (`entities/thm_406D.json`):
  > A stable consistent linear multistep method is convergent.
* **Lean statement captures**: same content. Hypotheses are
  exactly `M.IsStable` + `M.IsConsistent`; conclusion is
  `M.IsConvergent` (Definition 402A predicate). No extra
  hypotheses (intentionally — `0 < k` is NOT added at the
  scaffold level; cycle 048+ may need to handle `k = 0`
  separately or push `0 < k` up if it turns out to be
  fundamental to the proof).
* **Body**: `sorry`. **Documented as expected** — this is the
  scaffold-only deliverable for cycle 047, with the proof outline
  in the strategy file and below.
* `lean_status.json` updated to `"partial"` with `lean_symbol =
  "OpenMath.Chapter4.Section404.LinearMultistepMethod.stable_consistent_isConvergent"`.

## Dead ends

* Initial `match k, M with | 0, M => … | k' + 1, M => …` for
  `theta_isHomogeneousSolution` failed because the type of `α` was
  not refined. Fixed by `obtain ⟨k', rfl⟩` after adding `0 < k`.
* `rw [hk1, theta_succ]` rewrote the index in two places (outer
  `theta` and inner sum), creating an unsolvable `m+k-1+1-1 = m+k-1`
  equation visible to Lean but not auto-closed. Fixed by switching
  to `obtain ⟨k', rfl⟩` and using `show … ((m + k') + 1)` for the
  rfl-rewrite.

## Discovery

* **Strategy can be wrong about edge cases.** The `k = 0` case for
  `theta_isHomogeneousSolution` was claimed to collapse trivially in
  the strategy doc, but it doesn't — the predicate forces `y m = 0`
  which contradicts `theta_zero : theta _ _ 0 = 1`. Always
  sanity-check edge cases against the actual definitions.
* **`obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1` is the cleanest way to
  refine a positive natural.** It avoids the `match` expression's
  problem of not refining types of pre-defined locals.
* **The strategy's "k = 0 collapses" instinct is correct for
  `theta_bounded_of_isStable`** — there `IsStable` is vacuously
  true (the only solution is the zero sequence) and the bound holds
  with `Θ = 1` since `theta 0 _ 0 = 1` and all later values are 0.
  But because we built `theta_bounded_of_isStable` on top of
  `theta_isHomogeneousSolution`, it inherits the `0 < k` constraint.
  Both helpers could be reformulated to handle k=0 separately if
  cycle 048+ needs it.

## Suggested next approach

Per strategy §"Proof outline of the eventual `stable_consistent_isConvergent`":

1. **Cycle 048 — Σ θψ contraction sub-lemma** (Priority-3 batch
   item 3 from cycle 047 strategy). Given `|ψ_n| ≤ Ch·max + Dh²`
   and `|θ_i| ≤ Θ`, conclude
   `|Σ_{i=k..n-1} θ_{n-i} ψ_i| ≤ ΘChk · Σ |ε_{i-j}| + ΘD(n-k)h²`.
   This is the Σ → Σ contraction (the "factor `k`" remark in the
   textbook). Could be Aristotle-suitable (telescope inequality on
   `Finset.sum`).
2. **Cycle 049 — φ(h) → 0 helper** (Priority-3 batch item 4). Pure
   `Filter.Tendsto` analysis: from `start h i → y₀` (per
   `IsConvergent`'s starting-method hypothesis), conclude
   `max_{i < k} |yex(x₀ + i·h) - start h i| → 0` as `h → 0`.
3. **Cycle 050 — outer assembly**. Combine Σ θψ contraction +
   φ(h) → 0 + `discrete_gronwall_exp_bound` +
   `linRec_closed_form` to close the scaffold.

A multi-cycle decomposition (3 cycles after this one) is the
realistic shape. See strategy §"Estimated cost".

The connector helpers' `0 < k` constraint should be flagged to the
cycle 048 planner: the eventual proof needs to either inherit
`0 < k` (most natural — Butcher's `k = 0` case is degenerate) or
handle `k = 0` as a separate trivial branch.
