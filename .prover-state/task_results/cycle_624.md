# Cycle 624 Results

## Worked on
§512 LMM stability lift, Phase D step 3 — packaging the y-half iterate
of the structural `V`-iterate as the LMM companion-state iterate.
Three deliverables in `OpenMath/LMMAsGLM.lean`:

1. `LMM.toGLM_y_step` — real-valued companion-step operator on
   `Fin s → ℝ`.
2. `LMM.toGLM_y_half_step_eq` — one-step matching:
   `toGLM_y_half (V^{n+1} q) = toGLM_y_step m (toGLM_y_half (V^n q))`
   for `n ≥ s`.
3. `LMM.toGLM_y_half_iter_eq` — multi-step matching:
   `toGLM_y_half (V^{n+j} q) = (toGLM_y_step m)^[j] (toGLM_y_half (V^n q))`
   for `n ≥ s` and any `j : ℕ`.

## Approach
Followed the strategy script literally.

- Deliverable 1: a `noncomputable def` with a `dif`-branch on
  `(k : ℕ) + 1 = s`. The else-branch lifts the y-state index by 1 with
  the `Fin.isLt`-based bound.
- Deliverable 2: `funext k`, `by_cases hk1 : (k : ℕ) + 1 = s`. In each
  branch:
  - `rw [Function.iterate_succ_apply']` to rewrite the LHS into one
    application of `V` to `V^n q`.
  - A `show` clause exposed the LHS in the literal sum-shape used by
    the cycle 622/623 lemmas
    (`∑ l, m.toGLM.V (Fin.cast _.symm (Fin.castAdd s k)) l * (V^n q) l`).
    The `toGLM_y_half … k` projection is definitionally that sum, so
    `show` succeeds without a tactic.
  - `unfold toGLM_y_step; rw [dif_pos hk1]` (last branch) /
    `rw [dif_neg hk1]` (shift branch) and the existing
    `toGLM_V_iter_step_y_last` / `toGLM_V_iter_step_y_shift` lemmas
    closed each branch by `exact`.
- Deliverable 3: induction on `j`.
  - `j = 0`: `simp` closed it (both sides reduce to
    `toGLM_y_half (V^n q)`).
  - `succ j`: `rw [Nat.add_succ, Function.iterate_succ_apply' …]` to
    move one `toGLM_y_step` to the outside on the RHS, then
    `rw [← ih]` to fold the inner `j`-iterate, then
    `exact toGLM_y_half_step_eq m q (n + j) (by omega)` for the
    one-step bridge with the strengthened `s ≤ n + j` hypothesis.

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM.lean` exits 0;
`grep -c sorry OpenMath/LMMAsGLM.lean` is `0`. File grew from 1077 to
1143 lines, well under the 3000-line cap.

## Dead ends
None — followed the script first try. The only minor surprise was
that without the `show` clause Lean's elaborator did not see the LHS
of `toGLM_y_half (V^{n+1} q) k` and the `V^n q`-form sum as
definitionally equal at the surface level needed for `exact` to fire,
so I added a `show` to expose the sum shape. This was already the
shape suggested by the strategy ("`change` to that shape if needed").

## Discovery
- `Function.iterate_succ_apply'` rewrites `f^[n+1] x` to `f (f^[n] x)`,
  exposing the outer single-step shape needed to rewrite under a
  projection like `toGLM_y_half`.
- The y-half projection at the last index `k` with `(k : ℕ) + 1 = s`
  agrees definitionally with the indexed sum used by the cycle
  622/623 lemmas; same on the shift branch. No reindexing needed
  beyond the `show` clause.
- The `Nat.add_succ` + `Function.iterate_succ_apply'` pairing on the
  `succ j` step is the standard induction shape for chaining
  `f^[n+j]` against `f^[j] (f^[n] x)`.

## Suggested next approach
Phase D step 4 (one cycle): bridge the real-valued
`toGLM_y_step` to the LMM characteristic recurrence `tupleSucc` via
`Complex.ofReal` coercion. Concretely:

1. Define `toGLM_y_step_ℂ` as the `Complex.ofReal`-coercion of
   `toGLM_y_step` (or state a lemma equating
   `Complex.ofReal ∘ toGLM_y_step m v = m.toLinearRecurrence.tupleSucc (Complex.ofReal ∘ v)`
   up to whatever `Fin s ≃ Fin s` reindexing the LMM characteristic
   recurrence uses).
2. Lift `toGLM_y_half_iter_eq` to ℂ via that bridge.

Then Phase E (one cycle): combine the lifted iterate identity with
`uniformly_bounded_tupleSucc_iterates` (from the LMM stability /
characteristic-roots infrastructure) for `n ≥ s`, plus the cycle 621
Phase C `M_max`-row bound for `n < s`, to close
`LMM.toGLM_isStable`.

The key unknown for Phase D step 4 is the indexing convention used by
`m.toLinearRecurrence.tupleSucc`: whether its state is
`(y_n, y_{n+1}, …, y_{n+s-1})` (matching `toGLM_y_half`) or some other
ordering. Worth a quick `lean_hover_info` / `lean_declaration_file`
check on `LMM.toLinearRecurrence` and `tupleSucc` before scripting
Phase D step 4 in detail.
