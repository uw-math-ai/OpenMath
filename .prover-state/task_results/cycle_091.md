# Cycle 091 Results

## Worked on

`def:512A` — convergence of a general linear method (Butcher §512,
p. 409). Created the new file `OpenMath/Chapter5/Section512.lean`
containing:

* `GeneralLinearMethod.IsGLMSolution` — the per-step iteration
  recurrence with stage existential.
* `GeneralLinearMethod.IsConvergent` — the textbook predicate
  (Definition 512A).
* `isGLMSolution_zero_iff` — sanity bridge: `f ≡ 0` reduces to the
  homogeneous V-recurrence.
* `zero_isGLMSolution_zero` — non-vacuity: the zero sequence is a
  GLM iteration.
* `zero_seq_homogeneous_V` — bonus infrastructure helper.

Also wrote `.prover-state/issues/glm_convergence_witness_deferred.md`
documenting why a concrete `IsConvergent` witness is deferred to the
`thm:515D` cycle.

## Approach

1. Read `extraction/formalization_data/entities/def_512A.json` and
   confirmed the textbook statement.
2. Studied the LMM template in `OpenMath/Chapter4/Section404.lean`
   (cycle 038) for `IsLMMSolution` / `IsConvergent` shape.
3. Submitted three Aristotle helpers in parallel
   (`isGLMSolution_zero_iff`, `zero_isGLMSolution_zero`,
   `zero_seq_homogeneous_V`) at cycle start.
4. Wrote the file in the `OpenMath.Chapter5.Section510` namespace
   (matching the `Section520.lean` dot-notation pattern), with full
   manual proofs of all three helpers using
   `simp [mul_zero, Finset.sum_const_zero]` style.
5. Verified `lake env lean OpenMath/Chapter5/Section512.lean` and
   `lake build OpenMath.Chapter5.Section512` both clean.
6. Confirmed `#print axioms` shows only `propext, Classical.choice,
   Quot.sound` for all five new declarations — no `sorryAx`.
7. Aristotle returned in ~8 minutes with `aesop`-based proofs that
   were structurally identical (same theorem statements, more opaque
   tactics). Kept the more transparent manual proofs.
8. Updated `extraction/formalization_data/lean_status.json` and
   `plan.md` (counter `61 → 62`).

## Result

**SUCCESS** — all five new declarations compile, axioms are clean,
faithfulness checks pass.

## Faithfulness check

### `def:512A` → `GeneralLinearMethod.IsConvergent`

* Entity ID and textbook statement (quoted from formalization_data):
  > A general linear method `(A, U, B, V)`, is 'convergent' if for any
  > initial value problem `y'(x) = f(y(x)), y(x₀) = y₀`, subject to
  > the Lipschitz condition `‖f(y) − f(z)‖ ≤ L ‖y − z‖`, there exist a
  > non-zero vector `u ∈ ℝ^r`, and a starting procedure
  > `φ : (0, ∞) → ℝ^r`, such that for all `i = 1, 2, …, r`,
  > `lim_{h→0} φ_i(h) = u_i y(x₀)`, and such that for any `x > x₀`,
  > the sequence of vectors `y^{[n]}`, computed using `n` steps with
  > stepsize `h = (x − x₀)/n` and using `y^{[0]} = φ(h)` in each case,
  > converges to `u y(x)`.

* Lean statement captures: **same content** (with the documented
  scalar-`f` simplification — see below).

* Encoding choices vs. textbook:
  - **Autonomous scalar `f : ℝ → ℝ`** — matches textbook literally
    (`y'(x) = f(y(x))`). Vectorization is a future generalization.
  - **`φ : ℝ → Fin r → ℝ`** — the textbook's domain `(0, ∞)` is
    encoded by the `Filter.Tendsto … (nhds 0)` hypothesis, which only
    constrains behavior near 0; values at `h ≤ 0` are irrelevant
    junk. This matches the cycle-038 LMM encoding.
  - **No preemptive strengthening** (joint Lipschitz, ContDiff ℝ 1,
    `M_bound`) per planner directive. If a downstream §513/§514/§515
    proof needs them, file a parallel issue at that point.

* Tautology check: ✓ — the conclusion
  `Tendsto (Y n n) atTop (nhds (fun i => u i * yex x))` is genuinely
  derived from the iteration; no hypothesis says this directly.
* Identity check: N/A (definition, not a theorem with proof).
* Definition smuggling check: ✓ — `IsConvergent` does NOT embed the
  conclusion of `thm:515D` (stable+consistent ⇒ convergent). It is
  the convergence predicate alone, with no `IsStable` or
  `IsConsistent` sub-clauses.
* Hypothesis-strength check: ✓ — only `LipschitzWith L f`,
  `yex x₀ = y₀`, `HasDerivAt yex (f (yex x)) x` — exactly the
  textbook hypotheses, no more.

### `IsGLMSolution` (helper recurrence; not a textbook entity)

* Lean statement captures: the GLM step equations from Butcher §511,
  per-step over `Fin s` stages (parallel to `IsLMMSolution`).
* Existential `Y` per step (rather than over the whole history) is the
  right encoding because the stage tuple at step `n+1` depends only
  on `y_seq n`, not prior stages.
* Tautology check: ✓ — output equation has `y_seq (n+1) i = …` on the
  LHS and a function of `Y, y_seq n` on the RHS; not a
  re-statement.

### Helper theorems

* `isGLMSolution_zero_iff`: forward extracts `Y` from the existential
  and uses `mul_zero, Finset.sum_const_zero, zero_add`; reverse
  constructs `Y i := Σ_j U_{ij} y_seq n j` and verifies both
  equations. **Identity check ✓** — the proof is not `exact h`, it is
  forward/reverse implication of an unfolding with substantive
  `simp [mul_zero, Finset.sum_const_zero]` work.
* `zero_isGLMSolution_zero`: pure `simp` after instantiating
  `Y = (fun _ => 0)`. **Identity check ✓** — provides a witness
  (the zero stage) that the predicate did not contain.
* `zero_seq_homogeneous_V`: pure `simp`. Trivially true; no tautology
  (the LHS is `0` and the RHS is `Σ M.V i j * 0`, simplified).

### Confirmed via `#print axioms`

```
GeneralLinearMethod.IsConvergent       : [propext, Classical.choice, Quot.sound]
GeneralLinearMethod.IsGLMSolution      : [propext, Classical.choice, Quot.sound]
isGLMSolution_zero_iff                 : [propext, Classical.choice, Quot.sound]
zero_isGLMSolution_zero                : [propext, Classical.choice, Quot.sound]
zero_seq_homogeneous_V                 : [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. All clean.

## Dead ends

* Initial import `Mathlib.Topology.Algebra.Order.Filter` does not
  exist in this Mathlib snapshot. Replaced with the trio
  `Mathlib.Analysis.Calculus.Deriv.Basic`,
  `Mathlib.Topology.MetricSpace.Lipschitz`,
  `Mathlib.Topology.Order.Basic` which together cover
  `LipschitzWith`, `HasDerivAt`, `Filter.Tendsto`, `nhds`,
  `Filter.atTop`, `NNReal`. The `import Mathlib` fallback
  compiled but timed out at >480 s; targeted imports compile in <60 s.
* Aristotle's `aesop`-based proofs were structurally fine but more
  opaque than the manual `simp [mul_zero, Finset.sum_const_zero,
  zero_add]` proofs already in place; kept the manual proofs for
  readability and faster typecheck.

## Discovery

* The strategy's "Section520 pattern" of declaring
  `GeneralLinearMethod.foo` while inside `namespace
  OpenMath.Chapter5.Section510` works smoothly — the new dot-notation
  declarations end up in the same namespace as the structure
  definition itself, which is what downstream §513/§514/§515 work
  will want.
* For autonomous scalar `f : ℝ → ℝ` and the GLM iteration, the
  homogeneous V-recurrence falls out of `f ≡ 0` cleanly via two
  `simp [mul_zero, Finset.sum_const_zero, zero_add]` calls (one per
  direction). No need for the planner-suggested 30-line decomposition.
* Aristotle was much faster than the 30-min budget on this problem
  (~8 min for three trivial helpers). For future def-only cycles,
  Aristotle preflight is essentially free insurance — submit and
  proceed in parallel.

## Suggested next approach

Per `def:512A`'s dependents (`thm:513A`, `thm:514A`, `lem:515B`,
`thm:515D`), the natural next step is **`thm:513A`** — *necessity of
stability*. Butcher §513 (p. 410) shows that any convergent GLM is
stable. The proof (per textbook):

1. Assume `M.IsConvergent` and `¬ M.IsStable`.
2. Pick the trivial IVP `f ≡ 0`, `y₀ = 0`, `yex ≡ 0`.
3. Pick `u, φ` from the convergence assumption.
4. By `¬ IsStable`, find `n_k` with `‖V^{n_k}‖ → ∞`. Use this to
   construct an iterate sequence diverging from `u · 0 = 0`,
   contradicting convergence.

Cycle 092 should:

* State `thm:513A` (`M.IsConvergent → M.IsStable`).
* Use the just-landed `zero_isGLMSolution_zero` and
  `zero_seq_homogeneous_V` infrastructure to construct the
  contradiction sequence.
* If the proof needs `IsConvergent` strengthened (it likely doesn't
  for this case — the trivial IVP doesn't engage with continuity of
  `f`), file a parallel `glm_is_convergent_strengthened.md` issue.

Alternative cycle-092 candidates:

* **`thm:514A`** (necessity of consistency) — same shape as 513A but
  uses a slightly less trivial IVP (`f` constant nonzero,
  `yex(x) = y₀ + (x - x₀) * c`). Slightly harder.
* **`lem:515B` / `thm:515D`** (sufficiency direction) — substantially
  harder; requires discrete Grönwall on GLM iterates and likely the
  cycle-068 strengthenings. Probably 3+ cycles of work; not the next
  step.

Recommended: **`thm:513A`** for cycle 092. Smallest follow-on, uses
exactly the helpers landed this cycle, and directly exercises the
new `IsConvergent` predicate.
