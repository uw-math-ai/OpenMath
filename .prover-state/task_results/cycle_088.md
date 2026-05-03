# Cycle 088 Results

## Worked on
`def:520E` (A-stable general linear method) and three supporting
declarations in `OpenMath/Chapter5/Section520.lean`:

1. `GeneralLinearMethod.IsAStable` — the A-stability predicate.
2. `trivialZeroGLM` — non-vacuity witness, the all-zero `(1,1)` GLM.
3. `trivialZeroGLM_stabilityMatrix` — its stability matrix is `!![0]`
   for every `z ∈ ℂ`.
4. `trivialZeroGLM_isAStable` — the trivial GLM is A-stable.

## Approach
Followed the cycle 088 strategy verbatim. Added all four declarations
inside the `OpenMath.Chapter5.Section510` namespace block of
`Section520.lean`, just before its closing `end`. Reused the
`stabilityRegion`, `complexify`, and `Matrix.Norms.Operator` setup
already in that block from cycle 087. The
`trivialZeroGLM_stabilityMatrix` proof mirrors the cycle 086
`explicitEulerGLM_stabilityMatrix` proof (resolvent factor reduces to
`1`, then `Matrix.mul_apply` + `simp`). The `trivialZeroGLM_isAStable`
proof splits on `k`: the `k = 0` case closes by `simp`; for `k = n+1`
we use `zero_pow (Nat.succ_ne_zero n)` then `norm_zero`.

## Result
SUCCESS.

* `lake env lean OpenMath/Chapter5/Section520.lean` — clean (no
  output).
* `lake build OpenMath.Chapter5.Section520` — `✔ [2772/2772] Built
  OpenMath.Chapter5.Section520 (3.6s)`.
* `#print axioms` for all four new declarations:
  `[propext, Classical.choice, Quot.sound]`.

No Aristotle submissions were needed; the strategy's "only-if"
fallback condition did not trigger.

## Faithfulness check

### `def GeneralLinearMethod.IsAStable`

* **Entity ID**: `def:520E`.
* **Textbook statement** (quoted from
  `extraction/formalization_data/entities/def_520E.json`,
  `statement_latex` field):
  > A general linear method is `A-stable' if $M(z)$ is power-bounded
  > for every $z$ in the left half complex plane.
* **Lean statement**: `∀ z : ℂ, z.re ≤ 0 → z ∈ M.stabilityRegion`.
  Unfolding `M.stabilityRegion`, this becomes
  `∀ z : ℂ, z.re ≤ 0 → ∃ C, PowerBounded C (M.stabilityMatrix z)`,
  which is the literal textbook quantifier (left half plane → power
  bounded).
* **Captures**: same content. Encoding choice: closed left half-plane
  `z.re ≤ 0`. The textbook is silent on open vs closed; closed is the
  standard convention in stability theory and matches usage elsewhere
  in this codebase. Documented in the Lean docstring.
* **Definition smuggling**: NO. A-stability is encoded as exactly the
  textbook's quantifier (`∀ z, z ∈ left half-plane → power-bounded`),
  not as a derived characterization (e.g. eigenvalue conditions).
* **Hypothesis strength**: no hypotheses to weaken/strengthen.

### `def trivialZeroGLM`

* **Status**: not a Butcher entity — a Lean-side non-vacuity witness.
  Justification: needed to demonstrate `IsAStable` is satisfiable;
  `explicitEulerGLM` (the existing witness) is **not** A-stable
  (e.g. `M(-3) = !![-2]` whose powers diverge), so a separate witness
  is required.

### `theorem trivialZeroGLM_stabilityMatrix`

* **Tautology check**: hypothesis-free; conclusion is the matrix
  equation `M.stabilityMatrix z = !![0]`. Not a hypothesis restated.
* **Identity check**: proof is non-trivial — unfolds the resolvent,
  uses `Matrix.mul_apply`. Real mathematical work.

### `theorem trivialZeroGLM_isAStable`

* **Tautology check**: hypothesis-free; conclusion is `IsAStable`,
  providing real witnesses (`C = ‖1‖` and a `k`-uniform bound).
* **Identity check**: proof is non-trivial — supplies a concrete
  power bound and case-splits on `k`.
* **Hypothesis strength**: no hypotheses.

## Dead ends
None this cycle. The strategy's "Likely build issues and quick fixes"
section anticipated three potential snags (`cases k` motive,
`zero_pow` argument shape, `!![0] = 0` matrix coercion); none of them
fired — the spelled-out tactic block compiled on first attempt.

## Discovery
* The `cases k with | zero => ... | succ n => ...` syntax with a
  fully spelled-out `succ` arm (`zero_pow (Nat.succ_ne_zero n)`,
  `norm_zero`, `norm_nonneg _`) compiles cleanly without motive
  issues — useful template for future "norm of a `k`-power" lemmas.
* The `(!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0` rewrite
  via `ext + fin_cases + simp` is the canonical bridge between
  Lean's `!![0]` literal-matrix notation and the abstract
  `0 : Matrix _ _ _` element. Mathlib does not provide a direct
  simp lemma for this on `1×1`; the manual extension is short.

## Suggested next approach

* **`def:520F` (L-stable)** — the only direct downstream consumer of
  `def:520E`. L-stability adds a `lim_{|z| → ∞} ‖M(z)‖ = 0`
  requirement on top of A-stability. The complex-limit half is
  non-trivial: the planner should choose between `Filter.Tendsto`
  (`atTop` filter on `‖z‖`) and a more elementary `∀ ε > 0, ∃ R, ...`
  formulation. Non-vacuity still works with `trivialZeroGLM` (the
  norm of `M(z) = !![0]` is `0` for every `z`, so the limit is `0`).
* **`thm:520B`** — still needs the GLM-iteration encoding pass
  flagged in cycle 087's results; defer until a planner cycle is
  dedicated to that design.
* **`thm:520D`** (Instability Region Boundary Characterization) —
  closer in flavour to `def:520E` than `thm:520B`; uses
  `stabilityRegion` and the stability function directly. May be a
  good "in-between" target between `def:520E` and `def:520F`.
