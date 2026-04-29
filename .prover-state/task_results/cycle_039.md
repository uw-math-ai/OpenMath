# Cycle 039 Results

## Worked on
`def:406A` — local truncation error of a linear multistep method
(Butcher §406, p. 345). Added to
`OpenMath/Chapter4/Section404.lean` as
`LinearMultistepMethod.localTruncationError`, plus two non-vacuity
witnesses:

- `localTruncationError_const`: LTE vanishes on constant functions
  under preconsistency.
- `localTruncationError_linear`: LTE vanishes on linear-in-`x`
  functions under consistency.

## Approach
Followed the cycle 039 strategy verbatim — Option A (textbook-faithful
encoding). The definition reads:

```lean
noncomputable def LinearMultistepMethod.localTruncationError {k : ℕ}
    (M : LinearMultistepMethod k) (y : ℝ → ℝ) (x h : ℝ) : ℝ :=
  y x
    - ∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
    - h * ∑ i : Fin (k + 1), M.β i * deriv y (x - ((i.val : ℕ) : ℝ) * h)
```

Witness 1 unfolds the definition and uses `deriv_const` plus
preconsistency `1 = ∑ M.α i.succ` to collapse the formula to `c-c-0`.
Witness 2 expands `y(x - (i+1)·h) = a·x - a·h·(i+1) + b`, uses
`Finset.sum_sub_distrib`/`sum_add_distrib`/`Finset.mul_sum` to split,
applies preconsistency for the `Σ M.α i.succ = 1` sums and (404b) for
`Σ ((i+1):ℝ) · M.α i.succ = Σ M.β i`, and finishes with `ring`.

## Result
SUCCESS. The file compiles cleanly (`lake env lean
OpenMath/Chapter4/Section404.lean` exits 0 with no diagnostics).
No `sorry` in the new code.

A self-contained Aristotle submission was filed at
`.prover-state/aristotle_submissions/cycle_039/witnesses.lean`
(project ID `53e58db1-9207-4f51-a832-8804c4e7662d`) for both witness
theorems. As of commit time it remained `IN_PROGRESS` at 1% — the
manual proofs finished first, so per the cycle 039 strategy
("if your manual proof finishes first, keep it") the manual versions
ship. If a future cycle wants to swap Aristotle's cleaner version in,
the project can be polled via `mcp__aristotle__get_status`.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `LinearMultistepMethod.localTruncationError`

- Entity ID: `def:406A`. Textbook statement (quoted from
  `extraction/formalization_data/entities/def_406A.json`):

  > Let `[α, β]` be a consistent linear multistep method. The 'local
  > truncation error' associated with a differentiable function `y` at
  > a point `x` with stepsize `h` is the value of
  > `L(y, x, h) = y(x) − Σ_{i=1}^{k} α_i · y(x − ih) − h · Σ_{i=0}^{k} β_i · y'(x − ih)`.

- Lean statement captures: **same content**. The Lean definition
  encodes the textbook formula verbatim — sums, signs, and index
  ranges all match. Two trivial syntactic differences:
  (a) Butcher's `α_i` for `i ∈ {1,…,k}` is `M.α i.succ` for
  `i : Fin k` in our `Fin (k+1)`-based encoding (the leading
  `α 0 = -1` slot of our structure is unused in the formula, exactly
  as in Butcher).
  (b) `y'` is encoded as Mathlib's `deriv y`, which agrees with the
  classical derivative on differentiable points (the textbook's
  domain of interest) and returns `0` elsewhere — a standard
  Mathlib convention used identically in `IsLMMSolution`'s neighbour
  predicates.

- Definition smuggling check: ✓ defined as the textbook formula, not
  as an order property like "`L = O(h²)`". The order behaviour is a
  *consequence* under consistency (cf. §406's later content), not the
  definition.

- Hypothesis strength check: the definition takes no hypotheses
  (it's a value, not a Prop). Consistency / preconsistency are
  hypotheses of the *witnesses* below, not of the definition — which
  matches the textbook (Butcher's "Let `[α, β]` be a consistent…"
  is framing prose for the discussion that follows, not part of the
  formula's signature).

### `localTruncationError_const`

- Entity: helper non-vacuity witness (CLAUDE.md "every new
  `def` requires a concrete witness"). Not in the textbook entity
  list.
- Statement: `M.localTruncationError (fun _ => c) x h = 0` under
  `M.IsPreconsistent`.
- Tautology check: ✓ conclusion is not a hypothesis.
- Identity check: ✓ proof is real arithmetic, not `exact h`.
- Hypothesis strength: textbook-natural — Butcher's discussion in
  §406 implicitly assumes preconsistency for "constants kill LTE".

### `localTruncationError_linear`

- Entity: helper non-vacuity witness.
- Statement: `M.localTruncationError (fun t => a*t + b) x h = 0`
  under `M.IsConsistent`.
- Tautology check: ✓ conclusion is not a hypothesis.
- Identity check: ✓ proof unfolds, expands, splits the α-sum into
  three pieces, and applies the (404b) identity — real arithmetic
  work.
- Hypothesis strength: matches the textbook framing ("consistency
  ⇒ LTE vanishes on linear test functions").

## Dead ends

1. Initial draft of the definition was missing `noncomputable`. Lean
   rejected with `failed to compile definition, consider marking it as
   'noncomputable' because it depends on 'Real.instRCLike'`. Adding
   the marker fixed it (`deriv` is non-computable on `ℝ`, which forces
   the noncomputability up).
2. First draft of witness 2 had a stray `Finset.sum_mul_comm.symm`
   rewrite that doesn't exist in Mathlib. Removed; the proof closes
   without it via the explicit `hβ'` rewrite at the end.

## Discovery

The `M.SatisfiesEq404b` predicate stores its α-sum as
`((i : ℕ) + 1 : ℝ)` (with `i : Fin k`), but my expanded sum naturally
produces `(((i.val + 1 : ℕ) : ℝ))`. These are propositionally equal
but not definitionally so — `convert ... using 1` followed by
`Finset.sum_congr` + `push_cast; ring` bridges the gap. Future
consumers of `SatisfiesEq404b` should expect to use this same pattern.

## Suggested next approach

The strategy lists the natural follow-on chain:
`lem:406B → thm:406C → thm:405A → thm:405B → thm:405C → thm:406D`,
which after `thm:406D` collapses `thm:243A` to a corollary.

`lem:406B` is the next step. It is the "convergence condition
sufficiency bound" — likely a numerical bound on
`localTruncationError` for sufficiently smooth `y`. Cycle 040 should
read `entities/lem_406B.json` first to see whether it requires
Taylor-expansion infrastructure (which would push it to a multi-cycle
project) or is a one-cycle algebraic deliverable. If the former, the
fallback target should be `def:451A` (G-stable) — a standalone Ch.4
definition that doesn't gate other §405 / §406 work.

The Aristotle submission for cycle 039's witnesses
(project `53e58db1-9207-4f51-a832-8804c4e7662d`) is still in flight at
commit time; if it eventually returns clean proofs, cycle 040 could
swap them in for code-quality reasons (lower priority than the
forward-progress chain above).
