# Cycle 251 Results

## Worked on
Positivity infrastructure for α(t) (Butcher §302):

- Moved `order_pos` from `OpenMath/Chapter3/Section323.lean` to
  `OpenMath/Chapter3/Section301.lean` (same namespace, single
  definition site).
- Added `density_pos` and helper `densityProd_pos` (mutual block).
- Added `symmetry_pos` and helper `symmetryProd_pos` (mutual block).
- Added `alphaWeight_pos` (composite via `div_pos` / `mul_pos`).

All four new theorems in `namespace OpenMath.Chapter3.Section310.RootedTree`.

## Approach
Followed the cycle-251 strategy file verbatim:

1. Deleted the `order_pos` block from Section323 (lines 51–60 of the
   original file) and re-inserted it in Section301 just after
   `density_eq`. Section323 already imports Section301, so the two
   downstream consumers (`hasInternalOrder_zero` and
   `explicitEuler_hasInternalOrder_one`) keep working unchanged via
   the same fully-qualified `RootedTree.order_pos` name.
2. `density_pos`/`densityProd_pos` via `Nat.mul_pos` on the literal
   `order * densityProd` (resp. `density * densityProd`) bodies,
   exposed by `show`.
3. `symmetry_pos`/`symmetryProd_pos` via `split_ifs` on the
   `t ∈ rest` branch of `symmetryProd`, using
   `Nat.factorial_pos` + `pow_pos (symmetry_pos t) (full.count t)`
   for the new-distinct-subtree branch and recursive call on the
   already-seen branch. The empty-cursor base case needed
   `show (0 : ℕ) < 1; decide` because plain `by decide` failed on
   the unsubstituted `symmetryProd x✝ []` reduct (free-variable
   diagnostic).
4. `alphaWeight_pos` via `unfold alphaWeight; div_pos; mul_pos`
   with `exact_mod_cast` to lift the Nat-valued positivity facts to ℝ.

Two minor adjustments from the strategy template:

- Docstrings had to move *inside* each `mutual` block (attached to
  the individual theorems) rather than on the `mutual` keyword. The
  template had a single docstring on the block, which Lean rejected
  with `unexpected token 'mutual'; expected 'lemma'`.
- The `[]` base case of `symmetryProd_pos` needed an explicit
  `show (0 : ℕ) < 1` before `decide`; without it, `decide` saw
  `0 < symmetryProd x✝ []` and complained about the free variable
  `x✝` (the unsubstituted `full` argument) — `symmetryProd _ [] = 1`
  is `rfl` but `decide` apparently doesn't normalise through the
  pattern match in this position.

## Result
SUCCESS — all four new theorems land axiom-clean.

Verification protocol (§E of strategy):

| Step | Command | Outcome |
|---|---|---|
| E.1 | `lake env lean OpenMath/Chapter3/Section301.lean` | clean exit |
| E.2 | `lake env lean OpenMath/Chapter3/Section323.lean` | clean exit |
| E.3 | `lake env lean OpenMath/Chapter3.lean` | clean exit (after `lake build` refreshed Section323's .olean) |
| E.4 | `grep -c sorry OpenMath/Chapter3/Section301.lean` | 0 |
| E.5 | `grep -c sorry OpenMath/Chapter3/Section323.lean` | 0 |
| E.6 | `#print axioms` on the four theorems | only `[propext, Classical.choice, Quot.sound]` (or strict subsets) |
| E.7 | Tautology regex sweep on Section301 | 0 hits |

`#print axioms` per theorem:
- `order_pos`        → `[propext, Quot.sound]`
- `density_pos`      → `[propext, Quot.sound]`
- `densityProd_pos`  → `[propext, Quot.sound]`
- `symmetry_pos`     → `[propext]`
- `symmetryProd_pos` → `[propext]`
- `alphaWeight_pos`  → `[propext, Classical.choice, Quot.sound]` (Classical comes in via `div_pos`'s ordered-field plumbing)

## Faithfulness check
These four theorems are *derived corollaries* of definitions already
in the codebase, not new Butcher entities. No
`extraction/formalization_data/entities/` row was added or modified.

For each:

- **`order_pos : ∀ t, 0 < t.order`** — Direct consequence of the
  `order (mk children) = 1 + orderSum children` recursion: the `1 +`
  makes it positive regardless of subtrees. Captures the
  trivially-true fact that every rooted tree has ≥ 1 vertex (the
  root).

- **`density_pos : ∀ t, 0 < density t`** — Direct consequence of
  Butcher §300's positive-integer definition of γ(t) (product of
  positive subtree-orders). Lean statement matches: same content as
  textbook's implicit positivity claim.

- **`symmetry_pos : ∀ t, 0 < symmetry t`** — Direct consequence of
  Butcher §300's group-order definition of σ(t) (cardinality of a
  non-empty group is ≥ 1). Lean uses the stipulative recursive σ
  (per the file's σ-faithfulness divergence comment, lines 27–57 of
  Section301.lean), so positivity follows from
  `Nat.factorial_pos` + `pow_pos` rather than from group theory.
  This is the same divergence already documented for `σ_recursion`
  in cycle 017; no new gap introduced.

- **`alphaWeight_pos : ∀ t, 0 < alphaWeight t`** — Direct consequence
  of (302a): `r(t)! > 0`, `σ(t) > 0`, `γ(t) > 0`, so the quotient is
  positive. The Lean `alphaWeight` is defined via (302a)'s closed
  form (per the same faithfulness convention as σ — see lines
  240–249 of Section301.lean). Butcher's combinatorial α (count of
  labellings) is also positive (the identity labelling always
  satisfies (i)–(iii)), so the two definitions agree on positivity
  even modulo the combinatorial-equivalence gap.

### Checklist sub-items

- TAUTOLOGY CHECK: All four theorems have conclusion that is *not* a
  hypothesis. Each does real definitional work (unfolding through
  mutual recursions).
- IDENTITY CHECK: None of the proofs are `:= h_*` or `:= id`. Each
  has either a structural `mk children`/list-cons match or an
  explicit term-mode combinator (`div_pos`/`mul_pos`/`Nat.mul_pos`/
  `Nat.factorial_pos`/`pow_pos`).
- DEFINITION SMUGGLING CHECK: No new `structure`/`class` introduced.
- HYPOTHESIS STRENGTH CHECK: Each theorem is stated for *every*
  rooted tree with no auxiliary hypotheses — the textbook statement
  for "positivity of α/σ/γ/r" is also hypothesis-free.

## Dead ends
1. **`by decide` on `symmetryProd_pos [] case`** — failed with a
   free-variable diagnostic because Lean doesn't normalise
   `symmetryProd x✝ []` to `1` under `decide` when `x✝` is a free
   universe-level variable. Fixed by explicitly `show`-ing the
   reduced form `(0 : ℕ) < 1`. Recorded for future positivity-
   on-list-helpers proofs.
2. **Docstring on `mutual` block** — Lean rejects a docstring
   attached to the `mutual` keyword (`unexpected token 'mutual';
   expected 'lemma'`). Docstrings must go on the individual
   inner theorems. The existing `theta_eq_one` block in Section310
   already follows this pattern; the cycle-251 strategy template
   accidentally inverted it.

## Discovery
- The `decide` tactic in mutual-block list base cases with a free
  list parameter (here `full`) needs a manual `show` of the reduced
  goal. Worth remembering for future structural-positivity proofs
  on `…Prod` helpers (e.g. if/when we add `weight_pos` for §312's
  elementary-weight machinery, or positivity lemmas on §316
  Φ-coefficients).
- `pow_pos (h : 0 < a) (n : ℕ) : 0 < a^n` is the working spelling on
  the `ℕ` side; `Nat.pos_pow_of_pos` (which the strategy mentioned)
  has the arguments swapped (`Nat.pos_pow_of_pos n h`). Both are in
  Mathlib but the generic `pow_pos` is closer to the surface API
  and unifies with `mul_pos` chains.
- `exact_mod_cast` handles the `ℕ → ℝ` lift of `Nat.factorial_pos`,
  `symmetry_pos`, `density_pos` cleanly without an explicit
  `Nat.cast_pos.mpr` invocation.

## Suggested next approach
With α(t), σ(t), γ(t), r(t) all known-positive, the natural follow-ups
in order of payoff are:

1. **α(t) for Butcher Table 310(II) — extend the witness battery.**
   Cycle 250 shipped α-values on `vertex`, `cherry`, `broom₃`,
   `[vertex, cherry]`. Adding `mk [cherry]`, `mk [broom₃]`,
   `mk [vertex, vertex, vertex]` would cover the remaining r ≤ 4
   trees. Each is a mechanical `unfold alphaWeight; rw …; norm_num`
   one-liner (~5–10 LOC per tree). Useful non-vacuity for the
   §312 derivation of (310B).

2. **`internalWeight explicitEuler` on `cherry`/`broom₃`.** Cycle 250
   suggested this as option (4). Now that `alphaWeight_pos` rules
   out the trivial-zero-cancellation case, comparing `Φᵢ(t)` to
   `cᵢ^r/γ` on concrete trees becomes a meaningful test of §323's
   internal-order machinery.

3. **`lem:310B` infrastructure** — the elementary-differential-
   weight formula. Genuinely multi-cycle: needs a
   tree-indexed-sum truncation type (`{t : RootedTree // t.order ≤ N}`
   or `TruncatedRootedTreeSum`). Cycle 251's positivity API will
   plug into the absolute-convergence argument once that scaffolding
   exists, but the scaffolding itself is the gating work.

4. **Combinatorial equivalence of α(t)** — still gated on
   `.prover-state/issues/symmetry_group_equivalence.md` and the same
   labelling-count infrastructure as the σ-group equivalence.
   Defer until at least one of (1)–(3) has shipped.

Pure infrastructure cycles like 251 should be cheap to follow up:
the planner can ship (1) as a single low-risk follow-on while the
heavier scaffolding for (3) is being scoped.
