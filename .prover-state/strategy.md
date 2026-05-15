# Cycle 252 strategy — extend α(t) witness battery for Butcher Table 310(II)

## TL;DR

Ship four more axiom-clean `alphaWeight` witnesses in
`OpenMath/Chapter3/Section301.lean`, completing the `r ≤ 4` rows of
Butcher Table 310(II). This is option (1) from cycle 251's "Suggested
next approach" — the safest, highest-confidence single-cycle
deliverable that builds directly on cycles 250/251.

No new definitions, no new infrastructure, no Aristotle jobs needed.
Pure numerical witnesses exercising the existing
`alphaWeight = r!/(σ·γ)` machinery.

## State at HEAD

- Branch tip: `ccd6018 Cycle 251 — §302 alphaWeight_pos + density/symmetry/order positivity SHIPPED.`
- `OpenMath/Chapter3/Section301.lean`: 358 LOC, 0 sorries, axiom-clean.
- Existing α witnesses (cycle 250):
  - `alphaWeight_vertex : alphaWeight (mk []) = 1` (theorem; r=1 row)
  - `example : alphaWeight vertex = 1` (r=1, alias)
  - `example : alphaWeight cherry = 1` (r=2 row)
  - `example : alphaWeight broom₃ = 1` (r=3 row, σ=2)
  - `example : alphaWeight (mk [vertex, cherry]) = 3` (r=4 row, asymmetric, σ=1, γ=8)
- Existing positivity (cycle 251): `order_pos`, `density_pos`,
  `densityProd_pos`, `symmetry_pos`, `symmetryProd_pos`, `alphaWeight_pos`
  — all axiom-clean.
- No pending Aristotle results, no open blockers requiring infra work.

## Why this target

1. **Builds momentum on the §302/§310/§311/§312 cluster** (cycles
   248–251 have been in this cluster).
2. **Zero infrastructure risk** — every new witness is a mechanical
   `unfold alphaWeight; rw [...]; norm_num [Nat.factorial]` following
   the exact pattern of the cycle 250 examples at lines 330–354.
3. **Completes Butcher Table 310(II) through r=4** — by adding the
   four remaining r=3 / r=4 trees with r ≤ 4 in the textbook table,
   the witness battery becomes a useful regression-test fixture for
   any future definitional change to `order`/`symmetry`/`density`/
   `alphaWeight`.
4. **Faithfulness check stays clean** — no new entities, no new
   definitions, just numerical examples validating the cycle 250
   `alphaWeight` definition against the textbook table.

## Concrete deliverables — four new `example` blocks

All four go in `OpenMath/Chapter3/Section301.lean`, immediately after
the existing `example : alphaWeight (mk [vertex, cherry]) = 3` (line
349–354), inside `namespace RootedTree`. **DO NOT modify any
existing code.** Just append four new examples before the closing
`end RootedTree` on line 356.

### Witness 1 (r=3): `alphaWeight (mk [cherry]) = 1`

The 3-ladder tree: root with a cherry as its only child.
Computed values: order = 3, σ = 1, γ = 6, α = 3!/(1·6) = 1.

```lean
/-- Non-trivial witness: the 3-ladder `mk [cherry]` (root with a cherry
as only child) has `α = 1`. This is row r=3, second entry of Butcher
Table 310(II) — the depth-2 chain `f'(f'f)`. Order 3, symmetry 1
(single-child chain has no automorphism), density 3·2·1 = 6,
so α = 3!/(1·6) = 1. -/
example : alphaWeight (mk [cherry]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [cherry]) = 3 from rfl,
      show symmetry (mk [cherry]) = 1 from rfl,
      show density (mk [cherry]) = 6 from rfl]
  norm_num [Nat.factorial]
```

### Witness 2 (r=4): `alphaWeight (mk [vertex, vertex, vertex]) = 1`

The broom₄ tree: root with three leaves. Computed values:
order = 4, σ = 3! = 6 (three indistinguishable leaves), γ = 4,
α = 4!/(6·4) = 1.

```lean
/-- Non-trivial witness: the broom-of-4 tree `mk [vertex, vertex, vertex]`
(root with three leaves) has `α = 1`. This is row r=4, fourth entry of
Butcher Table 310(II) — the `f'''(f, f, f)` tree. Order 4, symmetry 3! = 6
(three indistinguishable leaves), density 4·1·1·1 = 4, so
α = 4!/(6·4) = 1. -/
example : alphaWeight (mk [vertex, vertex, vertex]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [vertex, vertex, vertex]) = 4 from rfl,
      show symmetry (mk [vertex, vertex, vertex]) = 6 from rfl,
      show density (mk [vertex, vertex, vertex]) = 4 from rfl]
  norm_num [Nat.factorial]
```

### Witness 3 (r=4): `alphaWeight (mk [broom₃]) = 1`

The lifted broom₃ tree: root with broom₃ as only child.
Computed values: order = 4, σ = 2 (broom₃'s two leaves remain
indistinguishable when lifted), γ = 12, α = 4!/(2·12) = 1.

```lean
/-- Non-trivial witness: the lifted broom-3 tree `mk [broom₃]`
(root with `broom₃ = [τ,τ]` as only child) has `α = 1`. This is
row r=4, third entry of Butcher Table 310(II) — the depth-2 tree
`f'(f''(f,f))`. Order 4, symmetry 2 (broom₃'s two leaves remain
indistinguishable when lifted), density 4·3·1·1 = 12, so
α = 4!/(2·12) = 1. -/
example : alphaWeight (mk [broom₃]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [broom₃]) = 4 from rfl,
      show symmetry (mk [broom₃]) = 2 from rfl,
      show density (mk [broom₃]) = 12 from rfl]
  norm_num [Nat.factorial]
```

### Witness 4 (r=4): `alphaWeight (mk [mk [cherry]]) = 1`

The 4-ladder tree: chain of depth 4. Computed values: order = 4,
σ = 1, γ = 24, α = 4!/(1·24) = 1.

```lean
/-- Non-trivial witness: the 4-ladder `mk [mk [cherry]]` (chain of
depth 4) has `α = 1`. This is row r=4, first entry of Butcher Table
310(II) — the deeply nested `f'(f'(f'f))`. Order 4, symmetry 1
(single-child chain has no symmetry), density 4·3·2·1 = 24, so
α = 4!/(1·24) = 1. -/
example : alphaWeight (mk [mk [cherry]]) = 1 := by
  unfold alphaWeight
  rw [show order (mk [mk [cherry]]) = 4 from rfl,
      show symmetry (mk [mk [cherry]]) = 1 from rfl,
      show density (mk [mk [cherry]]) = 24 from rfl]
  norm_num [Nat.factorial]
```

## Pre-flight verification of the numbers

Each tree's order/symmetry/density values were verified during
strategy authoring by hand-tracing the mutual recursions in
`Section301.lean` (order via `orderSum`, density via `densityProd`
at lines 134–139, symmetry via `symmetryProd` at lines 204–219). The
`show ... from rfl` lines will fail at compile time if any value is
wrong, but the table below is what the worker should expect:

| Tree | order | symmetry | density | α = r!/(σ·γ) |
|---|---|---|---|---|
| `mk [cherry]`                  | 3 | 1 | 6  | 6/6 = 1   |
| `mk [vertex, vertex, vertex]`  | 4 | 6 | 4  | 24/24 = 1 |
| `mk [broom₃]`                  | 4 | 2 | 12 | 24/24 = 1 |
| `mk [mk [cherry]]`             | 4 | 1 | 24 | 24/24 = 1 |

Trace details for the trickiest ones:

- **`mk [vertex, vertex, vertex]`** symmetry: `symmetryProd [v,v,v]
  [v,v,v]`. Cursor `[v,v,v]`: head=v, rest=[v,v], v∈rest → recurse.
  Cursor `[v,v]`: head=v, rest=[v], v∈rest → recurse. Cursor `[v]`:
  head=v, rest=[], v∉rest → emit `Nat.factorial ([v,v,v].count v) *
  symmetry v ^ count * symmetryProd [v,v,v] []`. `count v = 3`,
  `symmetry v = 1`, so the emitted factor is `3! · 1³ · 1 = 6`.
- **`mk [broom₃]`** symmetry: `symmetryProd [broom₃] [broom₃]`.
  Cursor `[broom₃]`: head=broom₃, rest=[], so emit `Nat.factorial
  ([broom₃].count broom₃) * symmetry broom₃ ^ count * 1`.
  `count = 1`, `symmetry broom₃ = 2` (already established in the
  existing cycle-250 witness at line 337–342), so factor is
  `1! · 2¹ · 1 = 2`.
- **`mk [mk [cherry]]`** density: recursive
  `4 · density (mk [cherry]) · 1 = 4 · 6 · 1 = 24`.

If any `show … from rfl` line fails, the most likely culprit is
either (a) a miscount in `symmetry`'s `Nat.factorial · pow · ...`
recursion, or (b) a missing `densityProd` step. Re-trace through
`Section301.lean` lines 204–219 (symmetry) and 134–139 (density)
with the explicit children list to find the error.

## Workflow

1. **Read** `OpenMath/Chapter3/Section301.lean` lines 305–356 to
   confirm the existing pattern. The first example block at line 330
   (`alphaWeight cherry = 1`) is the canonical template.
2. **Append** the four new `example` blocks in the order Witness 1
   → Witness 4 above, immediately after line 354 (`norm_num
   [Nat.factorial]` of the `alphaWeight (mk [vertex, cherry]) = 3`
   example) and before the closing `end RootedTree` on line 356.
3. **Verify** via `lake env lean OpenMath/Chapter3/Section301.lean`.
   Expected clean exit. If any `show … from rfl` line errors, fix
   the integer values per the pre-flight table above.
4. **Check Chapter3 aggregator**: `lake env lean OpenMath/Chapter3.lean`.
   Expected clean exit. (Examples don't produce named symbols, so no
   downstream impact.)
5. **Sorry sweep** (sanity, even though we're only adding examples):

   ```
   grep -c sorry OpenMath/Chapter3/Section301.lean    # expect 0
   ```

6. **Tautology scanner sweep**:

   ```
   rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section301.lean
   # expect zero hits
   ```

7. **Write `.prover-state/task_results/cycle_252.md`** documenting
   the four new witnesses + their computed values + faithfulness
   notes (see "Faithfulness check" section below).

## What NOT to try

- **Do NOT** define new `RootedTree` constants (e.g.
  `def ladder := mk [cherry]`, `def broom₄ := mk [vertex, vertex, vertex]`).
  Keep the witnesses inline with `mk [...]` notation. Adding named
  definitions invites future naming-clash issues and is out of scope
  for a witness-battery cycle. If cycle 253+ wants to add named
  constants for downstream readability, that's a separate decision.

- **Do NOT** modify the existing cycle 250/251 theorems or examples.
  Pure additive cycle. Touching `alphaWeight_vertex`, `alphaWeight_pos`,
  `density_pos`, `symmetry_pos`, or any existing example risks
  introducing regressions for no benefit.

- **Do NOT** attempt `lem:310B` (Elementary Differential Weight
  Formula). It needs a truncation type
  (`{t : RootedTree // t.order ≤ N}`) and absolute-convergence
  infrastructure — multi-cycle. The cycle 251 task results
  flag this explicitly as gated on "tree-indexed-sum truncation type".

- **Do NOT** attempt the combinatorial-α equivalence (showing the
  closed-form (302a) matches Butcher's labelling count). Same
  multi-cycle gating as the σ-symmetry-group equivalence in
  `.prover-state/issues/symmetry_group_equivalence.md`.

- **Do NOT** attempt `thm:302A` / `thm:302B` / `thm:302C`
  (generating-function and enumeration theorems). These need
  generating-function infrastructure (`PowerSeries`-based, similar
  to cycle 237's §441B work) and would be 2–4 cycle deliverables.

- **Do NOT** submit anything to Aristotle. These witnesses close
  in seconds each via `norm_num [Nat.factorial]`. Aristotle is
  unnecessary and would burn project slots.

- **Do NOT** raise `maxHeartbeats`. Each witness is ~5 LOC and
  `norm_num` handles the arithmetic trivially.

- **Do NOT** introduce sorries or `axiom` declarations.

- **Do NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`.
  The GPFS pathology against §441 has reproduced on 43+ consecutive
  attempts since cycle 182 (per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`). Section441
  has nothing to do with cycle 252's target — skip the smoke test
  entirely.

- **Do NOT** edit `scripts/autonomous_loop.py` or anything related
  to the tautology scanner / prompt-builder. Loop-maintainer
  territory.

- **Do NOT** rename `h_*` → `h*` in existing code as a tautology-
  scanner workaround. This cycle's new examples should already use
  hypothesis-free `unfold/rw/norm_num` proofs that don't trip the
  scanner.

## Faithfulness check (pre-commit)

For each of the four new examples:

- **Entity ID**: none. These are derived numerical witnesses, not
  new textbook entities. No `extraction/formalization_data/entities/`
  row to add or modify. **DO NOT** update `lean_status.json` (these
  are not new entities and the existing entries for `alphaWeight` /
  `def:302A` / etc. are unaffected by adding witnesses).
- **Textbook source**: Butcher §310 Table 310(II) (the elementary-
  differential table, page 152). Each tree appears in the r=3 or
  r=4 rows.
- **Lean statement captures**: exact numerical value from (302a).
  No new divergence — the existing α-faithfulness divergence
  (combinatorial vs closed-form definition; see lines 285–295 of
  `Section301.lean`) applies but is unchanged by adding these
  witnesses.
- **Tautology check**: each proof is non-trivial — it unfolds
  `alphaWeight`, rewrites three subterms (order, symmetry, density),
  and closes a numerical identity with `norm_num`. Not vacuous (the
  three `show ... from rfl` rewrites are doing real definitional
  work via the mutual recursions).
- **Identity check**: no `:= h_*` / `exact h_*` / `:= id` closers.
- **Hypothesis strength check**: no hypotheses. Statements are
  closed-form numerical equalities.
- **Absent theorem check**: no promised-but-missing `sorry`s.

## Score expectation

If all four witnesses land cleanly:
- New content: 4 examples (additive to the existing 4 cycle-250
  examples).
- Sorry delta: 0 (unchanged).
- Axiom-clean status: maintained.
- Regression risk: zero (additive, no edits to existing code).

Expected supervisor score: +2 (clean shipping cycle).

Worst case (e.g. one of the `show … from rfl` lines fails due to a
miscount): drop that witness, ship the other three, file a one-line
addendum to `cycle_252.md` noting the discrepancy and either fix the
arithmetic next cycle or escalate to an issue file if the recursion
genuinely behaves unexpectedly. Score floor: +1.

## After this cycle

Once Butcher Table 310(II) is saturated through r=4, the natural
next-cycle (cycle 253+) targets are:

1. **Extend to r=5** (eight more trees, ~10 LOC each). Another
   safe additive cycle.
2. **Pivot to `internalWeight` non-vacuity tests** on `cherry`,
   `broom₃` (per cycle 251's option 2 — exercises §323's
   internal-order machinery against the now-rich α/σ/γ data).
3. **Begin `lem:310B` scoping** — start writing the truncation type
   `{t : RootedTree // t.order ≤ N}` infrastructure as a Phase A
   deliverable. Multi-cycle.

These are cycle 253+ decisions. Do not pre-commit to them now.
