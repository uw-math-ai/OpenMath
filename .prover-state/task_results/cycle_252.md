# Cycle 252 Results

## Worked on
Extended the α-witness battery in `OpenMath/Chapter3/Section301.lean`
with four additional `example` blocks completing Butcher Table 310(II)
through `r ≤ 4`.

Per the strategy: pure additive cycle, no new definitions, no
infrastructure, no Aristotle jobs. Just numerical witnesses
exercising the existing `alphaWeight = r!/(σ·γ)` machinery.

## Approach
Followed the cycle-251 plan verbatim. Read lines 280–356 of
`Section301.lean` to confirm the canonical witness pattern
(`unfold alphaWeight; rw [show order ... = N from rfl, show symmetry
... = M from rfl, show density ... = K from rfl]; norm_num
[Nat.factorial]`). Appended the four new `example` blocks
immediately after the existing `alphaWeight (mk [vertex, cherry])
= 3` example (line 349–354) and before the closing `end RootedTree`
on line 356. Did not modify any existing code.

The four new witnesses (in append order, matching the strategy):

1. `alphaWeight (mk [cherry]) = 1` — 3-ladder `f'(f'f)`,
   r=3 row.  order=3, σ=1, γ=6, α=3!/(1·6)=1.
2. `alphaWeight (mk [vertex, vertex, vertex]) = 1` — broom₄
   `f'''(f,f,f)`, r=4 row. order=4, σ=6, γ=4, α=4!/(6·4)=1.
3. `alphaWeight (mk [broom₃]) = 1` — lifted broom₃
   `f'(f''(f,f))`, r=4 row. order=4, σ=2, γ=12, α=4!/(2·12)=1.
4. `alphaWeight (mk [mk [cherry]]) = 1` — 4-ladder
   `f'(f'(f'f))`, r=4 row. order=4, σ=1, γ=24, α=4!/(1·24)=1.

## Result
SUCCESS — all four witnesses compile axiom-clean.

Verification:
- `lake env lean OpenMath/Chapter3/Section301.lean`: clean exit in
  ~13 s (with NVMe toolchain). No errors, no warnings.
- `lake env lean OpenMath/Chapter3.lean`: clean exit (aggregator).
- Sorry count in `Section301.lean`: 0 (unchanged).
- Tautology scanner sweep: 0 hits.
- All `show ... from rfl` lines accepted by the kernel — every
  hand-traced order/symmetry/density value matched the actual
  definitional reduction. Pre-flight numbers were correct.

Section301.lean now ships **8 α-witnesses** total covering:
- r=1: τ (vertex) ✓
- r=2: cherry ✓
- r=3: broom₃, mk [cherry] (3-ladder) ✓
- r=4: mk [vertex,cherry], mk [vertex,vertex,vertex] (broom₄),
       mk [broom₃] (lifted broom₃), mk [mk [cherry]] (4-ladder) ✓

This saturates Butcher Table 310(II) through r=4 (1 + 1 + 2 + 4 = 8
trees, matching the standard tree counts).

## Faithfulness check
For each new `example` introduced this cycle:

- **Entity ID**: none. These are derived numerical witnesses, not
  new textbook entities. No `extraction/formalization_data/entities/`
  rows added or modified. `lean_status.json` not touched.
- **Textbook source**: Butcher §310 Table 310(II), p. 152. Each tree
  appears in the r=3 or r=4 rows with the listed elementary weight.
- **Lean statement captures**: exact numerical value from (302a).
  No new divergence from the pre-existing α-faithfulness convention
  (closed-form (302a) instead of combinatorial labelling count, see
  lines 285–295 of `Section301.lean`).
- **Tautology check**: each proof unfolds `alphaWeight`, rewrites
  three subterms (order/symmetry/density), and closes a numerical
  identity with `norm_num [Nat.factorial]`. Not vacuous — the
  three `show ... from rfl` rewrites do real definitional work
  via the mutual recursions.
- **Identity check**: no `:= h_*`, `exact h_*`, or `:= id` closers.
  Tautology scanner sweep returns 0.
- **Hypothesis strength check**: no hypotheses. Statements are
  closed-form numerical equalities.
- **Absent theorem check**: no promised-but-missing `sorry`s.
- **Definition smuggling check**: N/A — no new definitions.

## Dead ends
None. Pre-flight pencil-and-paper trace of order/symmetry/density
through the mutual recursions was correct on the first try for all
four witnesses; every `show ... from rfl` line type-checked
without modification.

## Discovery
The mutual recursions for `order`/`symmetry`/`density` decide all
four trees (including the depth-3 nested `mk [mk [cherry]]`) by
`rfl` in a single kernel reduction with no `decide`/`native_decide`
or extra unfolding hints. This confirms the cycle 250 approach of
keeping the recursions structurally simple — `unfold`-free `rfl`
reduction continues to scale through r=4 trees with depth-3 nesting.

For cycle 253 the same `rfl`-then-`norm_num` pattern should extend
unchanged to r=5 trees (eight more witnesses, ~10 LOC each); kernel
reduction time on `mk [mk [cherry]]` (the deepest cycle-252 tree)
showed no measurable slowdown vs the r=2/r=3 cases.

## Suggested next approach
Per the strategy "After this cycle" section, three options for
cycle 253+:

1. **Extend Table 310(II) to r=5** — eight more trees, mechanical.
   Lowest-risk continuation. Same pattern as cycle 252; each
   witness ~7 LOC.
2. **`internalWeight` non-vacuity tests** on `cherry` and `broom₃`
   (cycle 251 option 2). Exercises §323's internal-order machinery
   against the now-rich α/σ/γ data. Slightly more interesting from
   a regression-detection standpoint than (1).
3. **Begin `lem:310B` Phase A** — start writing the truncation type
   `{t : RootedTree // t.order ≤ N}` and absolute-convergence
   scaffolding. Multi-cycle scope. Higher risk, higher payoff.

Recommendation: do (1) or (2) one more time as a momentum cycle,
then pivot to (3). Continuing to defer (3) past cycle 254 risks
the witness-battery work becoming a treadmill instead of a
foundation for the §310B/§312B downstream theorems.
