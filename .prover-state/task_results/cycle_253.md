# Cycle 253 Results

## Worked on

§310 Butcher Table 310(II) row r=5 — α-witness battery for all 9
unordered rooted trees of order 5. Appended 9 `example` blocks to
`OpenMath/Chapter3/Section301.lean` between line 403 (the cycle 252
4-ladder witness) and `end RootedTree`. This saturates the last full
row of Butcher Table 310(II), completing the project's reproduction of
the textbook's small-tree data table through r ≤ 5.

## Approach

Mechanical extension of the cycle 252 pattern. For each tree `T`:

```lean
example : alphaWeight T = R := by
  unfold alphaWeight
  rw [show order T = N from rfl,
      show symmetry T = M from rfl,
      show density T = K from rfl]
  norm_num [Nat.factorial]
```

The 9 trees and their (r, σ, γ, α) tuples (verified by hand-tracing
the structural recursions `order` / `symmetryProd` / `density` before
writing the file):

1. `mk [mk [mk [cherry]]]` (5-ladder): (5, 1, 120, 1)
2. `mk [vertex, vertex, vertex, vertex]` (broom₅): (5, 24, 5, 1)
3. `mk [cherry, cherry]`: (5, 2, 20, 3)
4. `mk [cherry, vertex, vertex]`: (5, 2, 10, 6)
5. `mk [mk [vertex, vertex, vertex]]` (lifted broom₄): (5, 6, 20, 1)
6. `mk [mk [broom₃]]`: (5, 2, 60, 1)
7. `mk [mk [vertex, cherry]]` (lifted asym r=4): (5, 1, 40, 3)
8. `mk [broom₃, vertex]`: (5, 2, 15, 4)
9. `mk [mk [cherry], vertex]` (3-ladder + leaf): (5, 1, 30, 4)

α sum = 1+1+3+6+1+1+3+4+4 = 24 (= 5! / 5, expected for the order-5
labelled-rooted-tree count divided by trees-per-equivalence-class).

No fallbacks needed: every `show ... from rfl` reduced under kernel
computation without measurable slowdown, including the depth-4
5-ladder. No Aristotle submissions (the strategy explicitly said
none were planned for this cycle).

## Result

**SUCCESS** — all 9 r=5 α-witnesses ship. Verification:

1. `lake env lean OpenMath/Chapter3/Section301.lean` — clean exit
   in **7.7 s**.
2. `lake env lean OpenMath/Chapter3.lean` — aggregator clean in
   **7.5 s**.
3. `grep -c sorry OpenMath/Chapter3/Section301.lean` — **0**
   (unchanged from cycle 252).
4. Tautology scanner sweep
   (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on the file) —
   **0 matches**.

The depth-4 5-ladder (`mk [mk [mk [cherry]]]`) compiled fine under
plain `rfl`; the strategy's contingency Fallback A/B/C were not
triggered.

## Faithfulness check

No new `def` / `theorem` / `structure` introduced. Only `example`
blocks, each exercising the already-shipped `alphaWeight` definition
(Butcher equation (302a), `Section301.lean`:305) on a specific
`RootedTree` term. Each is a numerical sanity-check, not a new
mathematical claim.

The σ-faithfulness divergence (recursive (301b) definition vs
textbook §300 automorphism-group definition) is unchanged and
documented in `Section301.lean`'s file docstring lines 27–57 and
`.prover-state/issues/symmetry_group_equivalence.md`. The α-faithfulness
divergence (closed-form (302a) vs combinatorial labelling count of
§302 (i)–(iii)) is unchanged and documented at
`Section301.lean`:271–295.

The 9 α values were cross-checked against Butcher Theorem 301A's
recursive formulas (r-, σ-, γ-recursion) and the (302a) closed form
before writing the proof goals. Each `show ... from rfl` then
mechanically confirms the calculation against the recursive Lean
definitions; if any α value had been wrong, the corresponding `rfl`
or `norm_num` would have failed.

## Dead ends

None. The cycle was a pure mechanical extension of the cycle 252
pattern; no exploratory work was required, and no Aristotle calls
were made (strategy explicitly directed none).

## Discovery

* **Kernel reduction at depth 4 is fine.** The 5-ladder
  `mk [mk [mk [cherry]]]` reduced its (order, σ, γ) triple by `rfl`
  in well under a second. The cycle 252 worker's depth-3 confidence
  extends to depth 4 without issue. This is encouraging for
  cycle 254 work on `lem:310B` if explicit small-tree term-rewriting
  is needed.

* **`α(t)` sum for row r=5 is 24 = 5!/5.** The Butcher α-coefficient
  identity `Σ_{|t|=r} α(t) · σ(t) · γ(t) = r! · #{labelled trees
  on r vertices per orbit}` was not directly verified here, but the
  raw sum of α-values across the 9 r=5 trees comes out to 24, which
  matches the count `r^(r-2) · r! / r!` style identities. Worth a
  sanity check when `lem:310B` proof work begins — this row of the
  table is the regression oracle.

* **`symmetryProd` walks behaved as expected** for all asymmetric
  trees (`mk [cherry, vertex, vertex]`, `mk [broom₃, vertex]`,
  `mk [mk [cherry], vertex]`). The list-order-dependent
  recursion did not require any ordering adjustment beyond what the
  strategy specified. The cycle 252 worker's notes on the
  recursion's walk semantics are accurate.

## Suggested next approach

Per the cycle 253 strategy's explicit pivot signal: **cycle 254
should target `lem:310B` Phase A**, the truncation-type +
absolute-convergence scaffolding for B-series.

Concrete sub-phases for cycle 254 (or for the planner to break
across multiple cycles):

1. Define `TruncatedRootedTree (N : ℕ) := { t : RootedTree // t.order ≤ N }`.
2. Build `Fintype (TruncatedRootedTree N)` — the finite count of
   rooted trees with order ≤ N. This needs an enumeration helper:
   given `Fintype (TruncatedRootedTree (N-1))`, all order-N trees
   are root-products of partitions of children with combined
   order ≤ N-1. The 9 r=5 trees shipped this cycle serve as
   regression data: any `Fintype` instance must enumerate them.
3. Begin `lem:310B` statement: the truncated B-series
   `Σ_{t : TruncatedRootedTree N} (h^t.order / t.order!) · α(t) ·
   F[t](y₀)` converges absolutely as N → ∞ for `h` sufficiently
   small.

If `lem:310B` Phase A is judged too risky for cycle 254, fallback
targets per the strategy:

* `internalWeight` non-vacuity (cycle 252 option (2)) — needs a new
  RKTableau instance (e.g. Heun, implicit midpoint) and is more
  invasive than it sounds.
* `lem:312B` (Elementary Weight Summation Formula) — depends on
  `lem:310B` infrastructure, likely blocked.
* `thm:311B` (Taylor expansion exact-solution formula) — generalises
  cycle 248's `lem_311A_order_one` to order p; multi-cycle.

The α-witness saturation cycle 253 ships is the right inflection
point: maximum α-data with minimum cycle treadmill. **Do not extend
the witness battery to r=6** — Butcher Table 310(II) stops at r=5,
and the r=6 count is 20 trees (treadmill territory). Pivot to
`lem:310B` Phase A now.
