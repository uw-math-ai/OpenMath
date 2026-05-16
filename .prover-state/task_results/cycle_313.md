# Cycle 313 Results

## Worked on

`thm:342C` clause (342m) `B(2s) ∧ C(s) ⇒ E(s, s)` for arbitrary
`RKTableau` — the *generic* algebraic bridge generalising cycle 312's
specialisation `butcherGaussLegendreRK_satisfiesE`. Shipped as
`OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesC`
in `OpenMath/Chapter3/Section321.lean`, alongside two non-vacuity
witnesses (one in `Section321.lean` via `gaussLegendre1Stage`, one in
`Section342.lean` parametrically over `butcherGaussLegendreRK n`).

## Approach

Cycle 312's `butcherGaussLegendreRK_satisfiesE` proof was already
*purely algebraic* in the abstract B/C/E predicates — it never
inspected the specific Gauss–Legendre structure. So cycle 313 is a
**near-verbatim port** of that proof body with three textual
substitutions:

1. `butcherShiftedLegendre_collocationA n i j` → `M.A i j`
2. `butcherShiftedLegendre_zeros n j` → `M.c j`
3. `butcherShiftedLegendre_quadratureWeights n i` → `M.b i`

…and two deletions:

1. The `have hn : 0 < n := lt_of_lt_of_le hl1 hl` step is gone (the
   abstract `hB : M.SatisfiesB (2 * s)` hypothesis has no
   `0 < s` precondition; cycle 312 only needed `hn` because
   `butcherGaussLegendreRK_satisfiesB` *itself* required it).
2. The opening `show ∑ i, ∑ j, butcherShiftedLegendre_... = ...`
   line that unfolded the Gauss-Legendre projections is unnecessary —
   the abstract version stays at `M.A`/`M.b`/`M.c` throughout.

Apart from these, the four-step tactic skeleton is identical:

* **Step 1**: pull `hC i l hl1 hl` per row into `hCi`.
* **Step 2**: `h_outer` — factor the inner `j`-sum down to
  `M.b i * M.c i ^ (k - 1) * (∑ⱼ M.A i j * M.c j ^ (l - 1))` via
  `Finset.mul_sum` + `Finset.sum_congr rfl` + `ring`; apply `hCi i`;
  combine the powers `c i ^ (k - 1) * c i ^ l = c i ^ ((k+l)-1)` via
  the `(k-1)+l = (k+l)-1` rewrite + `pow_add`; close with `field_simp`.
* **Step 3**: `hkl_lo : 1 ≤ k + l` and `hkl_hi : k + l ≤ 2 * s` via
  `omega`; invoke `hB (k+l) hkl_lo hkl_hi`.
* **Step 4**: `push_cast; field_simp` closes
  `(1/l) * (1/(k+l)) = 1/(l * (k+l))`.

For the non-vacuity witnesses:

* `Section321.lean`: an *abstract-route* `gaussLegendre1Stage.SatisfiesE 1 1`
  example calling the new theorem with `B(2)` and `C(1)` hypotheses
  proved inline via `interval_cases k` (same body as the existing
  hand-built `gaussLegendre1Stage.SatisfiesB 2` / `SatisfiesC 1`
  examples a few lines above). The existing hand-built
  `SatisfiesE 1 1` example is left untouched — having both forms makes
  the regression check meaningful.
* `Section342.lean`: a parametric example
  `(butcherGaussLegendreRK n).SatisfiesE n n` derived through the new
  abstract bridge by combining cycle 309's `_satisfiesB` and cycle
  310's `_satisfiesC`. This is the *abstract-route* re-derivation of
  cycle 312's `butcherGaussLegendreRK_satisfiesE` (the direct theorem
  remains in place as the cycle 312 regression-witness).

## Result

**SUCCESS** — the theorem compiles axiom-clean and both non-vacuity
witnesses close cleanly.

### Verification protocol

```text
$ lake env lean OpenMath/Chapter3/Section321.lean           # exit 0
$ lake build OpenMath.Chapter3.Section321                   # ✔ 1941 jobs
$ lake env lean OpenMath/Chapter3/Section342.lean           # exit 0
$ lake build OpenMath.Chapter3                              # ✔ 2938 jobs

$ grep -c sorry OpenMath/Chapter3/Section321.lean           # 0
$ grep -c sorry OpenMath/Chapter3/Section342.lean           # 0

# Axiom check on the new theorem
$ #print axioms OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesC
  [propext, Classical.choice, Quot.sound]
# No sorryAx, no axiom/constant declarations.

# Cycle 312 theorem unchanged + axiom-clean (regression check)
$ #print axioms OpenMath.Chapter3.Section342.butcherGaussLegendreRK_satisfiesE
  [propext, Classical.choice, Quot.sound]
```

Note that the cycle 312 axiom set was previously listed as
`[propext, sorryAx, Classical.choice, Quot.sound]` in `plan.md`'s
`lem:342B` row (the `sorryAx` was *inherited from upstream cycle 301*'s
`_rootsInIoo_card_ge`). The freshly-verified axiom output above shows
the leak is gone — but the new abstract bridge in `Section321.lean`
*never touches* `Section342`'s Gauss-Legendre infrastructure, so its
axiom set is naturally clean independent of any upstream `sorryAx`
status.

## Faithfulness check

### New theorem `OpenMath.Chapter3.Section312.RKTableau.satisfiesE_of_satisfiesB_satisfiesC`

* **Entity ID**: `thm:342C` (clause (342m))
* **Textbook statement** (quoted from
  `extraction/formalization_data/entities/thm_342C.json`,
  `statement_latex` field):

  > `B(2s) \land C(s) \Rightarrow E(s, s)`, \label{eq:342m}

* **Lean statement**:

  ```lean
  theorem satisfiesE_of_satisfiesB_satisfiesC {s : ℕ}
      (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
      (hC : M.SatisfiesC s) :
      M.SatisfiesE s s
  ```

* **Captures**: *same content*. The Lean implication matches Butcher's
  flat implication exactly: same hypothesis pack (`B(2s) ∧ C(s)`,
  expressed as separately-named hypotheses `hB`/`hC`), same conclusion
  (`E(s, s)`).
* **Tautology check**: ✓ The conclusion `M.SatisfiesE s s` does not
  appear among the hypotheses (which are `M.SatisfiesB (2*s)` and
  `M.SatisfiesC s` — three distinct predicates from §321).
* **Identity check**: ✓ The proof is structural — four `have` /
  `rw` / `apply` steps — not a one-liner `:= h_*` re-export.
* **Definition smuggling check**: ✓ no new `def`, `class`, or
  `structure`. Only a `theorem`. The §321 B/C/E predicates were
  audited in cycle 306 and confirmed to faithfully encode Butcher's
  §321 (321a)/(321b)/(321c) equations.
* **Hypothesis strength check**: ✓ Hypotheses match Butcher exactly.
  Cannot weaken `SatisfiesB (2*s)` to `SatisfiesB s` (the `k + l ≤ 2*s`
  step requires the full `2*s` range). Cannot weaken `SatisfiesC s`
  to a lower index (we need C at the full exponent `s`, since
  `1 ≤ l ≤ s`).
* **No extra hypotheses**: ✓ no `0 < s` precondition. At `s = 0`,
  `SatisfiesE 0 0` is vacuous (no `k` satisfies `1 ≤ k ≤ 0`).

### New non-vacuity `example`s (no name, no faithfulness obligation)

Two unnamed `example`s in `Section321.lean` and `Section342.lean`
exercising the new bridge. Both are inhabitation witnesses for
B/C/E; no new mathematical content claimed.

## Dead ends

None. The strategy file (cycle 312 task results report) had already
worked out the exact substitution recipe, and the port was mechanical.
The only minor wrinkle was that `lake env lean Section321.lean` does
*not* update `.lake/build/lib/lean/OpenMath/Chapter3/Section321.olean`
(only typechecks), so the first attempt to compile `Section342.lean`
failed with `invalidField` errors. Resolved by running
`lake build OpenMath.Chapter3.Section321` to refresh the olean before
re-compiling `Section342.lean`.

## Discovery

* **The four "algebraic" clauses of `thm:342C` (342m/342n/342o/342p)
  can be shipped without touching `Section342.lean`** — they live
  naturally as theorems on the abstract `RKTableau` in
  `Section321.lean`, alongside the predicate definitions. The
  `Section342` infrastructure becomes a *consumer* of these abstract
  clauses, not a producer. Cycle 313 just needed to add ~80 lines of
  `Section321.lean` and 1 example in `Section342.lean`.
* **Cycle 312's proof was already maximally portable.** The substitution
  recipe in cycle 313's strategy (§C) was exact: 3 textual
  substitutions, 2 deletions, no other changes. This suggests cycle
  311's `D(n)` proof (which used IBP + polynomial antiderivative)
  is *not* similarly portable — that proof inspects the specific
  Lagrange-basis polynomial structure of the Gauss–Legendre tableau.
  A generic `B(2s) ∧ D(s) ⇒ E(s, s)` (clause 342o) would need a
  separate, sum-swap-based proof (sketched in cycle 313 strategy §D).
* **`lake env lean` does not update `.olean` files** on this build
  setup; only `lake build` does. When iterating across files (e.g.
  changing `Section321.lean` then verifying `Section342.lean` picks
  it up), use `lake build` not `lake env lean` to ensure dependencies
  see the new definitions.

## Suggested next approach

Two natural cycle-314 follow-ups, ranked by confidence:

1. **Clause (342o) `B(2s) ∧ D(s) ⇒ E(s, s)`** — the partner algebraic
   clause sketched in cycle 313 strategy §D. Sum-swap LHS via
   `Finset.sum_comm`, apply `D(s)` per column `j` at exponent `k`,
   collapse via `B(2s)` at exponents `l` and `k + l`, arithmetic
   close `(1/k)(1/l - 1/(k+l)) = 1/(l(k+l))`. Estimated ~90 LOC.
   No new infrastructure needed; pure algebraic composition like
   (342m). High-confidence single-cycle target.

2. **Clauses (342n)/(342p) — Vandermonde converses**. Need to prove
   that the `b`-weighted Vandermonde matrix `V[i, k] := b_i · c_i^(k-1)`
   over `Fin s × Fin s` is non-singular (assuming the `c_i` are
   distinct and the `b_i` are nonzero — both true for Gauss–Legendre
   but not all tableaux). Then `B(2s) ∧ E(s,s) ⇒ C(s)` follows by
   left-multiplying the matrix of `C(s)` defect quantities and
   inverting. Likely ~150 LOC each. Could be a single combined cycle
   (the proof skeleton is symmetric between C/D).

The G(2s)-involving clauses (342j)/(342k)/(342l) remain blocked on
`thm:314A` elementary-differential infrastructure — multi-cycle work
that should be scoped separately.

A third option: **pivot to a fresh §342 entity**. `thm:344A` (Radau /
Lobatto methods) consumes the §321 B/C/D/E predicates as building
blocks and would now benefit from the abstract `(342m)` bridge for
the same `E(n,n)` step. But this is a bigger lift; (342o) is the
better next-cycle target.
