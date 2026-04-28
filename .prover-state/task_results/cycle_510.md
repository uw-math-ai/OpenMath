# Cycle 510 Results

## Worked on

Butcher §381 right-padding primitive in `OpenMath/ButcherGroup.lean`:

- `ButcherTableau.padRight` (the primitive itself)
- Seven `@[simp]` projection lemmas for `b`, `c`, and `A`
  (`padRight_b_castAdd`, `padRight_b_natAdd`, `padRight_c_castAdd`,
  `padRight_c_natAdd`, `padRight_A_castAdd_castAdd`,
  `padRight_A_castAdd_natAdd`, `padRight_A_natAdd`)
- `padRight_weightsSum`
- `padRight_cSum`
- `padRight_elementaryWeight_castAdd` — substantive
- `padRight_bSeries` — stretch lemma

## Approach

Added the new `### §381 stage padding` section at the end of
`OpenMath/ButcherGroup.lean`, immediately before `end ButcherTableau`.
The padding primitive uses two layers of `Fin.addCases` for `A` and one
layer each for `b` and `c`, defaulting to `0` on the pad block, exactly
as the strategy prescribes.

Sorry-first plan: write all targets with `:= by sorry`, compile, then
batch to Aristotle. The unblocking surprise was that the scaffold
compiled **with no sorries** on the first attempt: each `@[simp]`
projection lemma reduces by a single `simp [padRight]`, the two sanity
sums close with `Fin.sum_univ_add` plus `simp`, the substantive
`padRight_elementaryWeight_castAdd` lemma transplants the cycle 497
`BTree.rec` motive split (with `motive_2` over `List BTree`) and
finishes by reducing the pad-block sum to zero via the new
`padRight_A_natAdd` simp lemma, and the stretch `padRight_bSeries`
follows the same `Fin.sum_univ_add` shape with the new
`padRight_b_natAdd` killing the pad block.

Because the scaffold was already sorry-free, I deliberately did **not**
submit Aristotle jobs — there were no sorries to delegate, and recent
cycles (505–509) have shown that submitting on a saturated queue just
returns 429s. This keeps Aristotle quota for cycles where it is
actually load-bearing, in line with the cycle 509 lesson.

## Result

SUCCESS. All five strategy steps **plus the stretch goal** are
sorry-free on the first compile.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/ButcherGroup.lean
# (no output)
rg -n "sorry" OpenMath/ButcherGroup.lean
# (no matches)
```

`lake env lean OpenMath/ButcherGroup.lean` exits 0; `rg` finds no
`sorry`s anywhere in the file. Two extra `@[simp]` `A`-projection
lemmas (`padRight_A_castAdd_castAdd`, `padRight_A_castAdd_natAdd`,
`padRight_A_natAdd`) were added beyond the strategy's explicit ask
because they are required to discharge the inner-sum reduction in
`padRight_elementaryWeight_castAdd` and they are zero-cost simp
lemmas of the same shape as the `b`/`c` projections.

`plan.md`'s §381 sub-bullet now records the new `padRight` API and
flags `IsRKEquivalentExt` as the natural next-cycle headline.
`## Current Target` was **not** rotated, per the strategy.

## Dead ends

None. The cycle 497 `BTree.rec` motive split transplants directly to
the cross-stage-count case once the pad-block `A` rows are known to be
zero, so no `lean_multi_attempt` exploration was needed.

## Discovery

The padding primitive's `A` matrix has two cleanly disjoint structural
zeros (the entire `natAdd` row block, and the pad column inside any
preserved row), and exposing each as its own `@[simp]` lemma lets the
inductive step reduce by a single `simp` after `Fin.sum_univ_add`.

The cycle-497 nested `BTree.rec` motive pattern generalizes cleanly to
"two tableaux on different stage counts where one is a stage-padded
embedding of the other": the only change versus the same-stage-count
version is that the inner sum splits into a preserved block and a zero
pad block, both of which collapse via the new projection simp lemmas.

## Suggested next approach

Cycle 511 should land the `IsRKEquivalentExt` cross-stage-count
relation that this cycle's primitive now unblocks. The shape:

1. `def QuotEquiv.padRight {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
   QuotEquiv (s + n)` — lift `ButcherTableau.padRight` through the
   quotient, with the obvious congruence on relabeling permutations.
2. `def IsRKEquivalentExt {s u : ℕ} (q₁ : QuotEquiv s)
   (q₂ : QuotEquiv u) : Prop := q₁.padRight (max s u - s) =
   q₂.padRight (max s u - u)` (or the analogous `Heq`-using shape, to
   avoid the cast pain).
3. Sanity lemmas: `IsRKEquivalentExt` is reflexive, symmetric, and
   transitive on the disjoint union of `QuotEquiv s` over `s`.
4. `bSeriesHom`, `weightsSum`, `cSum` are invariant under
   `IsRKEquivalentExt` (immediate consequences of the cycle 510
   `padRight_*` lemmas).

This is the right sequel because cycle 510 already landed the
algebraic facts the next cycle needs — it just has to do the
quotient-level packaging.
