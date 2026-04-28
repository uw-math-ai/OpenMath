# Cycle 506 Results

## Worked on

§387 successor-side power scaffold for `OpenMath/ButcherGroup.lean`.
The five concrete targets named in the cycle 506 strategy:

1. `ButcherProduct.npow_succ_weightsSum` (raw)
2. `QuotEquiv.weightsSum_npow_succ`
3. `QuotEquiv.weightsSum_npow` (closed form `= n * q.weightsSum`)
4. `QuotEquiv.bSeriesHom_npow_one`
5. `QuotEquiv.cSum_npow_zero`

## Approach

Wrote all five lemmas directly using cycle 501–505 templates already
present in the file. None of the proofs are research-level: they all
reduce to one or two `rw`/`simp` calls plus a `Nat`-induction step.

- (1) unfolds `ButcherProduct.npow_succ` and applies the cycle-500
  lemma `butcherProduct_b_sum`.
- (2) rewrites by `QuotEquiv.npow_succ` then by `product_weightsSum`.
- (3) inducts on `n`. Base case rewrites by `weightsSum_npow_zero`,
  `Nat.cast_zero`, and `zero_mul`. Successor case applies (2), the
  induction hypothesis, then `push_cast; ring` to absorb the
  `Nat.cast_succ` step.
- (4) After unfolding `npow_one = product (mk trivialTableau) q`, the
  goal becomes `bSeries (product (mk trivialTableau) q) τ = bSeries q τ`,
  closed by `product_bSeries_one_left` (cycle 504/505 left-identity).
  `funext τ` plus a `change` to thread the `bSeriesHom` definitional
  reduction.
- (5) Mirrors `weightsSum_npow_zero`: the zero-power lifts to
  `Quotient.mk _ trivialTableau`, and `cSum (Quotient.mk _ trivialTableau)`
  reduces to an empty `Fin 0` sum. Closed by `simp [npow, cSum, trivialTableau]`.

## Result

SUCCESS — all five lemmas land sorry-free.
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean` returns clean (no errors, no warnings,
no sorries).

## Aristotle batch

Skipped this cycle. The strategy notes that the cycle 505 batch
(`170aa9c6…`, `07c51076…`, `869eddf1…`, `0d2ddea9…`, `7329da44…`)
was still `QUEUED` after the 30-minute window. The five targets here
are tiny one-to-three-line proofs and were closed by hand on the
first attempt using the existing template chain. Submitting them to
Aristotle would not have helped close anything (there were no
remaining sorries by the time a 30-minute window would have elapsed)
and would have burned queue priority that future stuck cycles will
need. Documenting this so the next planner knows the §387 power
scaffold layer is closeable manually and does not require the
Aristotle batch.

## Dead ends

None this cycle. The strategy's "type alignment" worry for (3)
(`weightsSum` lives in `ℝ` so `(n : ℝ) * ...` is fine) and for (4)
(definitional vs propositional reduction of `npow q 1` against the
`0 + s` stage count) both turned out to be benign: the function-level
equality on `BTree → ℝ` discharges the stage-count discrepancy via
`product_bSeries_one_left`.

A small simp-lint loop around the (3) base case: `simp
[weightsSum_npow_zero]` flagged the lemma as unused (the `simp` can
discharge `(0 : ℝ) * x = 0` via `zero_mul` alone, but only after
`weightsSum_npow_zero` rewrites the LHS). Replaced with explicit
`rw [weightsSum_npow_zero, Nat.cast_zero, zero_mul]` to satisfy the
linter.

## Discovery

The (4) proof confirms that the `npowStages s 1 = 0 + s`
vs. `s` mismatch is invisible at the `bSeriesHom` level (where the
output type is `BTree → ℝ` independent of stage count). This
suggests the §387 inverse construction can be stated entirely at the
`bSeriesHom` / `weightsSum` level without needing a HEq dance over
stage counts — a useful observation for the next §387 layer.

## Suggested next approach

The natural next layer is the §387 successor-side `bSeriesHom` chain:
once the §384 tree-convolution gap closes, the analog of
`weightsSum_npow_succ` for `bSeriesHom` (i.e.
`bSeriesHom (npow q n.succ) τ = bSeriesHom (npow q n) τ +
bSeriesHom q τ` if such a thing held — it does not in general for
`bSeriesHom`, since `bSeriesHom` of a product is a tree-convolution,
not a sum) should fall out as a corollary.

Until §384 lands, the closeable §387 layers are:

- `QuotEquiv.cSum_npow_succ` (mirror of (2) for `cSum`) — needs a
  cycle-500-style `butcherProduct_c_sum` lemma. Not yet in the file.
  Writing one is straightforward: the `c` field of
  `ButcherProduct t₁ t₂` on the left block is `t₁.c i` and on the
  right block is `1 + t₂.c i`, so the sum equals
  `(∑ i, t₁.c i) + s + (∑ i, t₂.c i)` where `s` is the right block
  size. That is **not** a clean homomorphism (the `+ s` term breaks
  additivity), so a closed-form `cSum_npow` analog of (3) does
  **not** exist with the current `c` convention. Plan ahead: state
  `cSum_npow_succ` as `(npow q n.succ).cSum = (npow q n).cSum + n*s + q.cSum`
  or similar, and document the offset explicitly.
- `QuotEquiv.weightsSum_npow_one` as a `simp`-friendly corollary of
  (3) at `n = 1` — one-liner.
- The `bSeriesHom_npow_zero` zero-power identity (already landed)
  paired with a `(npow q 0).hasTreeOrder p ↔ True` corollary if the
  textbook needs it.

## Files touched

- `OpenMath/ButcherGroup.lean` — added §387 successor-side
  weights-sum chain and unit / zero power sanity lemmas.
- `plan.md` — extended the §387 bullet under "§38 Algebraic
  Properties of Runge–Kutta Methods" with the cycle 506 lemmas.
