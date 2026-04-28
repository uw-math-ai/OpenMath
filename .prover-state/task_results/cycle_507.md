# Cycle 507 Results

## Worked on

Butcher §387 power-chain node-sum lemmas in `OpenMath/ButcherGroup.lean`:
`butcherProduct_c_sum`, `QuotEquiv.product_cSum`,
`QuotEquiv.cSum_npow_succ`, `QuotEquiv.weightsSum_npow_one`, and
`QuotEquiv.cSum_npow_one`.

## Approach

Started with the required sorry-first scaffold and verified
`OpenMath/ButcherGroup.lean` compiled with exactly the five target sorries.
Submitted one Aristotle job per target, then slept for the required
30-minute window before checking statuses once.

The live `npow` recurrence initially had the opposite product orientation
from the cycle strategy:
`npow q (n+1) = product (npow q n) q`. With that orientation,
`(q.npow 1).cSum = q.cSum` is false because `product trivial q` offsets the
right block by `1`. I corrected the §387 recurrence to the planner-stated
right-associated shape `npow q (n+1) = product q (npow q n)`, with
`ButcherProduct.npowStages s (n+1) = s + ButcherProduct.npowStages s n`.
Existing power lemmas were updated to the new orientation.

After Aristotle remained queued, closed the proofs manually:

- `butcherProduct_c_sum`: split `Fin (s+t)` with `Fin.sum_univ_add` and
  simplified the right block sum of `1 + t₂.c i`.
- `QuotEquiv.product_cSum`: quotient induction plus `butcherProduct_c_sum`.
- `QuotEquiv.cSum_npow_succ`: rewrite by the updated `npow_succ` and
  `product_cSum`, giving the offset `(ButcherProduct.npowStages s n : ℝ)`.
- `QuotEquiv.weightsSum_npow_one`: direct `simpa` from `weightsSum_npow q 1`.
- `QuotEquiv.cSum_npow_one`: apply `cSum_npow_succ` at `n = 0` and simplify.

## Result

SUCCESS. All target lemmas are sorry-free, and the §387 power recurrence now
matches the cycle 507 target orientation.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean
rg -n "sorry" OpenMath/ButcherGroup.lean
```

The Lean check returned clean, and `rg` reported no sorries.

Aristotle jobs after the required 30-minute wait:

- `b4733578-2d57-4cca-8aca-8e21426195fe` (`butcherProduct_c_sum`): `QUEUED`
- `81c866ea-5d48-4155-97e2-799d115532a6` (`QuotEquiv.product_cSum`): `QUEUED`
- `a876928c-975b-4ee7-ac3b-f8f34bcd1ef7` (`QuotEquiv.cSum_npow_succ`): `QUEUED`
- `2298210b-fc99-4b5a-bbe6-43bb4af05a46` (`QuotEquiv.weightsSum_npow_one`): `QUEUED`
- `663ae1f3-daa7-4b8c-8588-211034fdb441` (`QuotEquiv.cSum_npow_one`): `QUEUED`

## Dead ends

The only dead end was trying to keep the old `npow` orientation. It makes the
requested unit `cSum` corollary mathematically wrong: `npow q 1` reduces to
`product trivial q`, whose `c` field is `1 + q.c` on every base stage.

## Discovery

The `cSum` behavior is a useful sanity check for the intended §387 power
orientation. The right-associated recurrence `product q (npow q n)` is the
orientation compatible with `q.npow 1` behaving like `q` for `cSum`; the
previous recurrence was still acceptable for `weightsSum` and `bSeriesHom`
unit checks because those projections do not see the `c` offset in the same
way.

## Suggested next approach

The next §387 layer should be either the inverse element
(`QuotEquiv.npowInv` / Connes-Kreimer-antipode-flavored inverse construction)
or the §384 convolution, but only after a planner cycle commits to the
tree-product definition. Do not reopen §386 list-split scaffolding without a
fresh planner pivot.
