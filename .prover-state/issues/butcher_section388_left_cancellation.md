# Issue: §388 left-cancellation identity proposed by cycle 578 strategy is false

## Blocker

The cycle 578 strategy schedules the "symmetric (left) direction" of the
§388 inverse cancellation as

```lean
theorem bSeriesConv_inverseCoeff_cancel_node_left
    {s : ℕ} (q : QuotEquiv s) (children : List BTree) :
    q.inverseCoeff (BTree.node children)
      + bSeriesConv q.inverseCoeff q.bSeries (BTree.node children) = 0
```

and reduces it (Step 3) via `bSeriesConv_eq_root_plus_nonRoot` and the
existing `QuotEquiv.inverseCoeff_node_eq` to the swap

```
bSeriesConvNonRoot q.inverseCoeff τ (fun σ _ => q.bSeries σ)
  = bSeriesConvNonRoot q.bSeries τ (fun σ _ => q.inverseCoeff σ)   -- (★)
```

**Both the headline identity and the swap (★) are false** for general
unit-stage `q`, including the standard Heun (RK2) tableau and even the
1-stage explicit Euler tableau.

## Counterexample

Take `q` = quotient class of the 1-stage explicit Euler tableau:
`s = 1, b₀ = 1, c₀ = 0, A = 0`.

Direct evaluation (using `bSeries_leaf`, `bSeries_node_nil`, the formula
`bSeries (node [leaf]) = ∑ b_i c_i = 0`, and the `inverseCoeff`
recursion):

| τ              | order | q.bSeries τ | q.inverseCoeff τ |
| -------------- | ----- | ----------- | ---------------- |
| `leaf`         | 1     | 1           | 1                |
| `node []`      | 1     | 1           | −1               |
| `node [leaf]`  | 2     | 0           | 1                |

`q.inverseCoeff (node [leaf])` is verified by the recursion:
`I (node [leaf]) = -(b (node [leaf]) + b leaf · I (node []))
                 = -(0 + 1 · (-1)) = 1`.

The proper inner cuts of `node [leaf]` enumerated by
`(node [leaf]).innerCut q.inverseCoeff` are

```
(none,                  q.inverseCoeff (node [leaf])) -- = 1, dropped by filterMap
(some (node [leaf]),    1)                            -- trunk = τ, full order
(some (node []),        q.inverseCoeff leaf)          -- = 1
```

so

```
bSeriesConv q.inverseCoeff q.bSeries (node [leaf])
  = 1 * q.bSeries (node [leaf]) + 1 * q.bSeries (node [])
  = 0 + 1 = 1
```

Hence

```
q.inverseCoeff (node [leaf]) + bSeriesConv q.inverseCoeff q.bSeries (node [leaf])
  = 1 + 1 = 2 ≠ 0
```

contradicting the headline target.

## Independent counterexample at Heun (RK2)

Heun: `s = 2, b = (1/2, 1/2), c = (0, 1), A[1,0] = 1`.

| τ              | q.bSeries τ | q.inverseCoeff τ |
| -------------- | ----------- | ---------------- |
| `leaf`         | 1           | 1                |
| `node []`      | 1           | −1               |
| `node [leaf]`  | 1/2         | 1/2              |

Right-inverse identity (cycle 577) at `node [leaf]`:
`b + bSeriesConv b I = 1/2 + (-1/2) = 0` ✓.

Proposed left-inverse identity at `node [leaf]`:
`I + bSeriesConv I b = 1/2 + 3/2 = 2 ≠ 0`.

The swap (★) at `τ = node [leaf]`:

- `bSeriesConvNonRoot I τ (· => b·)`: only proper cut has trunk `node []`,
  weight `I leaf = 1`, contributing `1 · b (node []) = 1`.
- `bSeriesConvNonRoot b τ (· => I·)`: same proper cut, weight `b leaf = 1`,
  contributing `1 · I (node []) = -1`.

So `1 ≠ -1`; (★) fails.

## What the existing recursion really says

`QuotEquiv.inverseCoeff_node_eq` gives, at `τ = node children`,

```
b τ + bSeriesConvNonRoot b τ (· => I·) + I τ = 0
```

Adding the cycle 577 peeling lemma `bSeriesConv = β τ + bSeriesConvNonRoot α τ β·`:

```
b τ + bSeriesConv b I τ = 0          (right inverse, cycle 577 result)
```

The **left** variant would require

```
I τ + bSeriesConv I b τ = 0
  = I τ + b τ + bSeriesConvNonRoot I τ (· => b·)   -- by peeling lemma
```

which, combined with `inverseCoeff_node_eq`, is equivalent to (★). The
counterexamples above show (★) does not hold, hence the left variant does
not hold either. The recursion **only** forces `inverseCoeff` to be a
right partial inverse of `q.bSeries` under `bSeriesConv`; it does **not**
make it a left inverse.

## Why this matters for `G1.inv`

The cycle 578 strategy planned to use both directions of the cancellation
to define `G1.inv`. The mismatch above means that `q.inverseCoeff`,
considered as a `BTree → ℝ` function, is **not** the convolution inverse
of `q.bSeries`. The correct `G1.inv` construction must use a
*tableau-level* inverse — i.e. produce a `QuotEquiv s'` whose `bSeries`
is the genuine convolution inverse (which on unit-stage characters
coincides with the standard Butcher-group antipode) — not the
recursively defined `inverseCoeff` function on its own.

In particular, even at the leaf the convolution unit is `0` (the trivial
tableau has `bSeries = 0`), but `q.inverseCoeff leaf = 1` for every `q`,
so already at `τ = leaf` we have
`q.bSeries leaf + bSeriesConv q.bSeries q.inverseCoeff leaf
   = q.bSeries leaf + 1 ≠ 0`
in general. The right-inverse cancellation theorem
`bSeriesConv_inverseCoeff_cancel_node` is therefore restricted to
non-leaf trees, and `inverseCoeff` is best read as the "unit-stage
auxiliary recursion" rather than a true inverse.

## What was tried this cycle

- Hand-evaluated the left identity at Heun and at 1-stage explicit Euler;
  both give a non-zero residue at `τ = node [leaf]`.
- Hand-evaluated the swap (★) at the same `τ`; the LHS gave `+1` and
  RHS `-1`, ruling out (★) as a pointwise equation of sums.
- Did **not** attempt the strong induction Step 2: the swap is not a
  theorem and the planner's "IH lets you swap inside a summand"
  reasoning has no foothold (each summand is a number; the IH would only
  give equalities of `bSeriesConvNonRoot` at strictly smaller trees,
  not pointwise relations between cut weights).

## Possible solutions

1. **Construct a tableau-level inverse.** For `q ∈ G1`, build a
   `QuotEquiv s'` (e.g. via the standard Butcher antipode formula on
   tableaux) whose `bSeries` is the true two-sided inverse under
   `bSeriesConv`. Land `G1.inv` from this tableau-level construction.

2. **Prove convolution associativity** for arbitrary `α, β, γ : BTree → ℝ`
   first, then derive existence and uniqueness of two-sided inverses by
   the standard Hopf-algebra argument
   `S = S * (id * R) = (S * id) * R = R`. Note this still requires
   adjusting the leaf-level recursion (`I leaf = -b leaf` rather than
   the current `I leaf = 1`) so that `I` is a true right inverse at the
   leaf as well — i.e. drop the unit-stage augmentation that motivated
   `I leaf = 1` in the current definition.

3. **Re-scope §388 to only the right-direction cancellation already
   established.** Acknowledge that the recursive `inverseCoeff` is only
   the partial right-inverse needed for the §388 statement of Iserles,
   and that `G1.inv` requires a separate tableau-level construction.

The cleanest path is probably (1) combined with (3): keep the existing
`inverseCoeff` as a §388 textbook artifact, and define `G1.inv` directly
from a tableau-level antipode construction.

## Acceptable cycle 578 minimum (per strategy)

Per the strategy's "If the strong induction stalls" clause, this issue
file plus the sorry-free leaf companion
`bSeriesConv_inverseCoeff_cancel_leaf_left` (which only restates
`bSeriesConv_leaf` at the inverse-arguments) is the agreed minimum.
Both have been landed.

## Cycle 579 status update

Cycle 579 did not reopen the false left-cancellation target. It added
right-slot structural identities for the honest §386 convolution:

- `bSeriesConv_add_right`
- `bSeriesConv_smul_right`
- `bSeriesConv_zero_left`

These lemmas are compatible with this issue: they describe linearity in
the second coefficient map and the canonical no-cut contribution when
the left coefficient is identically zero. They do **not** imply a
left-inverse law for `QuotEquiv.inverseCoeff`, because the obstruction
recorded above is in the first coefficient slot, where cut weights are
products and cross terms/non-invertible leaf behavior remain.
