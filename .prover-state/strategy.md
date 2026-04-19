# Strategy — Cycle 133

## Situation
- **Cycle**: 133
- **Project-wide sorrys**: 1, in `OpenMath/Collocation.lean` (line ~1947)
- **Target**: Close the last sorry in Theorem 342l `gen_tree_cond` (one-big-child case)
- **DahlquistEquivalence.lean**: fully proved (0 sorrys)

### Aristotle Jobs
```
25db1b57  — gen_tree_cond one-big-child (submitted cycle 132)
```

## The 1 Remaining Sorry

In `gen_tree_cond`, the one-big-child case of the node branch. After establishing `htb_unique` (at most one child `tb` has order > n), we need:

```
∑ i, b_i * c_i^q' * ew(node children, i) = node.order / ((q'+node.order) * node.density)
```

### Available hypotheses:
- `ih_gen`: recursive gen_tree_cond for trees with order < m
- `htb_unique`: all children with order > n equal tb
- `htb_mem : tb ∈ children`, `htb_big : n < tb.order`
- `hq'u : q' + (BTree.node children).order ≤ 2 * n`
- `hB`, `hC`, `hD` simplifying assumptions

## Proof Strategy (5 steps)

### Step 1: Factor elementary weight
`ew(node children, i)` is `children.foldr (fun t acc => acc * (∑_k a_{ik} ew(t, k))) 1`.

Need a helper lemma `foldr_extract_mem`: for tb ∈ children,
```
children.foldr f 1 = f(tb, (children.erase tb).foldr f 1)
```
where `f(t, acc) = acc * g(t)` is commutative/associative.

### Step 2: Simplify small children via C(n)
All children in `children.erase tb` have order ≤ n (by htb_unique).
Use `ew_factor_simplified` for each: `∑_k a_{ik} ew(ch, k) = c_i^{ch.order} / density(ch)`.
Product of small factors = `c_i^S / D_small` where:
- S = sum of small children's orders = (node.order - 1) - tb.order
- D_small = product of small children's densities

### Step 3: Swap sums
```
∑_i b_i c_i^{q'+S} * (∑_k a_{ik} ew(tb, k)) / D_small
= (1/D_small) * ∑_k ew(tb, k) * (∑_i b_i a_{ik} c_i^{q'+S})
```
Use `Finset.sum_comm`.

### Step 4: Apply D(n)
`q' + S + 1 ≤ n` (proved from: q' + node.order ≤ 2n, node.order = 1+S+tb.order, tb.order > n).
D(n) gives: `∑_i b_i a_{ik} c_i^{q'+S} = b_k (1 - c_k^{q'+S+1}) / (q'+S+1)`.

### Step 5: Apply ih_gen recursively
- `ih_gen` at q=0, tb: `∑_k b_k ew(tb,k) = tb.order/(tb.order * tb.density) = 1/tb.density`
- `ih_gen` at q=q'+S+1, tb: `∑_k b_k c_k^{q'+S+1} ew(tb,k) = tb.order/((q'+S+1+tb.order)*tb.density)`

Combine: telescoping gives `(q'+S+1)/((q'+S+1+tb.order)*(q'+S+1)*tb.density*D_small)`
= `1/(D_small*tb.density*(q'+node.order))` = `node.order/((q'+node.order)*node.density)`.

## Key Bounds
- `q' + S + 1 ≤ n`: from q'+node.order ≤ 2n, S = node.order-1-tb.order, tb.order ≥ n+1
- `tb.order < m`: child_order_lt_of_mem gives tb.order < node.order = m
- `0 + tb.order ≤ 2*n`: since tb.order < node.order ≤ 2n
- `q'+S+1 + tb.order ≤ 2*n`: equals q'+node.order ≤ 2n

## Priority 1: Harvest Aristotle (5 min)
Check job `25db1b57`. If complete, incorporate.

## Priority 2: Prove the sorry manually (if Aristotle fails)
Follow the 5-step strategy above. Key sub-lemmas to build:
1. `foldr_mul_extract`: factor one element out of a foldr product
2. `small_children_simplified`: product of small children's A-weighted ew sums = c_i^S / D_small
3. `D_swap_application`: the sum after applying D(n)
4. `telescope_gen_tree_cond`: combine ih_gen at q=0 and q=p to get the final expression

## What NOT to Try
1. Do NOT try to unfold everything at once — the algebraic manipulation is too large for field_simp alone.
2. Do NOT apply C(n) to tb (its order > n).
3. Do NOT try a different induction structure — the current gen_tree_cond with Nat.strongRecOn is correct.
4. Do NOT increase maxHeartbeats.

## Build Commands
```bash
LEAN_CC=gcc C_INCLUDE_PATH=/usr/include LIBRARY_PATH=/tmp/lean4-toolchain/lib PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH LAKE_NO_RESOLVE=1 lake env lean OpenMath/Collocation.lean
```
Note: Use `LAKE_NO_RESOLVE=1` to prevent lake from re-cloning mathlib on every run.

## Exit Criteria
- **Full success**: 0 sorrys project-wide → Theorem 342l complete
- **Good progress**: Sorry decomposed into 2-3 smaller sub-lemmas with clear proof path
- **Minimum acceptable**: At least one sub-lemma proved (e.g., foldr_mul_extract)
