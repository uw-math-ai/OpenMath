# Cycle 132 Results

## Worked on
Closing 4 sorrys in `OpenMath/Collocation.lean` for Theorem 342l: `B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)`.

## Approach
1. Attempted to harvest Aristotle results from cycle 131 — all returned 500 errors (server issue).
2. Manually proved all 4 sorry'd lemmas using strong induction on tree order, C(n) simplification, and algebraic manipulation.
3. Introduced `gen_tree_cond` (generalized tree condition with weighted sums `∑ bᵢ cᵢ^q Φᵢ(t)`) to handle the one-big-child case, which requires nested recursion.

## Result
**GOOD PROGRESS** — 3 of 4 original sorrys closed. 1 sorry remains (down from 4).

### Closed (3):
- `elementaryWeight_simplified_of_C`: Under C(n), ew(t,i) = cᵢ^(r-1)/childDensityProd(t). Proved by `Nat.strongRecOn` on tree order.
- `ew_simplified_of_C`: ∑ₖ aᵢₖ ew(t,k) = cᵢ^r/γ(t). Follows from above + C(n).
- `tree_cond_all_small`: When all children have order ≤ n, the tree condition holds. Uses ew simplification + B(2n).

### Remaining (1):
- `gen_tree_cond` one-big-child case (line ~1947): The algebraic proof that factors the elementary weight product, applies D(n) to swap sums, and uses recursive gen_tree_cond for the big child.

### New infrastructure added:
- `gen_tree_cond`: Generalized tree condition `∑ bᵢ cᵢ^q Φᵢ(t) = r(t)/((q+r(t))·γ(t))`. Leaf and all-small cases proved.
- `single_mem_order_le_foldr`: Member order ≤ foldr order sum.
- `two_distinct_order_le_foldr`: Two distinct members' orders sum ≤ foldr sum.
- `htb_unique` (inside gen_tree_cond): At most one child can have order > n (proved using order sum bound).
- `tree_cond_one_big` rewritten as corollary of `gen_tree_cond` with q=0.
- `foldr_density_prod_pos`, `foldr_ew_simplified`, `ew_factor_simplified`: Helper lemmas for ew factorization.

## Dead ends
- Aristotle cycle 131 jobs all returned 500 errors — couldn't harvest.
- `induction t` fails for nested inductive `BTree` — must use `cases t` + `Nat.strongRecOn`.
- `Nat.zero_add` doesn't apply to `↑0 + ↑t.order` on ℝ — need `Nat.cast_zero` + `zero_add`.
- Nested induction inside `two_distinct_order_le_foldr` caused type mismatch — refactored to use separate `single_mem_order_le_foldr` helper.
- Build environment: mathlib package kept getting deleted by lake on each run. Fixed with `LAKE_NO_RESOLVE=1` and `LEAN_CC=gcc C_INCLUDE_PATH=/usr/include LIBRARY_PATH=/tmp/lean4-toolchain/lib`.

## Discovery
- The one-big-child case fundamentally requires a **generalized** tree condition with exponent q, not just the standard q=0 case. This is because D(n) introduces correction terms involving `∑ bᵢ cᵢ^p Φᵢ(tb)` at higher powers p.
- The proof strategy for the remaining sorry is fully mapped out:
  1. Factor ew into big-child and small-child contributions
  2. Simplify small factors via C(n)
  3. Swap sums, apply D(n) with degree q'+S+1 ≤ n
  4. Telescoping via ih_gen at q=0 and q=q'+S+1 for the big child
  5. Algebraic cleanup: result = node.order / ((q'+node.order) * node.density)
- The key difficulty is step 1: factoring a List.foldr product when extracting one element. Need a lemma like `foldr_extract_mem` for multiplicative products.

## Suggested next approach
1. Check Aristotle job `25db1b57` (submitted this cycle for the remaining sorry).
2. If Aristotle fails: prove `foldr_extract_mem` helper (factoring one element out of a foldr product), then follow the 5-step strategy above.
3. Consider decomposing into sub-lemmas: `factor_big_child_ew`, `D_swap_sums`, `telescope_ih_gen`.
