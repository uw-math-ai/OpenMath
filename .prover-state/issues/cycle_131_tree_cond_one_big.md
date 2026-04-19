# Issue: Theorem 342l one-big-child reduction needs a second induction parameter

## Blocker
The remaining hard case in `OpenMath/Collocation.lean` for Theorem 342l is
`tree_cond_one_big`, where a tree `t = node children` has exactly one child `u`
with `u.order > n` and all other children have order at most `n`.

After applying `D(n)`, the proof naturally produces a correction term
`∑ j, b_j * c_j^(q+1) * elementaryWeight u j`. This term is the tree condition
for a grafted tree of the same total order as `t`, not a strictly smaller-order
tree, so plain strong induction on `t.order` is insufficient.

## Context
- File: `OpenMath/Collocation.lean`
- Local theorem skeleton:
  `private theorem tree_cond_one_big ...`
- Current decomposition:
  - `elementaryWeight_simplified_of_C`
  - `ew_simplified_of_C`
  - `tree_cond_all_small`
  - `tree_cond_one_big`
  - `hasTreeOrder_of_B_C_D` proved from these by strong induction

The intended algebra is:
1. Factor the small children using `C(n)`.
2. Let `q` be the total order contributed by the small children.
3. Use `D(n)` at `k = q + 1`.
4. Reduce to one tree condition for `u` plus one correction term for a grafted tree.

The obstruction is step 4: the grafted tree has order `|t|`, so the current
induction hypothesis does not apply.

## What was tried
- Reframed 342l into four local lemmas and proved the top-level theorem by strong
  induction assuming those lemmas.
- Isolated the all-small and one-big cases explicitly with `childrenOf`.
- Checked whether the one-big correction term could be rewritten to a strictly
  smaller-order tree condition directly; it cannot without extra structure.
- Submitted the decomposed lemmas to Aristotle for possible automation.

## Possible solutions
- Introduce a second induction parameter on the number of large branches or on a
  lexicographic measure `(order, number_of_children_above_n)`.
- Follow Hairer–Nørsett–Wanner IV.5 more literally by introducing the auxiliary
  right-hand-side quantity used in the textbook proof, then prove the recurrence
  simultaneously with the tree condition.
- Define and prove a dedicated grafting lemma that handles
  `∑ j, b_j * c_j^m * elementaryWeight u j` by induction on the exponent `m`
  together with the tree structure.
