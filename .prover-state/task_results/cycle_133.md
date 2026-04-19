# Cycle 133 Results

## Worked on
The last remaining sorry in `OpenMath/Collocation.lean`, in the one-big-child branch of `gen_tree_cond`.

## Approach
- Read the cycle strategy and inspected the live goal at the sorry site.
- Checked the Aristotle result directories referenced by the planner; the listed `Collocation.lean` snapshots did not contain a usable patch at the target region.
- Reworked the branch into a structured proof shape:
  - proved and recorded the key easy bounds
  - isolated the remaining algebraic argument into a local `hmain`
  - kept the file compiling with a single sorry
- Submitted the decomposed file to Aristotle:
  - project `8e40574b-5605-4d72-8212-fb5741c22f98`
  - submitted on April 19, 2026

## Result
FAILED

The file compiles, and the last sorry is now isolated behind explicit bound facts (`htb_order_lt`, `htb_q0`, `htb_qnode`), but I did not close the final algebraic proof.

## Dead ends
- The planner’s `children.erase tb` route implicitly needs occurrence-level uniqueness of the large child.
- The available hypothesis
  `htb_unique : ∀ ch ∈ children, n < ch.order → ch = tb`
  only gives uniqueness up to equality of tree values, not uniqueness as a list occurrence.
- Because of that, “all children in `children.erase tb` are small” is not currently justified if `children` contains multiple occurrences equal to `tb`.
- I also spent time trying to package the `erase` argument into top-level helper lemmas; that ran into `LawfulBEq` elaboration friction and did not produce a stable path forward.

## Discovery
- The current branch can be cleanly reduced to a single local `hmain` once the easy bounds are separated.
- The real missing ingredient is not yet the `D(n)` algebra, but a lemma ruling out multiple occurrences of a child with order `> n`, or an alternative factorization that does not rely on `erase`.
- I wrote the blocker up in `.prover-state/issues/one_big_child_factorization_needs_occurrence_uniqueness.md`.

## Suggested next approach
- First prove an occurrence-level uniqueness lemma for large children in this branch.
- After that, revive the original factorization plan:
  1. split off the unique large child,
  2. simplify the remaining fold with `C(n)`,
  3. apply `D(n)` and `ih_gen`,
  4. finish with field/ring cleanup.
- Once the Aristotle job is ready, check whether it found a way around the occurrence-uniqueness gap or proved the missing uniqueness lemma directly.
