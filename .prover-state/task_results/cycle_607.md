# Cycle 607 Results

## Worked on
Butcher §372 in `OpenMath/SymplecticRK.lean`: the symplectic simplifying
column identity for consistent symplectic Runge-Kutta tableaus.

## Approach
Followed the cycle strategy and kept the work out of the paused §38 files.
First updated `plan.md` for the already-landed §250 Taylor-series target,
then added `IsSymplectic.bA_col_eq` sorry-first and verified the file.
Closed the proof by summing `symplecticDefect i j = 0` over `i`, splitting
the finite sum, substituting consistency row/weight sums, and finishing by
linear arithmetic plus `ring`. Added the optional midpoint regression
corollary `rkGaussLegendre1_bA_col`.

## Result
SUCCESS. Added the sorry-free theorem:

```lean
theorem IsSymplectic.bA_col_eq {s : ℕ} {t : ButcherTableau s}
    (hSymp : t.IsSymplectic) (hCons : t.IsConsistent) :
    ∀ j : Fin s, (∑ i, t.b i * t.A i j) = t.b j * (1 - t.c j)
```

Also marked §250 and §372 complete in `plan.md` and removed both from the
Backlog Queue with the remaining items renumbered.

## Dead ends
The only Lean adjustment was orientation: `IsConsistent.row_sum` is stored
as `t.c j = ∑ i, t.A j i`, so the proof uses `(hCons.row_sum j).symm`.
No Aristotle jobs were submitted, per the cycle strategy.

## Discovery
The finite-sum split works directly with existing Mathlib lemmas
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, and `Finset.mul_sum`.
`linarith` is sufficient after rewriting the row and weight sums.

Verification:
- `lake env lean OpenMath/SymplecticRK.lean`
- Lean LSP `lean_verify` on `ButcherTableau.IsSymplectic.bA_col_eq`
  and `ButcherTableau.rkGaussLegendre1_bA_col`
- `lake build` completed successfully; warnings were pre-existing in
  unrelated modules.

## Suggested next approach
Keep §38 paused until a dedicated coproduct/cut-associativity design cycle.
For the next small algebraic target, promote the current top Backlog Queue
item (§341 implicit RK stage solvability) or schedule the larger §254
Taylor derivative plumbing explicitly.
