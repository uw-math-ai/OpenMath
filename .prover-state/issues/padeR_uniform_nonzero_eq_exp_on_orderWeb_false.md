# Issue: fully uniform `padeR_no_nonzero_eq_exp_on_orderWeb` is false

## Blocker
The original live statement

`∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`

cannot be proved uniformly in `(n,d)` because it is already false for
`(n,d) = (0,0)`.

## Context
- `padeR 0 0 z = 1` by the existing Padé edge lemmas.
- Taking `z = (2 * Real.pi : ℂ) * Complex.I`, we have:
  - `z ≠ 0`
  - `z ∈ orderWeb (padeR 0 0)` with witness `r = 1`
  - `padeR 0 0 z = exp z`
- A Lean check for this counterexample compiled in `/tmp/check_counterexample_cycle287.lean`.
- Repository use-site search found zero external consumers of
  `padeR_no_nonzero_eq_exp_on_orderWeb`.

## What was tried
- Re-read the concrete `OrderStars` seam and the Padé file for any existing
  theorem excluding nonzero coincidence points on `orderWeb (padeR n d)`.
- Re-triaged the cycle-286 Aristotle bundles. They still depend on stale or
  incompatible interfaces and were discarded.
- Checked the theorem shape directly instead of searching longer for a proof of
  a false statement.

## Possible solutions
- Keep the theorem local and honest, with an explicit hypothesis excluding
  nonzero unit-level points on `orderWeb (padeR n d)`.
- If a future cycle needs a Padé-specific theorem, restrict first to the actual
  Padé subfamily used downstream rather than restoring a false uniform claim.
- If the intended theorem was meant only for nontrivial Padé families, test the
  smallest plausible restriction such as `n + d > 0` before stating it in live
  code.
