# Cycle 508 Results

## Worked on

Butcher §387 closed-form arithmetic in `OpenMath/ButcherGroup.lean`:

- `ButcherProduct.npowStages_eq` (closed form `n * s`)
- `QuotEquiv.cSum_npow` (closed form
  `n * q.cSum + s * (n * (n-1) / 2)`)
- `QuotEquiv.weightsSum_npow_succ'` (right-associated successor form)
- `QuotEquiv.weightsSum_npow_two` (`= 2 * q.weightsSum`)
- `QuotEquiv.cSum_npow_two` (`= 2 * q.cSum + s`)

## Approach

Sorry-first scaffold landed in `OpenMath/ButcherGroup.lean` with all
five target lemmas marked `sorry`; the file compiled clean modulo the
five expected warnings. Submitted four jobs to Aristotle in batch
against the live module (the fifth submission was rate-limited by the
in-flight cap; per strategy we did not block on it). Sleep window
was used to close the proofs manually:

- `npowStages_eq`: `Nat.rec`. Base by `simp`. Step by
  `npowStages_succ`, `Nat.succ_mul`, and `Nat.add_comm` to reorient
  `s + n*s = n*s + s = (n+1)*s`.
- `cSum_npow`: `Nat.rec`. Base via `cSum_npow_zero` plus `push_cast`
  and `ring`. Step rewrites by `cSum_npow_succ`, the inductive
  hypothesis, and `npowStages_eq`, then `push_cast` and `ring`.
- `weightsSum_npow_succ'`: `rw [weightsSum_npow_succ, add_comm]`.
- `weightsSum_npow_two`: `simpa using weightsSum_npow q 2`.
- `cSum_npow_two`: instantiate `cSum_npow q 2`, `push_cast` away the
  natural-number coercions, then `linarith` collapses
  `(2:ℝ) * ((2:ℝ) - 1) / 2 = 1`.

## Result

SUCCESS. All five target lemmas are sorry-free, and the file compiles
clean with no warnings.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/ButcherGroup.lean
rg -n "sorry" OpenMath/ButcherGroup.lean
```

`lake env lean` returned no output (clean compile, no warnings) and
`rg` reported no sorries.

Aristotle jobs (submitted at 11:04 UTC, before the 30-minute window):

- `5e7eedaf-279a-4fcf-9c74-85dde085341d` (`npowStages_eq`)
- `b9c235df-6ca4-4e12-b8f0-d66c7075eddb` (`cSum_npow`)
- `64f856ff-e3f7-4f3f-ac47-9acdb9a6473f` (`weightsSum_npow_succ'`)
- `71bc225e-54c0-477d-be9a-41a6f1430a43` (`weightsSum_npow_two`)
- 5th (`cSum_npow_two`) submission rate-limited (HTTP 429); per
  strategy and the cycle-503/506/507 history, did not block on it.

Post-sleep status check (single check at ~30 min from submission):
all four submitted jobs were still `QUEUED`. Matches the cycle 503,
506, 507 pattern in this seam. Closed manually.

## Dead ends

- First attempt at `cSum_npow_two` used `simp at h` (after instantiating
  `cSum_npow q 2`); `simp` unfolded `q.npow 2` to the explicit
  `q.product (q.product trivial)` shape and then `linarith` lost the
  link to `(q.npow 2).cSum`. Switched to `push_cast at h` (which
  leaves `(q.npow 2).cSum` as-is and only collapses the cast on the
  constant side); `linarith` then closes immediately.

## Discovery

For `n = k` corollaries of a closed-form `cSum_npow`, prefer
`push_cast at h` over `simp at h`: `push_cast` collapses the casted
constant side without unfolding the `q.npow k` recursion on the LHS,
which keeps the named-target hypothesis intact for `linarith`.

## Suggested next approach

§387 closed-form arithmetic is now effectively closed. The next
planner cycle has three concrete pivots, ranked by how much they
unblock:

1. **§388 subgroups / quotient groups.** Independent of the §384
   convolution gap; would let us state structural theorems
   (e.g. the order-`n` filtration as a normal subgroup) without
   committing to the Connes–Kreimer coproduct shape yet.
2. **§385 generalization** — generalize `weightsSum`/`cSum` chains to
   arbitrary tree-indexed coefficients, using the §387 `cSum_npow`
   closed-form pattern as the template.
3. **§384 convolution.** Still blocked by
   `.prover-state/issues/butcher_section384_convolution.md`. The next
   planner cycle should commit to one of the three solutions in that
   issue before any worker cycle reopens that seam.

§387 inverse element and a non-trivial power-homomorphism remain
blocked by §384 and should not be revisited until §384 lands.
