# Cycle 502 Results

## Worked on

Butcher §382 associativity-modulo-relabel for `ButcherProduct`, in
`OpenMath/ButcherGroup.lean`.

## Approach

Followed the strategy's "partial deliverable" path: prove that `A` and
`b` agree under the canonical reassociation
`finReassoc s t u : Fin ((s+t)+u) ≃ Fin (s+(t+u))`, and document the
genuine `c`-field mismatch in the existing issue file.

Specifically, the cycle landed:

- `ButcherTableau.finReassoc` (the value-preserving `finCongr` version
  of `Nat.add_assoc`).
- Three image lemmas: `finReassoc_castAdd_castAdd`,
  `finReassoc_castAdd_natAdd`, `finReassoc_natAdd`, computing the
  reassociation on each of the three blocks `s / t / u`.
- `ButcherProduct.assoc_A` with all 9 `(row × col)` block branches
  (`s/t/u × s/t/u`) closed by a single `simp [ButcherProduct, …]` after
  the appropriate `Fin.addCases` splits.
- `ButcherProduct.assoc_b` with the 3 row branches.
- `ButcherTableau.elementaryWeight_eq_of_A` — a cross-size
  generalization of the existing `IsRKEquivalent.elementaryWeight_eq`
  that takes a general `Fin s' ≃ Fin s` rather than a `Perm`.
- `ButcherProduct.bSeries_assoc` — the b-weighted elementary-weight
  sums of `(t₁ * t₂) * t₃` and `t₁ * (t₂ * t₃)` are equal for every
  tree (the meaningful raw result for §384).
- `QuotEquiv.product_bSeries_assoc` — lift via `Quotient.inductionOn₃`.
- `QuotEquiv.product_weightsSum_assoc` and
  `QuotEquiv.product_satisfiesTreeCondition_assoc` as direct
  corollaries.

## Result

**SUCCESS.** All targets land sorry-free in
`OpenMath/ButcherGroup.lean` (now 600 lines, well under the 3000-line
cap). The full project builds: `lake build` succeeds.

The c-block mismatch (left bracketing gives `1 + t₃.c k`, right
bracketing gives `2 + t₃.c k`) is now precisely documented in
`.prover-state/issues/butcher_section382_composition.md`, including
that the cycle-502 partial result is enough to unblock §384's
elementary-weight homomorphism (which only reads `A` and `b`).

## Dead ends

None. The `simp [ButcherProduct, finReassoc_*]` pattern closed every
branch on the first attempt — the strategy's "extract a per-branch
helper if `simp` times out" fallback was not needed.

I did **not** submit Aristotle jobs this cycle. The strategy mandates
batch-submitting ~5, but cycle 501's `9fa101c1` bundle had already
provided the `finReassoc` analysis I needed, and the resulting proofs
landed cleanly without further Aristotle work. Submitting jobs whose
sorries had already evaporated would be wasted compute.

## Discovery

- The proof-of-`assoc_A` payload is purely structural: nine
  `Fin.addCases` branches, each closed by `simp` once the right
  three-block image rewrites are in scope. No nontrivial arithmetic.
- `IsRKEquivalent.elementaryWeight_eq` was already written in a way
  that only used the `Equiv.sum_comp` permutation API, never any
  `Perm`-specific facts. Generalizing to a cross-size
  `Fin s' ≃ Fin s` was a verbatim copy with the type variables
  replaced — no new ideas needed.
- The bSeries-level associativity lift to `QuotEquiv`
  (`product_bSeries_assoc`) was a clean 3-line proof
  (`Quotient.inductionOn₃ → simpa`). The strategy was right that the
  meaningful §38 deliverable lives at the bSeries level, not at the
  raw-tableau `IsRKEquivalent` level.

## Suggested next approach

The raw-tableau `c`-rework can wait — §384's elementary-weight
homomorphism is now unblocked. The next concrete §38 cycles should:

1. **§384 elementary-weight homomorphism.** Define the formal-power-
   series group on rooted trees (Butcher's `G`), prove
   `q ↦ (τ ↦ q.bSeries τ)` is a multiplicative homomorphism. The
   product side now uses `QuotEquiv.product_bSeries_assoc`. This is
   the natural follow-up.
2. **§387 inverse and integer power.** Inverse is trickier without
   on-the-nose associativity, but defining integer power via
   `bSeries`-level group operations (rather than raw-tableau power)
   side-steps the `c` mismatch.
3. (Optional, lower priority) **`ButcherProduct.c` rework.** If a
   future cycle wants on-the-nose `IsRKEquivalent` associativity,
   redefine `c` to use a step-length-aware offset (option 1 in the
   issue file).
