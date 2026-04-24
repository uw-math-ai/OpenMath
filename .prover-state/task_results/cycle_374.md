# Cycle 374 Results

## Worked on

Theorem 359B (Radau IIA family-level algebraic stability) per cycle 374
strategy. Target was to add a family-level wrapper theorem analogous to
`thm_359C_gaussLegendre` / `thm_359C_radauI`, and a concrete corollary
`rkRadauIIA3_algStable_via_358A` for the existing 3-stage Radau IIA tableau.

## Approach

1. Inspected the existing infrastructure in
   `OpenMath/CollocationAlgStability.lean` and `OpenMath/Legendre.lean` and
   the live sign convention: `shiftedLegendreStarPoly_eval n x =
   shiftedLegendreP n x`, with `shiftedLegendreP n 1 = 1` and
   `shiftedLegendreP n 0 = (-1)^n`.
2. Computed the boundary polynomial: `algStabilityBoundaryPoly s 1 =
   shiftedLegendreStarPoly s − shiftedLegendreStarPoly (s−1)`. Since
   `P_n^*(1) = 1`, this polynomial vanishes at `x = 1`, i.e. its zero set is
   the right-endpoint Radau (Radau IIA) node set, not the left-endpoint
   Radau IA node set.
3. Verified by direct expansion that for `s = 3` the zeros are exactly
   `{(4 − √6)/10, (4 + √6)/10, 1}`, matching `rkRadauIIA3.c`.
4. Added the following to `OpenMath/CollocationFamilies.lean` (and added
   `import OpenMath.RadauIIA3`):
   - `HasRadauIIANodes` predicate (zeros of `algStabilityBoundaryPoly s 1`).
   - `radauIIANodes_hasAlgStabilityBoundaryNodes` bridge (θ = 1 ≥ 0).
   - `thm_359B_radauIIA` family-level wrapper consuming `thm_358A_if`.
   - Concrete `rkRadauIIA3_hasRadauIIANodes`,
     `rkRadauIIA3_isCollocation`, and
     `rkRadauIIA3_algStable_via_358A`.
5. Verified with
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
    OpenMath/CollocationFamilies.lean` and
   `lake build OpenMath.CollocationFamilies`.

No Aristotle batch was sent: the entire deliverable is direct manipulation
of existing infrastructure (one bridge ⟨1, le_of_lt one_pos, ·⟩, two
fin-cases nlinarith proofs for the concrete tableau). All five sub-lemmas
from the strategy decomposition (`radauIIANodes_distinct`, etc.) became
unnecessary because `HasRadauIIANodes` is *defined* as zeros of the boundary
polynomial — the abstract bridge is a one-liner.

## Result

SUCCESS.

- `OpenMath/CollocationFamilies.lean` grew from 124 → 198 lines, no `sorry`s.
- `lake build OpenMath.CollocationFamilies` is clean.
- `plan.md` updated: 359B marked done, Current Target updated to flag the
  genuinely missing family case (Radau IA / left-endpoint, which needs
  θ = −1 under the live sign convention so 358A does not apply directly).

## Dead ends

- First attempt at the concrete `rkRadauIIA3_hasRadauIIANodes` used
  `simp only [..., shiftedLegendreP_three, shiftedLegendreP_two]` to expand
  both Legendre evaluations together. The `shiftedLegendreP_two` rewrite
  silently failed to match (the goal still contained
  `shiftedLegendreP 2 ((4 − √6)/10)`), so `nlinarith` had nothing to chew on.
  Fix: rewrite `shiftedLegendreP_two` *after* the `simp only`, via an
  explicit `show` to expose the three-term polynomial form, then `rw`.

## Discovery

The existing theorem `thm_359C_radauI` (θ = 1) is misnamed under the live
sign convention. With `shiftedLegendreP n 1 = 1`, the polynomial
`P_s^* − P_{s-1}^*` automatically vanishes at the right endpoint
`x = 1`, so `thm_359C_radauI` is mathematically the *Radau IIA* statement,
not Radau IA. The genuine Radau IA case (left endpoint, `c_1 = 0`) requires
θ = −1 in this convention — i.e. boundary polynomial `P_s^* + P_{s-1}^*` —
and so cannot be plugged into `thm_358A_if` directly. The strategy's
warning ("Do not try to apply 358A directly with a negative θ") applies
to that left-endpoint case, not to Radau IIA.

## Suggested next approach

Two natural follow-ups, in priority order:

1. **Radau IA family-level theorem (genuinely new).** The right approach is
   probably to use `shiftedLegendreP_symmetry` (`P_n^*(1 − x) = (−1)^n
   P_n^*(x)`) plus a reflection argument: a tableau `t` with Radau IA nodes
   `c_i` corresponds (after `c_i ↦ 1 − c_i`) to a Radau IIA tableau, and
   algebraic stability is invariant under the reflection. Alternatively,
   prove a reflected variant of 358A whose boundary polynomial is
   `P_s^* + θ P_{s-1}^*` with θ ≥ 0. Either way, this is the actual missing
   359B / 359-family content.
2. **Theorem 359D** (or the next §3.5 corollary in Iserles). Worth scanning
   the textbook to see what is the next theorem in the §3.5 chain that the
   formalization is missing.

If both 359B and 359-Radau-IA are now considered closed for plan purposes
(the currently named theorems do cover them under the live sign convention),
the cycle 375 strategy should pick up Theorem 359D / §3.5.10 corollaries
or pivot to Chapter 4 BDF / variable-step work.

## Aristotle usage

None this cycle. The deliverable was small, structurally trivial, and
relied on the existing `thm_358A_if` plus arithmetic on three roots of a
known cubic. Sending `sorry`s to Aristotle was not justified in this case.
