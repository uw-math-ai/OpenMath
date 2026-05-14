# Issue: thm:381H — three of four iff directions deferred

## Cycle 208 update

The `PEquivalent → Equivalent` direction (formerly deferred direction
(2) below) is now **closed** via cycle 208's
`PEquivalent.toEquivalent` in
`OpenMath/Chapter3/Section381.lean` (inside namespace
`OpenMath.Chapter3.Section312.RKTableau`, immediately after
`PReducesTo.toEquivalent`). Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). The proof composes
cycle 207's `PReducesTo.toEquivalent` on both legs of `PEquivalent`'s
existential common reduct, then closes via
`Equivalent.trans` + `Equivalent.symm` (cycles 204, 206).

Companion non-vacuity witnesses also shipped this cycle (inside
namespace `OpenMath.Chapter3.Section381`, after
`paddedEuler_equivalent_self`):
* `paddedEuler_equivalent_pReduced`
* `paddedEuler_equivalent_zeroReduced`

These exercise the `step` and `zeroStep` constructor paths through
cycle 207's `PReducesTo.toEquivalent`.

Bundled umbrella corollary
`PEquivalent.toEquivalent_and_toPhiEquivalent` (the two closed
directions of `thm:381H` packaged together) also shipped axiom-clean.

**Updated status**: 2 of 4 iff directions are now closed
(`PEquivalent → PhiEquivalent` via cycle 187,
`PEquivalent → Equivalent` via cycle 208). The remaining two
(`Equivalent → PEquivalent` and `PhiEquivalent → PEquivalent`,
deferred directions (1) and (3) below) are still blocked on
`thm:381G` + the combine-two-tableaux construction. Once at least
one of those becomes single-cycle closeable, the `thm:381H` umbrella
scaffold can be re-introduced (sorry count 0 → 2, satisfying
supervisor policy).

## Cycle 201 rollback

The cycle 200 statement-only scaffold was removed from
`OpenMath/Chapter3/Section381.lean` in cycle 201 to drive the file's
sorry count back to 0 (3 → 0) per supervisor policy ("sorry increase
is bad"; cycle 200 scored −2). The deleted block was the theorem
`equivalent_iff_pEquivalent_iff_phiEquivalent` together with its
docstring (previously at lines 1569–1641); the `lean_status.json` row
for `thm:381H` reverted to `unformalized`, and the `plan.md` row
reverted to `[ ]` form.

This rollback follows the established precedent from cycle 138 → 139
(thm:550A general-n scaffold) and cycle 149 → 150 (def:530B Path A
scaffold) — sorry-first scaffolds with no path to single-cycle closure
get rolled back, and the deferred-direction analysis stays in this
file as planning material for re-introduction once at least one of the
three directions becomes closeable in a single cycle.

**Cycle 201 P2** began the Banach-fixed-point foundation
(`RKStageMap` def + Lipschitz lemma + non-vacuity witness) — the
shortest path to closing `PEquivalent → Equivalent`. Re-introduce the
thm:381H scaffold once that direction (or any of the other two) can
be closed in one cycle: at that point sorry count goes from 0 → 2
(or → 1 if two directions are closeable) instead of 0 → 3, satisfying
supervisor policy.

## Status (cycle 200 — superseded by cycle 201 rollback above)

Cycle 200 shipped the statement-only scaffold of
`equivalent_iff_pEquivalent_iff_phiEquivalent`
(Butcher §380 Theorem 381H, p. 304) in `OpenMath/Chapter3/Section381.lean`
with **one of four** iff-directions closed axiom-clean and **three** left
as tracked `sorry`s.

## Closed direction

* **`PEquivalent → PhiEquivalent`** — closed via cycle 187's
  `PEquivalent.toPhiEquivalent` (one-line `exact`). This is the easy
  direction; `PhiEquivalent.of_pReducesTo` (also cycle 187 era) is the
  underlying induction.

## Deferred directions

### (1) `PhiEquivalent → PEquivalent`  (Butcher §380.8653–8661)

Textbook proof: Suppose two methods M, M' are Φ-equivalent but not
P-equivalent. Combine the s+s' stages of M and M' (together with their
output approximations) into a single tableau and replace by its reduced
form. Because M, M' are not P-equivalent, the two output approximations
end up in different partition blocks. **Apply thm:381G** to get
`t ∈ T` with `Φᵢ(t) ≠ Φⱼ(t)` for the two output approximations —
contradicting Φ-equivalence.

**Blocker**: thm:381G (Butcher §380, p. 282) is not formalised. Its
recon by cycle 199 estimates 2–3 cycles of prerequisite work
(thm:314A + subalgebra-of-elementary-weights infrastructure in ℝˢ).
See `.prover-state/issues/p_reduction_confluence_gap.md` for the
adjacent confluence-side multi-cycle plan; thm:381G is a different
multi-cycle subgoal in the §380 cluster.

**Also blocked on**: the "combine two tableaux into one" construction
itself (block-diagonal Runge–Kutta tableau on disjoint stage sets) is
not currently in `Section381.lean`. Would require ~50–100 LOC of
new infrastructure even with thm:381G in hand.

### (2) `PEquivalent → Equivalent`  (Butcher §380.8631–8638)

Textbook proof: It suffices to show that if `i, j ∈ P_I` in a
P-reducible method (def:381D), then for any IVP, `Yᵢ = Yⱼ` for `h < h₀`.
Calculate the stages by iteration starting with `Yᵢ⁽⁰⁾ = η` for every
`i ∈ {1, ..., s}`. The value of `Yᵢ⁽ᵏ⁾` in iteration `k` is identical
for all `i` in the same partitioned component (by induction on `k`,
using the row-sum-constancy of the partition).

**Blocker**: this requires:
* Banach-fixed-point convergence of the implicit-stage iteration for
  small `h` (specifically: `h ≤ h₀` where `h₀ L < 1` for the Lipschitz
  constant `L`). Mathlib has `ContractingWith`/`fixedPoint` but no
  ergonomic plug-in for the Runge–Kutta stage system; cycle 191-era
  notes flagged this as 2–3 cycles of integration work.
* The iteration-invariant `Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾ for i, j in same block` —
  natural induction on `k`, but needs the row-sum-constancy condition
  (`IsPReducibleVia`) phrased as an iteration-step preservation lemma.

A weaker variant — `PReducesTo → Equivalent` going through
`pReduced`'s output equality — might be reachable in 1-2 cycles if the
Banach fixed-point infrastructure is available, but full
`PEquivalent → Equivalent` requires chaining through the common reduct,
which adds another layer.

### (3) `Equivalent → PEquivalent`  (Butcher §380.8662–8667)

Textbook proof: Suppose two methods are equivalent but not P-equivalent.
Apply the same "combine two tableaux into one + reduce" construction as
in (1). By **thm:381G**, there is an IVP satisfying def:381A's
requirements such that `Yᵢ ≠ Yⱼ` for the two output approximations —
contradicting equivalence.

**Blocker**: same as (1): thm:381G + combine-two-tableaux construction.

## What would unblock each direction

| Direction | Blocker | Estimated cycles |
|---|---|---|
| `PhiEquivalent → PEquivalent` | thm:381G + tableau combine | 4–5 |
| `PEquivalent → Equivalent` | Banach fixed-point + iteration invariant | 2–3 |
| `Equivalent → PEquivalent` | thm:381G + tableau combine | 4–5 |

The two thm:381G-blocked directions could share the combine-construction
infrastructure, so the marginal cost of (3) given (1) is small.

## Related issues

* `.prover-state/issues/p_reduction_confluence_gap.md` — confluence of
  PReducesTo, a different multi-cycle gap in the §380 cluster (needed
  for full def:381E `reducedMethod` uniqueness, not for thm:381H itself).
* `.prover-state/issues/equivalent_self_general_deferred.md` — general
  `Equivalent M M` reflexivity (Banach fixed-point dependency shared
  with deferred direction (2)).
* `.prover-state/issues/reduced_method_deferred.md` — the canonical
  def:381E `reducedMethod` construction (also Banach-fixed-point-adjacent).

## Cycle 200 worker note

The strategy explicitly authorised statement-only ship with up to 4
sorries. Three sorries shipped (1 of 4 directions closed); within
target. No `axiom` declarations introduced. Per-sorry comments in
`Section381.lean` cite the textbook lines and the specific external
dependency.
