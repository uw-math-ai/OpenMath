# Issue: thm:381H — three of four iff directions deferred

## Status

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
