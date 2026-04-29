# Cycle 573 Results

## Worked on

`G1.mul_assoc` and the noncomputable `Monoid (G1 p)` instance in
`OpenMath/ButcherGroup.lean`.

## Approach

Checked the ready Aristotle bundle `14b9915a-...` first. It only contains
cycle-561 `QuadMixedOneThree*` slice work and creates/uses the obsolete
`OpenMath.ButcherGroup.Section384SlicesQuadMixed` path, so I did not
incorporate it per the cycle-573 strategy.

Used the required sorry-first flow for `G1.mul_assoc`: three quotient
inductions reduce the goal to representatives, `simp only [mul_mk]`
exposes the `IsG1Equiv` obligation, and `Quotient.sound` reduces it to
pointwise equality of `bSeriesHom`. The existing
`QuotEquiv.bSeriesHom_assoc` closes that equality directly.

After `mul_assoc` typechecked, the bare `Monoid (G1 p)` instance elaborated
without supplying explicit `npow` fields.

## Result

SUCCESS.

New declarations:
- `ButcherTableau.G1.mul_assoc`
- `ButcherTableau.G1.instMonoid`

Updated `plan.md` to record that cycles 572-573 close `G1 p` at the monoid
level and that remaining §38 group work is the unit-stage inverse/subgroup
layer.

Verification:
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build` — succeeds.
- `lean_verify ButcherTableau.G1.mul_assoc` — axioms only
  `propext`, `Classical.choice`, `Quot.sound`; no warnings.
- `lean_verify ButcherTableau.G1.instMonoid` — axioms only
  `propext`, `Classical.choice`, `Quot.sound`; no warnings.

## Dead ends

Aristotle submission for the single remaining proof hole returned HTTP 429
immediately:

`You have too many requests in progress. Please cancel or wait for a project
to complete before starting a new one.`

No job was queued, so there was no result to wait for or transplant. The
manual proof was short and followed the planned existing associativity
witness.

## Discovery

The `Monoid` structure in this Mathlib version does not require explicit
`npow` fields in the instance declaration; the default fields are inferred.

At the quotient level, `QuotEquiv.bSeriesHom_assoc` is exactly the equality
shape produced by `Quotient.sound` for `G1.mul_assoc`, including the sigma
representatives' `.snd.bSeriesHom`.

## Suggested next approach

Cycle 574 should pivot out of the `G1` monoid work. The next §38 work, when
scheduled, is the unit-stage inverse/subgroup layer; otherwise follow the
planner's suggested pivot toward Butcher §500 general linear methods.
