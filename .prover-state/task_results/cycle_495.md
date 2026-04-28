# Cycle 495 Results

## Worked on

Opened Butcher §38 in a new tracked module:

- `OpenMath/ButcherGroup.lean`
- `OpenMath.lean` root import
- §38 ledger entries in `plan.md`

The new Lean surface covers §380, §381, and the zero-stage identity part of
§387:

- `relabel`
- `reindexStages`
- `IsRKEquivalent`
- `relabel_comp`
- `IsRKEquivalent.refl/symm/trans`
- `IsRKEquivalent.equivalence`
- `rkEquivalentSetoid`
- `ButcherProduct`
- `butcherProduct_identity_left/right`
- deferred `butcherProduct_assoc_modEquiv`

## Approach

Followed the requested sorry-first shape.  `ButcherProduct` uses
`Fin.addCases` directly for the four coefficient blocks:

```text
[ γ₁ A₁   0  ]
[ γ₁ b₁  γ₂ A₂ ]
```

with `b = [γ₁ b₁, γ₂ b₂]` and `c = [γ₁ c₁, γ₁ + γ₂ c₂]`.

The relabelling proofs were closed by reducing tableaux to their three
component functions.  The composition lemma has the Lean orientation

```lean
relabel (σ.trans τ) t = relabel σ (relabel τ t)
```

so `IsRKEquivalent.trans` uses witness `τ.trans σ` after substituting the two
equivalence witnesses.

For identities, the right identity can state directly against `t` because
`s + 0` is definitional enough for the tableau type.  The left identity needs
the canonical `Fin s ≃ Fin (0+s)` reindex:

```lean
reindexStages (finCongr (Nat.zero_add s).symm) t
```

Two private `Fin.addCases` lemmas for zero left/right blocks close the
otherwise-stuck impossible branch rewrites.

## Result

SUCCESS.  `lake env lean OpenMath/ButcherGroup.lean` succeeds.  The only
tracked `sorry` is the planned §382 theorem
`butcherProduct_assoc_modEquiv`.

`OpenMath.lean` now imports `OpenMath.ButcherGroup`.

## Aristotle usage

Submitted exactly five Aristotle jobs after the local scaffold compiled, then
waited once for 30 minutes via `sleep 1800` before checking status:

- `d8b55aa9-56ae-4880-b48f-77f32effbca7`:
  `aristotle_butcherProduct_identity_left` — `COMPLETE_WITH_ERRORS`.
- `75e7effc-e77f-468c-b676-0fb5aeeacfa2`:
  `aristotle_butcherProduct_identity_right` — `COMPLETE_WITH_ERRORS`.
- `8314c9b0-d74e-41dc-8ff6-4da6f7896a93`:
  `butcherProduct_assoc_modEquiv` — still `IN_PROGRESS` at 17% after the
  required wait.
- `344f2d53-1a38-4b4a-a2dc-bc720506bd3e`:
  `aristotle_relabel_comp` — `COMPLETE_WITH_ERRORS`.
- `8700ceb0-5cb6-422e-940d-8519c9d17134`:
  `aristotle_IsRKEquivalent_equivalence` — still `IN_PROGRESS` at 9% after
  the required wait.

No Aristotle proof was incorporated.  The three completed jobs did not return
a usable proof through the available status channel, and the two remaining
jobs were not polled again.

## Dead ends

The main theorem statement for associativity is type-correct only after a
`Nat.add_assoc` transport, because the two nestings have stage counts
`(s+t)+u` and `s+(t+u)`.

A more serious issue is that the current scaffold's four weight parameters do
not appear to state a true associativity law for generic real weights: the
left nesting gives weights `[γ₁δ₁, γ₁δ₂, γ₂]`, while the right nesting gives
`[γ₁, γ₂δ₁, γ₂δ₂]`.  This is recorded in
`.prover-state/issues/cycle_495_butcher_group_assoc_weights.md`.

## Discovery

- `Fin.addCases_left/right` are useful only after exposing the index as
  `Fin.castAdd` or `Fin.natAdd`; for zero-sided products, small helper lemmas
  rewriting arbitrary `Fin (0+s)` / `Fin (s+0)` indices are much cleaner.
- The stage relabelling action is contravariant relative to sequential
  relabellings, hence the transitive witness is `τ.trans σ`, not
  `σ.trans τ`.
- A fixed-stage `Setoid (ButcherTableau s)` is now available for quotient
  work in later cycles.

## Plan rotation

Updated the §38 ledger:

- §380 marked `[~]` with `ButcherProduct`.
- §381 marked `[~]` with `relabel`, `IsRKEquivalent`, and
  `IsRKEquivalent.refl/symm/trans`.
- §382 left `[ ]` with a reference to the deferred
  `butcherProduct_assoc_modEquiv` sorry.
- §387 marked `[~]` for `butcherProduct_identity_left/right`; inverse and
  power remain open.

The `## Current Target` body was left unchanged, and no Backlog item was
promoted.

## Suggested next approach

Before trying to close `butcherProduct_assoc_modEquiv`, revise the §382
statement or introduce a ternary-product lemma so the substep weights match
under reassociation.  After that, the remaining proof should be the expected
`Fin` associator / `finSumFinEquiv` bookkeeping plus componentwise extensional
equality.
