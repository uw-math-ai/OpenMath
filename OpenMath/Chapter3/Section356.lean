import OpenMath.Chapter3.Section312

/-!
# Butcher §356 — DJ-reducibility and DJ-irreducibility (Definitions 356B and 356A)

This file formalises **Definition 356B** from Butcher's *Numerical
Methods for Ordinary Differential Equations* (3rd ed., page 268), and
the *DJ-irreducibility* component of **Definition 356A** (same page).

## Definition 356B textbook statement (quoted verbatim from `def_356B.json`)

> A Runge–Kutta method is 'DJ-reducible' if there exists a partition
> of the stages
>     {1, 2, …, s} = S ∪ S₀ ,
> with `S₀` non-empty, such that if `i ∈ S` and `j ∈ S₀`,
>     `b_j = 0` and `a_{ij} = 0`.
>
> The 'reduced method' is the method formed by deleting all stages
> numbered by members of the set `S₀`.

## Definition 356A second-named-concept (quoted verbatim from `def_356A.json`)

> we identify 'irreducibility in the sense of Dahlquist and Jeltsch',
> or 'DJ-irreducibility', (Dahlquist and Jeltsch, 1979) as the
> property that a tableau cannot be reduced in the sense of
> Definition 356B.

## Faithfulness notes

* **Both-sides-non-empty strengthening of `def:356B`.** Butcher writes
  "with `S₀` non-empty" but is silent on whether `S` must be non-empty.
  Read literally, taking `S = ∅, S₀ = {1, …, s}` makes the conjunction
  "if `i ∈ S` and `j ∈ S₀`" vacuously true for every method — so
  *every* tableau would be DJ-reducible and DJ-irreducibility would
  have no models. Butcher's §357 usage (e.g. `cor:356D` asserting
  `b_i > 0` *under* DJ-irreducibility, which would be vacuous on the
  literal reading) treats DJ-irreducibility as a non-vacuous
  strengthening. We therefore additionally require `S` non-empty in
  `IsDJReducible`. This mirrors the analogous `P₀ ≠ ∅` strengthening
  on `IsZeroReducible` in `Section381.lean`.
* **AN-stability deferral (`def:356A`).** Definition 356A introduces
  *two* named concepts: AN-stability (a complex matrix-valued
  resolvent boundedness condition) and DJ-irreducibility. This file
  formalises only the DJ-irreducibility component. AN-stability is
  deferred to a dedicated cycle — see
  `.prover-state/issues/AN_stability_deferred.md`.
* **Why this file does not import `Section381`.** Mathematically
  DJ-reducibility is a special case of 0-reducibility (with both
  partition sides non-empty), but the textbook positions
  DJ-reducibility *before* the §381 unified treatment. Keeping
  `Section356` independent of `Section381` matches the textbook order
  and avoids a forward-importing tangle.
-/

namespace OpenMath.Chapter3.Section312.RKTableau

/-- Predicate form of Butcher §356 Definition 356B: the 2-block
partition `S := {i | inS i = true}`, `S₀ := {i | inS i = false}`
witnesses DJ-reducibility of `M` when, for every `j ∈ S₀`, both
`b_j = 0` and `A i j = 0` for every `i ∈ S`.

This factors out only the conjunctive zero conditions on the partition;
the both-sides-non-empty side condition lives in `IsDJReducible` so
that `IsDJReducibleVia` may be re-used by future "reduced method"
constructions that do not need the non-emptiness premise. -/
def IsDJReducibleVia {s : ℕ}
    (M : RKTableau s) (inS : Fin s → Bool) : Prop :=
  ∀ j : Fin s, inS j = false →
      M.b j = 0 ∧ ∀ i : Fin s, inS i = true → M.A i j = 0

/-- Butcher §356 Definition 356B — a Runge–Kutta method is
*DJ-reducible* if there is a 2-block partition (encoded as a Boolean
predicate `inS`) with **both** `S` and `S₀` non-empty satisfying the
zero conditions of `IsDJReducibleVia`. The both-sides-non-empty
strengthening is justified in the file docstring (without it, every
tableau is trivially DJ-reducible via `S = ∅`, and DJ-irreducibility
is vacuous). -/
def IsDJReducible {s : ℕ} (M : RKTableau s) : Prop :=
  ∃ inS : Fin s → Bool,
    (∃ i, inS i = true) ∧ (∃ i, inS i = false) ∧ M.IsDJReducibleVia inS

/-- Butcher §356 Definition 356A (DJ-irreducibility component) — a
Runge–Kutta method is *DJ-irreducible* if it is not DJ-reducible
(`def:356B`). The AN-stability component of Definition 356A is
deferred; see the file docstring. -/
def IsDJIrreducible {s : ℕ} (M : RKTableau s) : Prop :=
  ¬ M.IsDJReducible

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section356

open OpenMath.Chapter3.Section312

/- ### Non-vacuous witness for DJ-irreducibility

The 1-stage `RKTableau.explicitEuler` tableau is DJ-irreducible:
any partition of `Fin 1` into both a non-empty `S` and a non-empty
`S₀` would require the unique stage `0` to lie in both sides — but
`inS 0` is a single Boolean, so it cannot be both `true` and `false`. -/

/-- `RKTableau.explicitEuler` is DJ-irreducible (def:356A,
DJ-irreducibility component). -/
theorem explicitEuler_isDJIrreducible :
    RKTableau.explicitEuler.IsDJIrreducible := by
  rintro ⟨inS, ⟨i, hi⟩, ⟨j, hj⟩, _⟩
  fin_cases i
  fin_cases j
  simp_all

/- ### Non-vacuous witness for DJ-reducibility

The 2-stage `paddedEuler` tableau (`A = 0`, `b = ![1, 0]`, `c = 0`)
performs the same computation as `explicitEuler` and is DJ-reducible
via the partition `inS := ![true, false]` (so `S = {0}`, `S₀ = {1}`).
The zero conditions hold because `paddedEuler.b 1 = 0` and
`paddedEuler.A 0 1 = 0` (in fact `A` is identically zero).

This duplicates the `Section381.lean` `paddedEuler` definition; we
keep a local copy here so that `Section356` does not depend on
`Section381` (textbook order). A future refactor could share the
witness via a dedicated helpers file. -/

/-- Local 2-stage padded version of explicit Euler. See
`OpenMath.Chapter3.Section381.paddedEuler` for the same definition
in §380. -/
def paddedEuler : RKTableau 2 where
  A := 0
  b := ![1, 0]
  c := 0

/-- `paddedEuler` is DJ-reducible-via the partition `![true, false]`
(i.e. `S = {0}`, `S₀ = {1}`). -/
example : paddedEuler.IsDJReducibleVia ![true, false] := by
  intro j hj
  fin_cases j
  · simp at hj
  · refine ⟨rfl, ?_⟩
    intro i _
    simp [paddedEuler]

/-- Hence `paddedEuler` is DJ-reducible. -/
example : paddedEuler.IsDJReducible :=
  ⟨![true, false], ⟨0, by decide⟩, ⟨1, by decide⟩, by
    intro j hj
    fin_cases j
    · simp at hj
    · refine ⟨rfl, ?_⟩
      intro i _
      simp [paddedEuler]⟩

end OpenMath.Chapter3.Section356
