import OpenMath.Chapter3.Section301
import OpenMath.Chapter3.Section312

/-!
# Butcher §323 — Internal order of a Runge–Kutta stage (Definition 323A)

This file formalises Definition 323A from Butcher's *Numerical Methods
for Ordinary Differential Equations* (3rd ed., page 203).

## Textbook statement (Definition 323A, quoted verbatim from `def_323A.json`)

> Consider a Runge–Kutta method given by the tableau
>
>     c    A
>          b^T
>
> For a tree `t` and stage `i`, let `Φᵢ(t)` denote the elementary weight
> associated with `t` for the tableau
>
>     c    A
>     eᵢ   A
>
> Stage `i` has 'internal order `q`', if for all trees such that
> `r(t) ≤ q`, `Φᵢ(t) = cᵢ^{r(t)} / γ(t)`.

## Notational decision (READ THIS)

Butcher reuses the symbol `Φᵢ(t)` between §312 and §323, with two
phrasings that look different at first glance:

* §312 — the **internal weight** `Σⱼ aᵢⱼ (Φⱼ D)(t)`, captured by
  `RKTableau.internalWeight`.
* §323 — "the elementary weight of the auxiliary tableau `[c A / eᵢ A]`",
  which expands to `Σⱼ (eᵢ)ⱼ (Φⱼ D)(t) = (Φᵢ D)(t)` of the *original*
  tableau (i.e. the §312 `derivativeWeight`).

These two would normally disagree (the former is a sum of `aᵢⱼ`-weighted
derivative weights; the latter is a single derivative weight). The
textbook line at `extraction/raw_text/ch03.txt:2465` resolves the
ambiguity:

> internal order 1 is equivalent to `cᵢ = Σⱼ aᵢⱼ`

That is, `cᵢ = M.internalWeight τ i` — the §323 `Φᵢ(τ)` is the §312
*internal weight*, not the §312 *derivative weight*. We therefore
interpret §323 `Φᵢ(t) = M.internalWeight t i` throughout this file. The
auxiliary-tableau phrasing is a notational restatement, not a different
function.
-/

namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section310

/-- Butcher §323 Definition 323A — stage `i` of the Runge–Kutta method
`M` has *internal order* `q` if for every rooted tree `t` with
`t.order ≤ q`, the internal weight `Φᵢ(t)` equals
`(M.c i)^{r(t)} / γ(t)`.

See the file docstring for the notational decision identifying §323's
`Φᵢ(t)` with `M.internalWeight t i` (rather than with the §312
`derivativeWeight`). -/
def HasInternalOrder {s : ℕ} (M : RKTableau s) (i : Fin s) (q : ℕ) :
    Prop :=
  ∀ t : RootedTree, t.order ≤ q →
    M.internalWeight t i = (M.c i) ^ t.order / (t.density : ℝ)

/-- Vacuous case: every stage has internal order `0` because no rooted
tree has `r(t) ≤ 0` (orders are positive). -/
theorem hasInternalOrder_zero {s : ℕ} (M : RKTableau s) (i : Fin s) :
    M.HasInternalOrder i 0 := by
  intro t ht
  have hpos : 0 < t.order := RootedTree.order_pos t
  omega

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section323

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312

/- ### Non-vacuous witness

Stage `0` of the 1-stage explicit Euler tableau (`A = 0`, `c = 0`) has
internal order `1`. For every rooted tree `t`:

* LHS: `internalWeight t 0 = Σⱼ A 0 j * derivativeWeight j t = 0`
  because `A = 0`.
* RHS: `(c 0)^{r(t)} / γ(t) = 0^{r(t)} / γ(t) = 0` because `c 0 = 0`
  and `r(t) ≥ 1`.

So both sides are `0`, and the predicate holds for `q = 1` (in fact for
any `q`, but the textbook only asks about `r(t) ≤ q`). -/

/-- Stage 0 of explicit Euler has internal order 1 (Butcher §323
Definition 323A — non-vacuous witness). -/
theorem explicitEuler_hasInternalOrder_one :
    RKTableau.explicitEuler.HasInternalOrder 0 1 := by
  intro t _ht
  have hpos : t.order ≠ 0 := Nat.pos_iff_ne_zero.mp (RootedTree.order_pos t)
  have hLHS : RKTableau.explicitEuler.internalWeight t 0 = 0 := by
    show ∑ j : Fin 1, RKTableau.explicitEuler.A 0 j *
            RKTableau.explicitEuler.derivativeWeight j t = 0
    simp [RKTableau.explicitEuler]
  have hRHS : (RKTableau.explicitEuler.c 0) ^ t.order /
                (t.density : ℝ) = 0 := by
    simp [RKTableau.explicitEuler, zero_pow hpos]
  rw [hLHS, hRHS]

end OpenMath.Chapter3.Section323
