import Mathlib

/-! Cycle 080 — Aristotle target 1/4 (the bijection).

Key combinatorial bijection on multisets: for fixed `S`, summing first
over `Q ≤ S` and then over `T ≤ S - Q` is the same as summing first over
`R ≤ S` and then over `Q ≤ R` (with the implicit identification
`T = R - Q`).

This is the multiset analogue of the textbook reindexing
`Σ_{Q ⊑ R ⊑ S} f(R-Q, Q) = Σ_{Q ⊑ S, T ⊑ S-Q} f(T, Q)` via the
bijection `(Q, T) ↔ (Q + T, Q)`.

Generic type — written for any `α : Type*` with `DecidableEq` (i.e.
this is a pure Multiset library lemma; not specific to rooted trees).
-/

variable {α : Type*} [DecidableEq α]

/-- Key combinatorial bijection on multisets. -/
theorem double_powerset_swap
    (S : Multiset α)
    (f : Multiset α → Multiset α → ℝ) :
    ((S.powerset).bind
        (fun Q => (S - Q).powerset.map (fun T => f Q T))).sum
      = ((S.powerset).bind
          (fun R => R.powerset.map (fun Q => f Q (R - Q)))).sum := by
  sorry
