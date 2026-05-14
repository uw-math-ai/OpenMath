# Cycle 204 Results

## Worked on

All three positive priorities from the cycle 204 strategy landed in
`OpenMath/Chapter3/Section381.lean`:

* **P1** — `paddedEuler_equivalent_self` (≤8 LOC corollary).
* **P2** — `RKStageMap_fixedPoint_unique` (Banach-uniqueness
  abstraction, ~25 LOC) + the optional internal refactor of cycle
  203's `equivalent_self` to consume it (−6 LOC net in that proof
  body).
* **P3** — `Equivalent.symm` (stretch deliverable, ~10 LOC of
  tactic body + 5 LOC docstring).

Priority 0 (SKIP §441 Phase C.2 smoke test, 24th consecutive
GPFS-blocked iteration) honoured. No Aristotle traffic this cycle
(none of P1/P2/P3 was well-suited).

## Approach

### P2 first (foundation for P3 + internal refactor)

Inserted `RKStageMap_fixedPoint_unique` immediately after
`RKStageMap_contracting`. The body is the verbatim strategy recipe:
`M.RKStageMap_contracting h hf y₀ h_small` produces a `ContractingWith`
packaging; `eq_or_edist_eq_top_of_fixedPoints` produces the
disjunction; the `edist = ⊤` branch is discharged by `edist_ne_top`.

Then refactored cycle 203's `equivalent_self` (Banach uniqueness
section, ex-lines 1732–1745). The 4-line in-line Banach block plus
the explicit `have hContract` invocation became a one-liner
`M.RKStageMap_fixedPoint_unique h hL y₀ h_small hY_fix hY'_fix`.
The two `Function.IsFixedPt … Y` `have` bindings simplified to
plain `M.RKStageMap h f y₀ Y = Y` (defeq to `IsFixedPt`'s body),
saving one `show` line each.

### P3 — universe-polymorphism gotcha

First attempt at `Equivalent.symm` (verbatim strategy recipe with
`intro N _ _ f L hL y₀; obtain ⟨h₀, h₀_pos, hUniq⟩ := hEq f L hL y₀`)
**failed** with

```
Application type mismatch: The argument
  N
has type Type u_2 of sort `Type (u_2 + 1)`
but is expected to have type Type u_1 of sort `Type (u_1 + 1)`
in the application @hEq N
```

Cause: `Equivalent.{u_1}` is universe-polymorphic (one universe
parameter for `{N : Type*}`). Each reference to `Equivalent` in
the theorem signature gets a *fresh* auto-bound universe, so
`hEq : @Equivalent.{u_1} s s' M M'` and the goal
`@Equivalent.{u_2} s' s M' M` use different universes — there is no
way to instantiate `hEq`'s implicit `N` with the inner `N : Type u_2`
because the universe doesn't unify.

Fix: explicit shared universe annotation on the theorem signature:

```lean
theorem Equivalent.symm.{u} {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (hEq : @Equivalent.{u} s s' M M') :
    @Equivalent.{u} s' s M' M := by
  intro N _ _ f L hL y₀
  obtain ⟨h₀, h₀_pos, hUniq⟩ := hEq f L hL y₀
  ...
```

Both references now share `u`, so the inner `intro N` introduces
`N : Type u` consistent with `hEq`'s expected argument universe.

### P1 — one-liner corollary

`paddedEuler_equivalent_self := paddedEuler.equivalent_self`. The
dot-notation resolves to
`OpenMath.Chapter3.Section312.RKTableau.equivalent_self paddedEuler`
via `open OpenMath.Chapter3.Section312` at the §381 namespace head.

## Result

**SUCCESS — all three priorities land axiom-clean.**

* `lake env lean OpenMath/Chapter3/Section381.lean` — warm rebuild
  **4.6s** (cycle 203 baseline was 6.9s; the internal `equivalent_self`
  refactor shaved ~2s off, plausibly from fewer `funext`/`show` calls).
* `lean_verify` per new theorem, full namespace:
  * `OpenMath.Chapter3.Section312.RKTableau.RKStageMap_fixedPoint_unique`
    → `[propext, Classical.choice, Quot.sound]`.
  * `OpenMath.Chapter3.Section312.RKTableau.equivalent_self`
    (regression check after internal refactor)
    → `[propext, Classical.choice, Quot.sound]`.
  * `OpenMath.Chapter3.Section312.RKTableau.Equivalent.symm`
    → `[propext, Classical.choice, Quot.sound]`.
  * `OpenMath.Chapter3.Section381.paddedEuler_equivalent_self`
    → `[propext, Classical.choice, Quot.sound]`.
* `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.
* Repo-wide `sorry` scan finds only docstring/comment occurrences
  (cycles 112/119/138/etc. historical notes) — no actual tactic
  sorries.
* Tautology scanner (`grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|
  :=\s*id\s*$'`) — 0 hits.
* File size 1957 LOC (was 1914 LOC pre-cycle), net +43 LOC across
  the three new theorems plus docstrings minus the −6 LOC refactor
  saving inside `equivalent_self`.

## Faithfulness check

### `RKStageMap_fixedPoint_unique` (P2, infrastructure)

* **Entity ID**: none (infrastructure abstraction, not a textbook
  named lemma). Corresponds to the standard Banach fixed-point
  uniqueness conclusion as applied to the cycle 202
  `RKStageMap_contracting` instance.
* **Lean statement captures**: same content as the inline Banach
  uniqueness step that cycle 203 used inside `equivalent_self`'s
  body — the abstraction generalises the consumer's view of
  Banach uniqueness without changing the underlying mathematics.
  Smallness hypothesis `|h| * (L : ℝ) * (Σᵢⱼ |M.A i j|) < 1`
  matches `RKStageMap_contracting`'s smallness exactly.
* **Hypothesis-strength check**: no extra hypotheses beyond what
  `RKStageMap_contracting` itself takes plus the two fixed-point
  witnesses `hY, hY'`. No autonomy / smoothness / dimensional
  extras.
* **Definition-smuggling check**: N/A (no new def/class/structure).
* **Tautology check**: conclusion `Y = Y'` is not among the
  hypotheses (the hypotheses speak of fixed-point equations
  `RKStageMap … Y = Y` and `RKStageMap … Y' = Y'`, not of
  `Y = Y'` directly).
* **Identity check**: 4-line tactic body; does real work via the
  `ContractingWith.eq_or_edist_eq_top_of_fixedPoints` + `edist_ne_top`
  pair. Not vacuous.
* **Absent-theorem check**: N/A — no docstring promises.

### `Equivalent.symm` (P3, equivalence-relation closure)

* **Entity ID**: none (infrastructure — Equivalent's symmetry as
  applied to def:381A). The textbook (Butcher §380) does not
  explicitly prove this, but the definition's `y₁ = y₁'` conclusion
  is manifestly symmetric in M and M', so symmetry is an immediate
  consequence of the definition. This is the second of three legs
  of "Equivalent is an equivalence relation" (refl shipped cycle
  203, trans deferred to cycle 205+ per strategy §J).
* **Lean statement captures**: same content. The output-equality
  conclusion `y₁ = y₁'` is symmetric in y₁/y₁', so swapping which
  IsRKOneStep witness is "first" vs "second" and applying `Eq.symm`
  yields a witness for the reversed `M'.Equivalent M` statement.
  No new mathematical content is introduced.
* **Hypothesis-strength check**: no extra hypotheses beyond the
  Equivalent witness `hEq`.
* **Definition-smuggling check**: N/A.
* **Tautology check**: conclusion `M'.Equivalent M` is not among
  the hypotheses (`hEq : M.Equivalent M'`, with M and M' swapped).
* **Identity check**: 4-line tactic body; does real work by
  destructuring `hEq` and reconstructing with swapped IsRKOneStep
  arguments. Not vacuous.
* **Absent-theorem check**: N/A.

### `paddedEuler_equivalent_self` (P1, non-vacuity witness)

* **Entity ID**: def:381A (non-vacuity witness specialised to
  `paddedEuler : RKTableau 2`). Quoted statement from
  `extraction/formalization_data/entities/def_381A.json`:
  > Two Runge–Kutta methods are 'equivalent' if, for any initial
  > value problem defined by an autonomous function f satisfying a
  > Lipschitz condition, and an initial value y0, there exists
  > h0 > 0 such that the result computed by the first method is
  > identical with the result computed by the second method, if
  > h ≤ h0.
* **Lean statement captures**: same content — direct specialisation
  of `equivalent_self` (cycle 203) at `M := paddedEuler`. The reflexive
  case `paddedEuler.Equivalent paddedEuler` carries no extra
  hypotheses beyond what cycle 203's general lemma needs (which is:
  none, since reflexivity of Equivalent is unconditional given the
  Banach foundation). Strengthens cycle 030's
  `equivalent_explicitEuler_self` (1-stage explicit-Euler
  reflexivity) to the heterogeneous-stage `s = 2` setting.
* **Hypothesis-strength check**: no hypotheses (the proof body is a
  single term application `paddedEuler.equivalent_self`).
* **Definition-smuggling check**: N/A.
* **Tautology check**: N/A (no hypotheses, conclusion is the goal
  itself).
* **Identity check**: a single-term proof, but it is *not* an
  `exact h_…` re-export of a hypothesis — it is a specialisation
  of cycle 203's general theorem at a specific tableau. Does real
  work in the sense that the underlying Banach foundation fires at
  `M := paddedEuler`.
* **Absent-theorem check**: N/A.

### `equivalent_self` (regression — refactored body)

* No change to the statement, threshold, or axiom profile. Body
  trimmed by ~6 LOC by consuming P2's new uniqueness lemma. Cycle
  203's faithfulness check (see `cycle_203.md`) still applies
  verbatim.

## Dead ends

1. **First-attempt `Equivalent.symm` without universe annotation**
   — failed with the universe-mismatch error documented above.
   Resolved by `.{u}` explicit shared annotation. The
   `(N := N)` named-argument annotation alone (intermediate attempt)
   was insufficient because it merely supplies the *value* of the
   implicit, not the universe-level constraint between the two
   `Equivalent` references in the signature.

## Discovery

1. **Universe-polymorphism gotcha for `Equivalent` consumers**. Any
   future theorem that takes an `Equivalent` hypothesis AND
   concludes an `Equivalent` (or otherwise references the bound
   `{N : Type*}` in both positions) must use an explicit shared
   universe `.{u}` annotation. Without it, Lean's auto-bound
   universes pick fresh levels per reference and instantiation
   fails. Worth applying preemptively to `Equivalent.trans` in
   cycle 205+.

2. **`Function.IsFixedPt` defeq-collapse**. The cycle 203 inline
   uniqueness used `Function.IsFixedPt (M.RKStageMap h f y₀) Y`
   typed bindings; for the new abstraction
   `RKStageMap_fixedPoint_unique`, plain `M.RKStageMap h f y₀ Y = Y`
   typed bindings work — `IsFixedPt f x ↔ f x = x` is definitional,
   so the `ContractingWith.eq_or_edist_eq_top_of_fixedPoints` lemma
   accepts either form. Saved one `show … = Y` line per fixed-point
   binding in the refactored `equivalent_self`.

3. **`paddedEuler.equivalent_self` dot-notation resolves cleanly**
   across the namespace boundary. The §381 namespace has
   `open OpenMath.Chapter3.Section312`, so the `RKTableau` namespace
   is in scope, and `paddedEuler.equivalent_self` resolves to
   `RKTableau.equivalent_self paddedEuler` without needing the
   fully-qualified fallback that the strategy hedged against.

## Suggested next approach

Cycle 205 candidates, ordered by leverage:

1. **`RKStageMap_fixedPoint_exists`** (Banach *existence* — the
   missing leg of `ContractingWith`'s output). Mathlib provides
   `ContractingWith.fixedPoint` / `efixedPoint`; the helper would
   package "for every starting tuple `Y₀`, the iteration converges
   to a (unique by cycle 204 P2) fixed point" as the existence
   witness needed for `Equivalent.trans` and for `PReducesTo →
   Equivalent`. Estimated ~30 LOC.

2. **`Equivalent.trans`** (third leg of equivalence-relation
   closure). Once `RKStageMap_fixedPoint_exists` lands, trans is
   ~15 LOC: threshold for the composition is `min h₀ h₀'`; both
   methods produce *some* output via the existence helper; uniqueness
   bridges via two applications of `hEq`/`hEq'`. Together with cycles
   203 (`equivalent_self`) and 204 (`Equivalent.symm`), this would
   close "`Equivalent` is an equivalence relation" — useful for any
   future quotient-by-equivalence work.

3. **One direction of `thm:381H` (PEquivalent → Equivalent)** —
   direction 2 of 4 in `thm_381H_deferred.md`. The cycle 203 task
   results flagged this as Priority 2 for cycle 204 but the
   strategy explicitly out-of-scoped it; cycle 204 P2's
   abstraction (`RKStageMap_fixedPoint_unique`) is the right
   preparatory step, so cycle 205 can attempt it with cleaner
   infrastructure in hand. Still ~1.5 cycles per the cycle 200
   precedent; plan accordingly.

4. **Tighter sup-norm row bound in `RKStageMap_lipschitz`**
   (cosmetic, optional — admits a larger `h₀` threshold but does
   not change reachable theorems). Lowest priority.

5. **§441 Phase C.2 GPFS smoke test**: still blocked, 25th
   consecutive timeout would be at risk; recommend continuing the
   skip until the loop-maintainer surfaces a recovery signal.
