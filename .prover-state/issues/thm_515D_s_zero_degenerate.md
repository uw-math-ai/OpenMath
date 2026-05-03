# Issue: `thm:515D` `s = 0` degenerate case

## Resolution (cycle 109) — RESOLVED via Option D

Cycle 109 strengthened the theorem signature with an `(hs : 0 < s)`
precondition, eliminating the degenerate `s = 0` branch. The
faithfulness divergence is documented in
`OpenMath/Chapter5/Section515.lean` at the docstring of
`GeneralLinearMethod.stable_consistent_isConvergent` and in the
`thm:515D` row of
`extraction/formalization_data/lean_status.json`.

The original Blocker / Context / What was tried / Possible solutions
sections are kept below as a record of the analysis that led to the
divergence decision.

## Blocker

The main theorem `GeneralLinearMethod.stable_consistent_isConvergent`
in `OpenMath/Chapter5/Section515.lean` (cycle 108 scaffold) carries a
single inline `sorry` for the degenerate case where the GLM has zero
internal stages (`s = 0`).

In that case:

* `M.U *ᵥ u = (fun _ : Fin 0 => 1)` is automatically true for any
  `u : Fin r → ℝ` (both sides are the unique empty function from
  `Fin 0 → ℝ`, which extensionally equal `0`). So the
  preconsistency equation `U·u = 𝟙` does **not** force `u ≠ 0`.
* `IsConsistent`'s witness `u` may therefore be `0`, but
  `IsConvergent` requires `u ≠ 0`.
* For `r = 0`, the type `Fin 0 → ℝ` has only one inhabitant (the
  empty function = `0`), so `u ≠ 0` is *literally false* and the
  IsConvergent statement is vacuously False — i.e. the theorem
  `stable + consistent ⇒ convergent` is False as stated for `(s, r) =
  (0, 0)` GLMs.

## Context

The textbook (Butcher §515) implicitly assumes `s ≥ 1` (a GLM with
no stages doesn't have the `c = A·𝟙 + U·v` abscissae structure
analyzed in lem:515A/lem:515B), but the formalization's
`GeneralLinearMethod` structure permits `s = 0` and `r = 0`.

The cycle-108 strategy advised "for s = 0 vacuous so still fine" for
the inline `u ≠ 0` proof, but on closer inspection this is
incorrect: the equation `U·u = 𝟙` collapses to the trivial empty-
function identity when `s = 0`, so we cannot derive `u ≠ 0` from
preconsistency in that case.

## What was tried

1. **Direct contradiction via `(M.U *ᵥ u) i = 1` evaluation.** Works
   for `0 < s` (one-line via `congrFun hUu ⟨0, hs⟩` + `simp`).
   Fails for `s = 0` because `Fin 0` has no inhabitants.
2. **Picking a different `u` from `IsConsistent`.** The consistency
   `u` need not be the IsConvergent witness, but for `s = 0`,
   `r = 0`, no `u ≠ 0` exists, so this approach fails outright.

## Possible solutions

### Option A — Add a structural hypothesis `[NeZero s]` to thm:515D

Justify as: Butcher's GLM analysis implicitly assumes at least one
internal stage. A `(0, r)` GLM has degenerate dynamics
(`y_{n+1} = V·y_n`, no `f`-dependence) and is not the object of
study in §515.

* **Pro**: Cleanest mathematical fix; the `s ≥ 1` case is the only
  one that matches Butcher's narrative.
* **Con**: Diverges from the textbook's flat statement "*A* stable
  and consistent GLM is convergent" — explicitly disallowed by
  the cycle-108 strategy.

### Option B — Derive a contradiction from `IsConsistent` for `s = r = 0`

For `(s, r) = (0, 0)`, `IsConsistent` is vacuously satisfied
(every component is empty). So we cannot derive False from
`IsConsistent` alone.

For `s = 0, r ≥ 1`, IsConsistent's `B·𝟙 + V·v = u + v` with
`B : Matrix (Fin r) (Fin 0) ℝ = 0` simplifies to `V·v = u + v`. We
need to find a non-trivial constraint that forces `u ≠ 0`. This
would require reasoning about `V·u = u` (preconsistency) plus
spectral conditions, which adds machinery.

* **Pro**: Keeps the textbook signature.
* **Con**: Significant new work, not obviously provable.

### Option C — Pick a different `u` in the `s = 0` case

Instead of using IsConsistent's `u`, pick any `u ≠ 0` (e.g.
`u = (fun _ => 1)` if `r ≥ 1`). But then verifying the limit
`Y n n → u · yex(x)` for an arbitrary GLM iteration becomes the
hard part, and may not be provable at all.

* **Pro**: Keeps the textbook signature.
* **Con**: Almost certainly not provable for arbitrary `s = 0` GLMs.

### Option D — Recommend Option A + faithfulness divergence note

Add `(_hs : 0 < s)` (or `[NeZero s]`) to the theorem signature with
a docstring note: "Butcher implicitly assumes at least one internal
stage; the `s = 0` case is degenerate and not in scope". Mark the
divergence in `lean_status.json` and the cycle results.

## Recommendation for cycle 109+

Option D (add `0 < s`) is the simplest and most honest fix.
Alternatively, leave the inline `sorry` as a permanent gap (Option
B/C deferred indefinitely) and document the edge case in the
theorem's docstring.

## Affected file/symbol

* `OpenMath/Chapter5/Section515.lean:1566` — inline `sorry` in the
  `s = 0` branch of
  `GeneralLinearMethod.stable_consistent_isConvergent`.
