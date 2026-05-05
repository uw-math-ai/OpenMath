# Cycle 130 Results

## Worked on

* **Primary**: `def:542A` — *Runge–Kutta stability* of a general linear
  method (Butcher §542, p. 445). New predicate
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.IsRKStable` plus
  non-vacuity witness `explicitEulerGLM_isRKStable`.
* **Secondary**: two mirror lemmas for the implicit-midpoint GLM in
  `OpenMath/Chapter5/Section510.lean`:
  `implicitMidpointGLM_isStable` and
  `implicitMidpointGLM_isConsistent` (rounding out the existing
  `implicitMidpointGLM_isPreconsistent` triple).

## Approach

### Primary (`def:542A`)

Encoded the textbook factorisation directly:

```lean
def GeneralLinearMethod.IsRKStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ R : ℂ → ℂ, ∀ w z : ℂ,
    M.stabilityFunction w z = w ^ (r - 1) * (w - R z)
```

`M.stabilityFunction w z` is the existing `def:520C` `Φ(w, z) =
det(w·I − M(z))` (equation 542a). The textbook calls `R` rational, but
the predicate's content is the *factorisation existing*; rationality is
deferred to downstream theorems (e.g. `def:551A`) — pre-emptively
forcing `RatFunc ℂ` would be hypothesis smuggling.

Witness: `explicitEulerGLM` has `r = 1`, so the equation reduces to
`Φ(w, z) = w − R(z)` after `w^0 = 1`. Combined with the existing
`explicitEulerGLM_stabilityFunction` (`Φ = w − 1 − z`), the factorisation
holds with `R(z) := 1 + z`. Closer:
```lean
refine ⟨fun z => 1 + z, ?_⟩
intro w z
rw [explicitEulerGLM_stabilityFunction]
simp [pow_zero]
ring
```
Closed first try; no fallback ladder needed.

### Secondary

Both `implicitMidpointGLM_isStable` and `implicitMidpointGLM_isConsistent`
are verbatim copies of `explicitEulerGLM_isStable` /
`explicitEulerGLM_isConsistent` modulo the GLM structure name. Because
`implicitMidpointGLM`'s `B`, `U`, `V` blocks coincide with explicit
Euler's (`!![1]` for all three; only `A` differs at `!![1/2]` vs
`!![0]`), the proofs go through identically — `IsStable` only references
`V`, and the consistency equation `B·𝟙 + V·v = u + v` only references
`B` and `V`. ≤ 2-line deviation, well within the strategy's stop
threshold.

## Result

**SUCCESS** for both primary and secondary.

* `lake env lean OpenMath/Chapter5/Section520.lean` — clean (exit 0).
* `lake env lean OpenMath/Chapter5/Section510.lean` — clean (exit 0).
* `lake build OpenMath.Chapter5.Section510 OpenMath.Chapter5.Section520`
  — full project rebuilds (2772 jobs).
* `#print axioms` (after `lake build` to refresh `.olean` cache):
  ```
  IsRKStable                       : [propext, Classical.choice, Quot.sound]
  explicitEulerGLM_isRKStable      : [propext, Classical.choice, Quot.sound]
  implicitMidpointGLM_isStable     : [propext, Classical.choice, Quot.sound]
  implicitMidpointGLM_isConsistent : [propext, Classical.choice, Quot.sound]
  ```
  All four axiom-clean (no `sorryAx`, no custom axioms).

Files updated:
* `OpenMath/Chapter5/Section520.lean` — `IsRKStable` + Euler witness
  inserted after `explicitEulerGLM_hasStabilityOrder_one`.
* `OpenMath/Chapter5/Section510.lean` — two implicit-midpoint witness
  theorems appended after `implicitMidpointGLM_isPreconsistent`.
* `extraction/formalization_data/lean_status.json` — `def:542A` row
  updated to `formalized` with `lean_file` /  `lean_symbol`.
* `plan.md` — `def:542A` checkmarked in §54 with annotation; progress
  bumped 66 → 67.

## Faithfulness check

### `def:542A` — `GeneralLinearMethod.IsRKStable`

Entity ID and textbook statement (quoted from
`extraction/formalization_data/entities/def_542A.json`):

> A general linear method $(A, U, B, V)$ has \emph{Runge--Kutta
> stability} (RK stability) if its characteristic polynomial, given by
> $\Phi(w,z)=\det(wI-V-zB(I-zA)^{-1}U)$, has the form
> $\Phi(w,z) = w^{r-1}(w - R(z))$.
> The rational function $R(z)$ is the \emph{stability function} of the
> method.

Lean statement captures: **same content** — `M.stabilityFunction w z`
is `det(w·I − M(z))` per `def:520C` (where `M(z) = V + zB(I−zA)⁻¹U`),
so `M.stabilityFunction = Φ` exactly. The factorisation
`w^(r-1) * (w − R z)` mirrors the textbook verbatim.

Encoding deviations (documented in the docstring):

* `R : ℂ → ℂ` rather than `RatFunc ℂ`. The textbook *describes* `R` as
  rational, but the *predicate* asserts only the factorisation; whether
  `R` is rational is a downstream lemma. Forcing `RatFunc ℂ` here
  would either (a) fail to capture rationality if `R` is not extracted
  carefully, or (b) build a stronger predicate than the textbook
  states. Plain `ℂ → ℂ` is the cleanest faithful encoding.
* `r − 1` is `Nat.sub`, so `r = 0` gives `r − 1 = 0` and the
  factorisation reduces to `Φ(w, z) = w − R(z)`. As argued in the
  docstring, the `r = 0` case is unsatisfiable (because
  `Φ(w, z) = det(w·1 − M(z)) = 1` over the empty matrix is constant in
  `w`), correctly making the trivial `r = 0` GLM never RK-stable. This
  matches the textbook's implicit `r ≥ 1`.

Definition smuggling check: the predicate asserts the *existence* of a
factorisation with the textbook shape, not the existence of `R`
extracted as `Φ(0, z)` or any other algebraic projection. The
factorisation has real algebraic content (it constrains the
characteristic polynomial's structure as a polynomial in `w`). ✓

Tautology check: `IsRKStable` is purely existential over `R`; it has
no hypotheses to be tautologous with. ✓

### `explicitEulerGLM_isRKStable`

This theorem witnesses non-vacuity by constructing `R(z) := 1 + z`
*ex nihilo* and verifying the factorisation via the existing
`explicitEulerGLM_stabilityFunction` lemma. The conclusion is
`explicitEulerGLM.IsRKStable`; no hypotheses to compare to. The proof
is genuine algebraic identity (`w − 1 − z = w^0 · (w − (1 + z))`),
not `exact h` re-export. ✓

### `implicitMidpointGLM_isStable`, `implicitMidpointGLM_isConsistent`

* `IsStable` quantifies a bound on `‖V^n‖`, so the proof reduces `V` to
  the identity `1 × 1` matrix and uses `one_pow`. Genuine computation,
  not vacuous. ✓
* `IsConsistent` produces the witnesses `u = 1`, `v = 0` and verifies
  the four conditions of `def:510B` by `simp` on `mulVec` /
  `dotProduct`. Genuine computation. ✓

Both theorems mirror the existing explicit-Euler analogues; the textbook
has no separate "implicit midpoint is stable/consistent" statement
because consistency/stability are GLM properties, not method-specific.
The mirror lemmas are non-vacuity upkeep, not new mathematics — they
ensure the implicit-midpoint witness slot is fully filled out.

## Dead ends

None. The strategy's predicted `simp [pow_zero]; ring` closer worked
on the first attempt for the primary witness; the fallback ladder in
the strategy was not needed.

## Discovery

* `pow_zero` plus `ring` is sufficient to close the `r − 1 = 0` case
  for `r = 1` even when `r − 1` is `Nat.sub`. The `simp` call resolves
  `1 - 1` to `0` automatically; no explicit `Nat.sub_self` rewrite is
  needed.
* The `r = 0` non-existence behaviour of `IsRKStable` (correct: an
  empty-matrix GLM is never RK-stable because `Φ ≡ 1`) is captured
  *for free* by `Nat.sub`'s saturation at `0`. No defensive
  `(r_pos : 0 < r)` hypothesis required.

## Suggested next approach

Two natural follow-ups (planner's call):

1. **`def:551A` "Inherent Runge–Kutta stability"** is now unblocked.
   Its dependency list points to `def:542A`, which we just landed.
   This is the natural next leaf in §55.
2. **`thm:541A` "The types of DIMSIM methods"** in §541 — depends only
   on §510 / §520 infrastructure that's already in place. Worth
   scoping for tractability.
3. The substantive `implicitMidpointGLM_isRKStable` witness (with
   `R(z) = (1 + z/2)/(1 − z/2)`) is still deferred — it requires
   computing `(I − z/2)⁻¹` over `ℂ` for a `1×1` matrix, which is a
   ~20-line proof using `Matrix.det_fin_one` and field algebra. Useful
   as a substantive non-vacuity for downstream lemmas that require a
   non-trivial `R`, but not load-bearing now that the explicit-Euler
   `r = 1` slot is filled.

The cycle 129 task results' note about the implicit-midpoint
`IsStable` / `IsConsistent` mirror lemmas is now resolved — both
landed as part of this cycle's secondary deliverable.
