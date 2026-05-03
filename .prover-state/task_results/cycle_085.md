# Cycle 085 Results

## Worked on
`def:510B` (consistent GLM, Butcher §510, p. 406). Added the
`GeneralLinearMethod.IsConsistent` predicate, the projection lemma
`IsConsistent.isPreconsistent`, and the non-vacuity witness
`explicitEulerGLM_isConsistent` to `OpenMath/Chapter5/Section510.lean`.

## Approach
Followed the planner strategy verbatim:

1. Read `extraction/formalization_data/entities/def_510B.json` to
   confirm the textbook statement: a GLM is consistent if it is
   preconsistent with vector `u` and there exists `v` with
   `B·𝟙 + V·v = u + v` (eq. 510c).
2. Inserted `IsConsistent` immediately after `IsStable`, encoded as
   `∃ u v : Fin r → ℝ, (V u = u ∧ U u = 1) ∧ B·𝟙 + V·v = u + v`.
3. Added the projection lemma `IsConsistent.isPreconsistent` to
   recover `IsPreconsistent` from `IsConsistent`.
4. Added `explicitEulerGLM_isConsistent` with witnesses
   `u = (fun _ => 1)`, `v = (fun _ => 0)`. The 1×1 simp shape from
   `explicitEulerGLM_isPreconsistent` carried over for the V·u and
   U·u goals; the 510c goal closed under
   `simp [explicitEulerGLM, dotProduct]` (the `Matrix.mulVec` simp
   argument was redundant — simp already unfolded the addition via
   `Pi.add_apply`).
5. Verified `lake env lean OpenMath/Chapter5/Section510.lean`
   (clean) and `lake build OpenMath.Chapter5.Section510` (clean).
6. Used `lean_verify` (lean-lsp MCP) on all three new declarations:
   axioms list is `[propext, Classical.choice, Quot.sound]` — no
   `sorryAx`, no new axioms.
7. Updated `extraction/formalization_data/lean_status.json` and
   `plan.md` (progress 55 → 56, `def:510B` row marked `[x]`).

## Result
SUCCESS. `def:510B` is formalized faithfully. Three new
declarations, all axiom-clean.

## Faithfulness check

### `GeneralLinearMethod.IsConsistent`
- Entity ID: `def:510B`. Textbook statement (from
  `def_510B.json`):
  > A general linear method `(A, U, B, V)` is 'consistent' if it is
  > preconsistent with preconsistency vector `u` and there exists a
  > vector `v` such that `B·𝟙 + V·v = u + v` (510c).
- Lean statement captures: **same content**. The existential
  binding on `u` mirrors `IsPreconsistent`'s shape, so a single `u`
  simultaneously witnesses preconsistency (via the embedded
  `V u = u ∧ U u = 1` clause) and consistency (via 510c). The
  projection lemma `IsConsistent.isPreconsistent` proves the
  textbook's "preconsistent with preconsistency vector `u`" clause
  is genuinely implied.
- Tautology check: not applicable to `def`.
- Definition smuggling check: `IsConsistent` is the literal
  textbook predicate (existence of vectors satisfying the named
  equations). It is NOT a derived characterization (e.g.
  second-order accuracy). ✓

### `GeneralLinearMethod.IsConsistent.isPreconsistent`
- Tautology check: conclusion is `M.IsPreconsistent`; only
  hypothesis is `M.IsConsistent`. The conclusion does NOT appear
  verbatim as a hypothesis. ✓
- Identity check: proof destructures the existential and
  rebuilds the preconsistency witness — not `exact h`. ✓
- Hypothesis strength check: takes only `IsConsistent`; no extra
  hypotheses. ✓

### `explicitEulerGLM_isConsistent`
- Tautology check: conclusion is the existential
  `explicitEulerGLM.IsConsistent`; no hypotheses to compare
  against. ✓
- Identity check: proof exhibits explicit witnesses and
  discharges three sub-goals via `simp` — non-trivial. ✓
- Hypothesis strength check: hypothesis-free. ✓

## Dead ends
None. The simp shape from cycles 083/084 transferred directly. The
fall-back unfolding paths from the strategy were not needed.

## Discovery
- For 1×1 GLM goals involving `B·𝟙 + V·v = u + v`, `simp` is happy
  to unfold pointwise addition (`Pi.add_apply`) without it being
  named explicitly in the simp set; the explicit `Matrix.mulVec`
  simp argument is *unused* (linter warning) once `dotProduct` is
  in the simp set. `simp [explicitEulerGLM, dotProduct]` suffices.
- The two-step approach (independent existential predicate +
  projection lemma) keeps `IsConsistent` self-contained while still
  recovering `IsPreconsistent`. This pattern should generalize to
  future "X with extra structure" definitions in §51 and §52.

## Suggested next approach
With the §510 trilogy (`IsPreconsistent`, `IsConsistent`,
`IsStable`) now complete, the planner has two reasonable next
targets:

1. **`def:520A` / `def:520C`** — the §520 stability-function
   infrastructure. These depend only on `IsPreconsistent` (already
   in place), so they are immediately accessible and should be
   smaller than `def:512A`.
2. **`def:512A` (convergent GLM)** — substantial; analogous to the
   cycle 037–038 LMM `IsConvergent` work. Would benefit from a
   dedicated multi-cycle plan covering Lipschitz IVPs, starting
   procedures, and stage-vector convergence. Defer 1–2 cycles.

I'd recommend tackling §520 first to build out a wider stability
landscape before committing to the bigger `def:512A` push.
