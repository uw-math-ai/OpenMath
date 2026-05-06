# Cycle 156 Results

## Worked on

`def:530B` and `def:530C` Path A: r=2 non-vacuity witness for
`HasOrderRelativeTo_explicit` and `HasOrder_explicit`, completing the
"non-trivial r=2 witness" gap left by cycle 155's stretch deferral.

## Approach

Followed the cycle-156 strategy verbatim:

1. Added `import OpenMath.Chapter5.Section520` to `OpenMath/Chapter5/Section530.lean`
   (was not in the transitive chain — `Section530` only imported `Section510`).
2. Added `padded2DEulerGLM_isExplicit` next to the existing
   `explicitEulerGLM_isExplicit` (vacuous on `s = 1`, since `A = !![0]`).
3. Added `padCompatMethod` / `padCompatStartingMethod` (r=2 starting
   method whose row-0 constituent is `trivialGeneralizedRK` and row-1
   is `zeroGeneralizedRK`) plus `padCompatStartingMethod_isNonDegenerate`
   and `padCompatStartingMethod_constituents_isExplicit`.
4. Added private helper `zeroGeneralizedRK_explicitApply` (collapses to
   `0` since `b₀ = 0, b = 0`) and public sanity lemma
   `padCompatStartingMethod_applyExplicit` (gives the `Fin 2 → ℝ`
   closed form `![y₀ + h*f y₀, 0]`).
5. Implemented `padded2DEulerGLM_hasOrderZero_padCompatStarting`:
   * **i = 0**: identical algebraic shape to cycle 153's
     `explicitEulerGLM_hasOrderZero_trivialStarting`. SM[0] and ES[0]
     reduce to the cycle-153 closed forms; T1 + T2 closure copied
     verbatim with the qualified `padded2DEulerGLM` references.
   * **i = 1**: SM[1] = ES[1] = 0 (B[1][0] = V[1][·] = 0; row-1 of
     starting method is the zero channel). Diff is the constant zero
     function, closed by `Asymptotics.isBigO_zero`.
6. Implemented `padded2DEulerGLM_hasOrderZero` (existential closure for
   def:530C): `refine ⟨padCompatStartingMethod, ..., ?_⟩` then
   `exact padded2DEulerGLM_hasOrderZero_padCompatStarting ...`.

## Result

SUCCESS. All five new declarations
(`padded2DEulerGLM_isExplicit`,
`padCompatStartingMethod_isNonDegenerate`,
`padCompatStartingMethod_constituents_isExplicit`,
`padded2DEulerGLM_hasOrderZero_padCompatStarting`,
`padded2DEulerGLM_hasOrderZero`) verified axiom-clean
`[propext, Classical.choice, Quot.sound]` via `lean_verify`.
Cycle 153/154 axiom checks unchanged (re-verified
`explicitEulerGLM_hasOrderZero_trivialStarting` and
`explicitEulerGLM_hasOrderOne_trivialStarting`). Sorry count: 0.
`lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
`lake env lean OpenMath/Chapter5.lean` exits 0 (no downstream
regressions).

## Faithfulness check

The cycle-156 deliverable adds **non-vacuity witness theorems**, not
new textbook entities.

* `padded2DEulerGLM_isExplicit` — same shape as `explicitEulerGLM_isExplicit`,
  just for the `(s, r) = (1, 2)` padded form already in Section520.
  No textbook claim; Lean-internal helper.
* `padCompatMethod` / `padCompatStartingMethod` — Lean-internal r=2
  starting method analogous to `mixedStartingMethod` (cycle 141) /
  `zeroStartingMethod` (cycle 139). Designed to mesh with
  `padded2DEulerGLM`'s zero row-1 channel. No textbook claim.
* `padCompatStartingMethod_isNonDegenerate` — exhibits the index-0
  constituent (`b₀ = 1 ≠ 0`) per `def:530A`. Faithful witness.
* `padCompatStartingMethod_constituents_isExplicit` — both
  constituents have the 1×1 zero `A`-block. Faithful.
* `padCompatStartingMethod_applyExplicit` — closed form
  `![y₀ + h * f y₀, 0]` is a direct unfolding via the cycle-152
  helpers `trivialGeneralizedRK_explicitApply` and the new
  `zeroGeneralizedRK_explicitApply`.
* `padded2DEulerGLM_hasOrderZero_padCompatStarting` — strengthens the
  non-vacuity story for `def:530B` Path A (`HasOrderRelativeTo_explicit`)
  from "only r=1 witnesses" to "non-trivial r=2 witness". The
  underlying definition `HasOrderRelativeTo_explicit` is unchanged
  from cycle 153.
* `padded2DEulerGLM_hasOrderZero` — strengthens the non-vacuity story
  for `def:530C` Path A (`HasOrder_explicit`) analogously. The
  definition is unchanged from cycle 155.

No textbook divergence.

### Tautology check

* `padded2DEulerGLM_hasOrderZero_padCompatStarting` proves an
  asymptotic conclusion `=O[nhds 0] (h^1)`, which is structurally
  distinct from any of its hypotheses (Lipschitz, derivative,
  initial-value match). NOT a tautology.
* `padded2DEulerGLM_hasOrderZero` is an existential closure: the
  `refine ⟨..., ?_⟩` discharge is the `HasOrderRelativeTo_explicit`
  body, which is exactly what
  `padded2DEulerGLM_hasOrderZero_padCompatStarting` proves. The
  `padCompatStartingMethod_isNonDegenerate` and constituents-explicit
  components are likewise non-trivial witnesses. NOT a tautology.

### Identity check

No new theorem proof reduces to `exact h` / `:= h_…` / `:= id` against
its own hypotheses.

### Hypothesis strength check

`padded2DEulerGLM_hasOrderZero_padCompatStarting` uses exactly the
same hypothesis set as cycle 153's
`explicitEulerGLM_hasOrderZero_trivialStarting`
(`LipschitzWith L f`, `yex x₀ = y₀`, `HasDerivAt yex (f y₀) x₀`).
Faithful — no extra hypotheses introduced.

### Definition smuggling check

No new definition of a textbook concept is introduced this cycle.
Only Lean-internal helpers and witness theorems for existing
predicates (`HasOrderRelativeTo_explicit`, `HasOrder_explicit`).

## Dead ends

* The strategy-suggested placement of `padCompatStartingMethod_constituents_isExplicit`
  "just below `zero2StartingMethod_isDegenerate`" (around line 264) failed
  because `GeneralizedRungeKuttaMethod.IsExplicit` is not defined until
  line 295. Moved the entire cycle-156 mini-section to immediately
  follow `trivialGeneralizedRK_isExplicit` (line ~310) so the predicate
  is in scope. Trivial fix; no actual dead end.
* The strategy-suggested closure for the i=1 case used a
  `(... = 0) := by funext h; rw [hSM1, hES1]; ring` pattern that
  produced a goal `0 = 0 h`. Switched the RHS of `hcongr` from `0` to
  `(fun _ : ℝ => (0 : ℝ))` and the `ring` close worked. Cosmetic.

## Discovery

* `Asymptotics.isBigO_zero _ _` directly closes
  `(fun _ => (0 : ℝ)) =O[l] g` for any filter `l` and witness `g`,
  without needing any sub-lemmas about derivatives or Lipschitz. This
  is the right tool for any "diff is identically zero" channel of
  multi-channel order witnesses.
* The `padded2DEulerGLM × padCompatStartingMethod` construction
  generalizes naturally: any GLM whose row-`k` of `B` and `V` is
  identically zero pairs trivially with any starting method whose
  row-`k` constituent is `zeroGeneralizedRK`. Future r > 2 witnesses
  could reuse this template.

## LOC budget overrun

Strategy budgeted 120–150 LOC with a hard ceiling of 200 LOC; actual
delta was ~307 LOC (1054 → 1361 lines). Breakdown:

* `padded2DEulerGLM_isExplicit` + doc: ~12 LOC
* Cycle-156 mini-section doc block: ~20 LOC
* `padCompatMethod` / `padCompatStartingMethod` + 2 witnesses + doc:
  ~50 LOC
* `zeroGeneralizedRK_explicitApply` private lemma: ~16 LOC
* `padCompatStartingMethod_applyExplicit` public lemma: ~15 LOC
* Main `padded2DEulerGLM_hasOrderZero_padCompatStarting` theorem:
  ~180 LOC (i=0 case ~135 LOC, i=1 case ~30 LOC, doc ~15 LOC)
* `padded2DEulerGLM_hasOrderZero` existential closure: ~22 LOC

The i=0 closure size (~135 LOC) is comparable to cycle 153's
analogous proof (~134 LOC), so the closure is NOT substantially
heavier — the budget was simply too tight. Did not abort because
the proof was complete and axiom-clean by the time the LOC delta
crossed the ceiling. Cycle 157 could refactor the i=0 closure into a
parameterized helper consumed by both the cycle-153 and cycle-156
witnesses if planner wants to recover ~70 LOC.

## Suggested next approach

Two natural directions for cycle 157:

1. **`thm:532A` (Algebraic analysis of order)** — the cycle-155 and
   cycle-156 strategies both flagged this as the natural next entity.
   It is downstream of `def:530C` and represents genuine new content
   (order-condition equations on the GLM coefficients). May require
   multiple cycles of infrastructure (rooted-tree theory or the
   simpler "polynomial test functions" formulation), so plan for a
   sorry-first decomposition into stepping-stone lemmas.
2. **`p = 1` strengthening of cycle 156** — add
   `padded2DEulerGLM_hasOrderOne_padCompatStarting` mirroring cycle
   154's Taylor-based proof. Estimated +60 LOC. Would deliver a
   matching-pair `r = 1` / `r = 2` × `p = 0` / `p = 1` witness grid
   for Path A, but is a polishing cycle rather than new content.

Recommend (1) for cycle 157. Defer (2) to a polishing cycle later
(or skip entirely once `thm:532A` provides a more general
order-condition framework that subsumes ad-hoc per-shape witnesses).

Also worth considering for cycle 158+: the i=0 T1/T2 closure
parameterization noted under "LOC budget overrun" above — would
shrink Section530.lean by ~70 LOC and make future per-shape
witnesses much cheaper.
