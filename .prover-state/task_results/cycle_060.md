# Cycle 060 Results

## Worked on
* Six private `noncomputable def`s exposing the closed-form
  bound's `(a, b, c)` coefficients as functions of `h`:
  `CbaseOf`, `DbaseOf`, `yPrimeSumOf`, `aOf`, `bOf`, `cOf`.
* Private helper lemma
  `globalError_recurrence_form_explicit` — the recurrence form of
  cycle 052 with `Θ` exposed as a parameter and the existential
  `(a, b, c)` peeled off into the new `*Of` defs.
* Public theorem
  `LinearMultistepMethod.globalError_closed_form_autonomous_explicit`
  — the cycle 053 closed-form bound with `(a, b, c)` exposed via
  the `*Of` defs.

## Approach
1. Audited the formulas inside `globalError_recurrence_form`'s
   `set` block (lines 2731–2761 pre-edit) and copied them
   verbatim into top-level `noncomputable def`s in the same
   namespace, immediately above
   `globalError_closed_form_autonomous`.
2. Added a `private` helper
   `globalError_recurrence_form_explicit` whose conclusion uses
   the new `*Of` defs and which takes `Θ` plus the `θ`-bound as
   explicit parameters. Its body opens with
   `unfold aOf bOf cOf yPrimeSumOf CbaseOf DbaseOf` so the goal
   matches the formulas verbatim, then replays the existing
   `globalError_recurrence_form` body essentially unchanged
   (skipping the `obtain ⟨Θ, hΘ_nn, hΘ⟩ := …` line, since `Θ`
   is now a parameter, and dropping the existential's `a, b, c`
   from the closing `refine`).
3. Added `globalError_closed_form_autonomous_explicit` immediately
   after `globalError_closed_form_autonomous`. It calls
   `theta_bounded_of_isStable` to extract `Θ`, then
   `globalError_recurrence_form_explicit` to get the recurrence
   in `*Of` form, and finally `discrete_gronwall_exp_bound` to
   produce the exponential closed form.

## Result
SUCCESS — `lake env lean OpenMath/Chapter4/Section404.lean`
exits 0 with the expected three pre-existing unused-variable
warnings (`hM`, `hh`, `hMmax0`) plus the line-3751
declaration-uses-`sorry` warning (the same single sorry from
cycle 058+, shifted by ~+544 lines because the new
`globalError_recurrence_form_explicit` proof body is a near-
verbatim ~430-line replay of `globalError_recurrence_form`).

The full-replay path was chosen over the cite-then-congr
shortcut described in the strategy: the existential witnesses
returned by `globalError_recurrence_form` and
`globalError_closed_form_autonomous` are opaque after
destructuring (no syntactic match with `aOf, bOf, cOf` is
provable from the type signature), so a direct cite cannot
close the bound subgoal. The strategy's "fall back to full
replay" path was therefore used. The replay differs from the
original body only at three points:
* `unfold aOf bOf cOf yPrimeSumOf CbaseOf DbaseOf` is added at
  the top so the goal is presented in formula form (and the
  later `set Cbase := …`, `set y'sum := …`, etc. fold cleanly).
* The `obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable …`
  line is removed because `Θ`, `hΘ_nn`, `hΘ` are now in scope
  as helper parameters.
* The final `refine ⟨a, b, c, ha_nn, hb_pos, hc_nn, ?_, hu0⟩`
  becomes `refine ⟨ha_nn, hb_pos, hc_nn, ?_, hu0⟩` (no
  existential to populate).

## Faithfulness check
For each new `def` or `theorem` introduced this cycle:

* `CbaseOf`, `DbaseOf`, `yPrimeSumOf`, `aOf`, `bOf`, `cOf` —
  not Butcher concepts. They are abbreviations for the local
  `set`-bound formulas inside cycle 052's
  `globalError_recurrence_form` proof; this cycle only exposes
  them at top level so cycle 061 can speak about their `h → 0`
  limits. Each `def` carries a one-line comment documenting
  this provenance.

* `globalError_recurrence_form_explicit` — internal helper. Its
  conclusion is the cycle-052 conclusion with the existential
  `∃ a b c` peeled off into `aOf, bOf, cOf` and `Θ`-related
  arguments lifted from `hstab` to explicit parameters. No new
  mathematical content; no Butcher entity ID applies.

* `LinearMultistepMethod.globalError_closed_form_autonomous_explicit`
  — entity ID `thm:406D` (autonomous, explicit-`(a,b,c)` form).
  Textbook statement (`extraction/formalization_data/entities/thm_406D.json`):
  > "A stable consistent linear multistep method is convergent."

  Lean statement captures: **same content as the cycle-053
  existential `globalError_closed_form_autonomous` (which is
  the closed-form bound underlying thm:406D's autonomous
  case), but with the existential `a, b, c` peeled off via the
  new `*Of` defs.** Hypothesis list is identical to the cycle-053
  version (no strengthening). The `Θ` is still existential
  because its value depends on `M, hstab` via
  `theta_bounded_of_isStable`; cycle 061 will lift it to a
  named function once needed for the outer squeeze.

* Tautology check — none of the conjuncts in
  `_explicit`'s conclusion appears verbatim as a hypothesis;
  same for `_recurrence_form_explicit`. Both pass.
* Identity check — neither proof is a single `exact h`;
  `_recurrence_form_explicit` is a ~430-line replay,
  `_explicit` is a ~10-line composition with
  `discrete_gronwall_exp_bound`.
* Hypothesis strength check — `_explicit` mirrors the cycle-053
  hypothesis list exactly. `_recurrence_form_explicit` drops
  `hstab` (replaced by the explicit `Θ`-and-bound parameters).
* Absent theorem check — N/A.

## Dead ends
Initially considered the strategy's "cite then congr" path
(call `globalError_closed_form_autonomous`, destructure its
existential, prove the bound for `aOf, bOf, cOf` by linarith /
congr after observing the algebraic shapes match). This is not
provable: the existential witnesses returned by `globalError_
closed_form_autonomous` are opaque after the `obtain`, so
there is no syntactic or type-level handle on
`a = aOf M Θ L h yex Y x₀` etc. The strategy's caveat about
this path being "finicky" was correct; full replay is the
clean path.

Also briefly considered modifying `globalError_recurrence_form`
in place to use the `*Of` defs in its `set` lines. The strategy
explicitly forbids touching it, and a parallel
`_recurrence_form_explicit` lemma is a non-breaking change that
keeps the existential infrastructure intact for any downstream
consumer that might depend on it. Stuck with the strategy.

## Discovery
The `unfold ... at the top` + `set ... with ..._def` pattern is
clean for refactoring an existing `set`-heavy proof body into a
new lemma whose conclusion uses named abbreviations: the
`unfold` exposes the formula, the `set` then folds it back to a
local name, and the rest of the body works verbatim. This
pattern lets cycle 060's ~430-line replay be byte-for-byte
identical with cycle 052's body modulo the three documented
edits.

## Suggested next approach
Cycle 061 (per the cycle 060 strategy's roadmap):
* Prove `bOf_tendsto`: `Tendsto (fun h => bOf M Θ L h)`
  `(nhds 0) (nhds ((Θ + 1) * Cbase∞ + 1))`. The cycle 056 helper
  `b_tendsto_at_zero` already proves the same statement modulo
  `unfold bOf CbaseOf`; this should be a one-liner.
* Prove `cOf_tendsto`: similar from `c_tendsto_at_zero`
  (cycle 056).
* Prove `yPrimeSumOf_tendsto_zero` — the new piece. Requires
  threading the starting-method convergence assumption
  (`Tendsto (fun h => start h i) (nhds 0) (nhds y₀)` for each
  `i : Fin k`). The current `yPrimeSumOf` takes `Y` as an
  arbitrary `ℕ → ℝ`, so cycle 061 will likely need to specialise
  to `Y = fun n => some chosen sequence agreeing with `start` on
  `i < k`` to get the limit, OR hoist the starting-data
  hypothesis up into a per-`h` parameter. The cycle 060 strategy
  flagged this design problem; cycle 061's planner should pick
  one approach (probably the second, since `IsConvergent`
  threads `start` as a per-`h` function).
* Once those three Tendsto lemmas land, cycle 062 assembles the
  outer squeeze using cycle 059's
  `globalError_outer_squeeze_a_term` /
  `globalError_outer_squeeze_c_term` plus `aOf_tendsto_zero` /
  `cOf_tendsto`.
