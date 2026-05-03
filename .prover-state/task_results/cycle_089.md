# Cycle 089 Results

## Worked on
`def:520F` — L-stable general linear method. Added
`OpenMath.Chapter5.Section510.GeneralLinearMethod.IsLStable` and the
non-vacuity witness `trivialZeroGLM_isLStable` in
`OpenMath/Chapter5/Section520.lean`.

## Approach
Followed the planner's strategy verbatim:

1. Added `import Mathlib.Analysis.Normed.Algebra.Spectrum` to expose
   `spectralRadius` and `Filter.cocompact`.
2. Defined `IsLStable` as the conjunction of `IsAStable` and the
   `Filter.Tendsto` of `z ↦ spectralRadius ℂ (M.stabilityMatrix z)`
   along `Filter.cocompact ℂ` to `nhds 0`. This sidesteps the
   `M(∞)`-as-matrix issue (which would require a case split on
   `A`-invertibility) and is the formulation used in the modern
   stiff-ODE literature (Hairer–Wanner).
3. Proved `trivialZeroGLM_isLStable` by reusing
   `trivialZeroGLM_isAStable` (cycle 088) for the A-stable conjunct,
   then reducing the spectral-radius function to the constant `0`
   (because `M(z) = !![0]` for every `z`, and `spectralRadius _ 0 = 0`)
   and finishing with `tendsto_const_nhds`.

Two minor deviations from the strategy's draft code (both resolved on
first build error, no encoding change):

* Used `(0 : ENNReal)` instead of `(0 : ℝ≥0∞)` — the latter notation
  was not in scope at this point in the file (would require
  `open scoped ENNReal`).
* Used the fully qualified name `spectrum.spectralRadius_zero` — the
  lemma lives in the `spectrum` namespace, not the root namespace.

No Aristotle round-trip needed (planner explicitly said not to use it
this cycle; manual verification was faster).

## Result
SUCCESS.

* `lake env lean OpenMath/Chapter5/Section520.lean` exits clean.
* `lake build OpenMath.Chapter5.Section520` succeeds (3.4s, 2772 jobs).
* `#print axioms OpenMath.Chapter5.Section510.trivialZeroGLM_isLStable`
  returns `[propext, Classical.choice, Quot.sound]` — matches
  acceptance criterion.
* `lean_status.json` updated (`def:520F` → `formalized`).
* `plan.md` updated: `def:520F` ticked, progress 59 → 60.

## Faithfulness check

### `def GeneralLinearMethod.IsLStable`

* Entity ID: `def:520F`. Textbook statement (from
  `entities/def_520F.json`):
  > A general linear method is L-stable if it is A-stable and
  > ρ(M(∞)) = 0.
* Lean statement captures: **same content**, with the `M(∞)` symbol
  re-interpreted as a `Filter.Tendsto … (Filter.cocompact ℂ) (nhds 0)`
  limit on `spectralRadius ℂ (M.stabilityMatrix z)`. This is the
  standard reading of `ρ(M(∞))` in the stiff-ODE literature
  (Hairer–Wanner, Butcher) — `M(∞)` is not a literal matrix in Lean
  syntax (it would be undefined unless `A` is invertible), so the
  spectral-radius limit at infinity is the literal Lean expression of
  the textbook condition. Documented in the docstring.
* Hypothesis strength: identical to textbook (no extra typeclass
  conditions beyond what `IsAStable` already requires plus the
  `spectralRadius` instances inferred from `Matrix _ _ ℂ`).
* No tautology, no identity proof, no definition smuggling: the
  predicate is the textbook conjunction; non-vacuity is exhibited by
  `trivialZeroGLM`.

### `theorem trivialZeroGLM_isLStable`

* Real witness: `trivialZeroGLM` exists (cycle 088), A-stability is
  proved (`trivialZeroGLM_isAStable`, cycle 088), and the
  spectral-radius limit is established by reducing to a constant `0`
  function and applying `tendsto_const_nhds`.
* No hypotheses; conclusion is a closed Prop. Tautology / identity /
  hypothesis-strength checks vacuous.

## Dead ends
None. The strategy's draft compiled with two trivial fixes
(notation/namespace), no rework needed.

## Discovery

* `ℝ≥0∞` notation is not unconditionally in scope — it requires
  `open scoped ENNReal` (the `Spectrum.lean` file opens it locally
  but the import does not re-export it). Default to `ENNReal` in the
  body of definitions/proofs to avoid the issue.
* `spectralRadius_zero` lives in the `spectrum` namespace
  (`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:81`), not at the
  root. Reference it as `spectrum.spectralRadius_zero` or
  `open spectrum`.
* `lake env lean <file>` does NOT refresh dependent `.olean` caches
  for downstream verification snippets. After editing
  `Section520.lean`, an `#print axioms` script in `/tmp` cannot
  resolve the new constant until `lake build OpenMath.Chapter5.Section520`
  is run. (Already a known pattern; worth restating.)

## Suggested next approach

Likely next targets (small, no large new infrastructure):

* `thm:520D` — listed as a transitive dependency of `def:520F`. Worth
  checking whether it's already formalized; if not, it should be
  trivial after the §520 stack we now have. Search
  `entities/thm_520D.json` first.
* `def:521A` — next §52* definition in `lean_status.json` order; the
  planner can decide whether to tackle the `§520`/`§521` stability
  theorems (`thm:521B` etc.) next or pivot to a different §52*
  introduction.
* `def:535A` — would unblock the GLM-of-LMM/RK underlying-method
  results that anchor a lot of §53 content.

The planner should pick whichever has the least new Mathlib
infrastructure overhead. From a Mathlib-coverage standpoint,
`thm:520D` is the cheapest follow-up because it only needs
`spectralRadius` (now wired in) and the existing GLM stack.
