# Issue: Concrete LMM convergence witness deferred

## Blocker

`def:402A` (Definition 402A — convergence of a linear multistep method)
was formalized in cycle 038 as the predicate
`OpenMath.Chapter4.Section404.LinearMultistepMethod.IsConvergent`.

No concrete witness `_ : explicitEulerLMM.IsConvergent` (or
`implicitEulerLMM.IsConvergent`, or any `_ : IsConvergent` for any
preconsistent + stable LMM) was produced. The cycle delivered the
*definition* + two non-vacuity sanity helpers
(`isLMMSolution_zero_iff`, `const_sequence_isHomogeneousSolution`)
only.

## Why deferred

A genuine convergence witness for a non-trivial method is essentially
the textbook Theorem 422C ("Convergence of linear multistep methods",
Butcher §422, p. ~352). That proof requires:

1. **Discrete Grönwall on LMM iterates** — controlling the per-step
   error of an LMM under a Lipschitz RHS. This is a non-trivial chunk
   of LMM-specific stability analysis (cf. Butcher §422).

2. **Existence of a global exact solution** — Picard–Lindelöf on the
   full interval `[x₀, x]`. Our `IsConvergent` predicate quantifies
   over `yex` (it is a *hypothesis*, not a *conclusion*), so an
   abstract `def:402A` does not need this. But to *produce* a witness
   for a concrete method on a concrete IVP, we need to *use* `yex`,
   and the textbook proof of `thm:422C` uses Picard–Lindelöf to
   bound `‖f(x, yex(x))‖` uniformly on `[x₀, x]`.

   The Picard–Lindelöf existence result in
   `OpenMath/Chapter1/Section110.lean` currently has a strengthening
   gap (a uniform `‖f‖`-bound on a closed ball) recorded in
   [`picard_lindelof_bound_strengthening.md`](picard_lindelof_bound_strengthening.md).
   That gap blocks any *production* of an exact solution; for the
   `def:402A` *predicate* itself it is irrelevant (the predicate
   *receives* `yex` as a hypothesis).

3. **Starting-method partial-step error tracking** — the textbook
   convergence proof carefully accumulates the partial error from the
   `k` initial values `Y_0, …, Y_{k-1}` produced by the starting
   method. This is straightforward arithmetic but still ~20 lines of
   Lean and needs `(k+1)`-step reasoning.

Even on the simplest non-trivial case (`explicitEulerLMM`, `k = 1`),
the proof reduces to the standard Euler-method convergence theorem
(`thm:213A` / `thm:213B`), which has *not yet* been formalized in
this project as a usable consumer. (Forward Euler is treated in
§210 / §213 of Butcher, but the corresponding Lean development is
still infrastructure-light.)

## Context

- Definition site:
  `OpenMath/Chapter4/Section404.lean::LinearMultistepMethod.IsConvergent`
- Sanity helpers (already in place):
  `isLMMSolution_zero_iff`, `const_sequence_isHomogeneousSolution`.
- Dependents per `entities/def_402A.json`: `thm:243A`, `thm:405A`,
  `thm:405B`, `thm:405C`, `thm:406D`. None requires a witness yet —
  they all consume the predicate symbolically.

## What was tried

Cycle 038 deliberately scoped down per the planner's strategy. No
witness attempt was made. The planner's reasoning (paraphrased):

* The CLAUDE.md non-vacuity rule is met by the helper lemmas
  (`isLMMSolution_zero_iff` shows `IsLMMSolution` is the right shape;
  `const_sequence_isHomogeneousSolution` shows the homogeneous
  recurrence has concrete solutions).
* A full `IsConvergent` witness is at least 2–3 cycles of work and
  needs infrastructure that is not on the critical path for the
  next several entities (`thm:243A`, `def:406A`, etc.).

## Possible solutions

* **Future cycle path A (recommended):** prove `thm:422C`
  ("Convergence of LMMs") in full as the canonical witness producer,
  then derive `explicitEulerLMM.IsConvergent` and
  `implicitEulerLMM.IsConvergent` as corollaries. This needs (1)
  discrete Grönwall, (2) `picard_lindelof_bound_strengthening`, and
  (3) the §422 stability infrastructure (`thm:405C` / `thm:406C`).

* **Future cycle path B:** for explicit Euler specifically, bypass
  `thm:422C` and rebuild the `thm:213A/B` Euler-convergence proof
  directly against the LMM-iterate predicate. Cheaper but only
  produces one witness, not a general theorem.

* **Stretch goal (cycle 038 noted but skipped):** a *trivial-IVP*
  convergence statement (`f ≡ 0`, `yex ≡ y₀`) packaged as a separate
  lemma — not as `_ : IsConvergent` (since `IsConvergent` quantifies
  over *all* IVPs). This was deferred to keep the cycle focused on
  the definition and the two helpers.

## Cross-links

* [`picard_lindelof_bound_strengthening.md`](picard_lindelof_bound_strengthening.md)
  — Picard–Lindelöf strengthening; gates path A's solution-production
  step.
* `entities/thm_422C.json` — the textbook target theorem.
* `entities/thm_405C.json`, `entities/thm_406C.json`,
  `entities/thm_406D.json` — the §405/§406 theorems that consume
  `IsConvergent` symbolically (definitionally fine right now; they
  would need the witness to be informative).
