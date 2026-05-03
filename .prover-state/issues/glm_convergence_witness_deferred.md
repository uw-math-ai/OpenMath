# Issue: Concrete GLM convergence witness deferred

## Cycle 092 update

Cycle 092 repaired the φ quantifier in `def:512A` from existential
to universal (`∃ φ` → `∀ φ`), aligning with the LMM analog at
`OpenMath/Chapter4/Section404.lean:333–354` and enabling the
cycle-093 §B work to construct φ explicitly per Butcher's §513
proof. The deferral itself remains in force: a concrete
`_ : explicitEulerGLM.IsConvergent` still requires `thm:515D` (or
the path-B trivial-IVP slice). The repair only changed the shape
of the universal quantification, not the deferred witness.

## Blocker

`def:512A` (Definition 512A — convergence of a general linear method)
was formalized in cycle 091 as the predicate
`OpenMath.Chapter5.Section510.GeneralLinearMethod.IsConvergent`.

No concrete witness `_ : explicitEulerGLM.IsConvergent` (or for any
other specific GLM) was produced in this cycle. The deliverable was
the definition + the iteration recurrence `IsGLMSolution` + three
non-vacuity sanity helpers (`isGLMSolution_zero_iff`,
`zero_isGLMSolution_zero`, `zero_seq_homogeneous_V`) only.

This mirrors the deferral recorded in
[`lmm_convergence_witness_deferred.md`](lmm_convergence_witness_deferred.md)
for the LMM analogue (`def:402A`, cycle 038).

## Why deferred

A genuine convergence witness for any specific GLM is essentially the
content of Butcher Theorem `thm:515D` ("Stability and consistency
imply convergence", §515, p. ~414). That theorem is one of the
*dependents* of `def:512A` — it cannot even be stated without the
predicate that this cycle introduces. So `thm:515D` (and its helper
`lem:515B`) are the canonical witness producers, and they are
downstream work, not cycle 091.

The two §513/§514 necessity theorems (`thm:513A`, `thm:514A`) consume
`IsConvergent` symbolically (they assume `M.IsConvergent` and derive
`M.IsStable` / `M.IsConsistent`); they do not produce a witness.

## Trivial-IVP slice (NOT a witness for `IsConvergent`)

For the trivial IVP `f ≡ 0`, `y₀ = 0`, `yex ≡ 0`:

* The constantly-zero sequence `Y n m i = 0` solves the GLM iteration
  recurrence (`zero_isGLMSolution_zero` in `Section512.lean`).
* The choice `u = (fun _ => 1)`, `φ = (fun _ _ => 0)` would satisfy
  `lim_{h→0} φ_i(h) = u_i · 0 = 0` and `Y n n → 0 = u_i · yex(x)`.

This is a valid *trivial-IVP slice* lemma, but it is **not** a witness
for `M.IsConvergent` because the `IsConvergent` predicate quantifies
over *all* IVPs (i.e. all `f`, `L`, `x₀`, `y₀`, `yex` satisfying the
hypotheses), not just the trivial one. Producing a witness requires
proving the convergence statement for arbitrary Lipschitz-RHS IVPs,
which is the full content of `thm:515D`.

A future cycle may package the trivial-IVP slice as a separate lemma
(`isConvergent_trivial_IVP`, restricted predicate); this is cheap but
of limited use.

## Context

* Definition site:
  `OpenMath/Chapter5/Section512.lean::GeneralLinearMethod.IsConvergent`
  (in namespace `OpenMath.Chapter5.Section510`).
* Iteration recurrence:
  `OpenMath/Chapter5/Section512.lean::GeneralLinearMethod.IsGLMSolution`.
* Sanity helpers (already in place):
  `isGLMSolution_zero_iff`, `zero_isGLMSolution_zero`,
  `zero_seq_homogeneous_V`.
* Dependents per `entities/def_512A.json`: `thm:513A`, `thm:514A`,
  `lem:515B`, `thm:515D`, `def:542A`. None requires a witness yet —
  they all consume the predicate symbolically.

## What was tried

Cycle 091 deliberately scoped down per the planner's strategy. No
witness attempt was made. The planner's reasoning:

* The CLAUDE.md non-vacuity rule is met by the helper lemmas
  (`isGLMSolution_zero_iff` shows `IsGLMSolution` is the right shape;
  `zero_isGLMSolution_zero` and `zero_seq_homogeneous_V` give a
  concrete inhabitant of the recurrence side).
* A full `IsConvergent` witness *for any specific GLM* requires
  `thm:515D`, which itself requires this cycle's `def:512A`. Putting
  the witness in cycle 091 would create a circular work item.

## Possible solutions

* **Future cycle path A (canonical):** prove `lem:515B` and `thm:515D`
  ("stability + consistency ⇒ convergence") in full, then derive
  `explicitEulerGLM.IsConvergent` (and any other preconsistent /
  stable / consistent GLM) as corollaries. This is the intended
  textbook path.
* **Future cycle path B:** for `explicitEulerGLM` specifically, fold
  the GLM step into a one-step LMM and reuse the LMM convergence
  witness once `lmm_convergence_witness_deferred` is resolved. Cheaper
  but produces only one witness.
* **Stretch goal:** a *trivial-IVP slice* lemma (per the trivial-IVP
  section above) — not as `_ : IsConvergent` (since the predicate
  quantifies over *all* IVPs), but as a restricted convergence
  statement. Useful for sanity but not informative about real GLMs.

## Cross-links

* [`lmm_convergence_witness_deferred.md`](lmm_convergence_witness_deferred.md)
  — the LMM analogue; same structural deferral.
* [`is_convergent_strengthened.md`](is_convergent_strengthened.md) —
  record of the LMM-side strengthenings (joint Lipschitz, ContDiff ℝ 1,
  M_bound). The GLM `IsConvergent` deliberately does **not** apply
  these preemptively; if a §513/§514/§515 proof needs them, file a
  parallel issue at that point.
* `entities/thm_515D.json` — the textbook target theorem.
* `entities/lem_515B.json`, `entities/thm_513A.json`,
  `entities/thm_514A.json` — the §513/§514/§515 theorems that consume
  `IsConvergent` symbolically (definitionally fine right now; they
  would need the witness to be informative).
