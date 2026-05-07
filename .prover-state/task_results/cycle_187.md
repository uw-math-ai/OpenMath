# Cycle 187 Results

## Worked on

* Priority 0 — GPFS health probe.
* Priority 2 — Section381 follow-up:
  * Deliverable A — shipped `PhiEquivalent.of_pReducesTo`
    (`RKTableau.PReducesTo M M' → PhiEquivalent M M'`) + per-step
    preservation lemma `pReduced_phiEquivalent`
    (`M.IsPReducibleVia P → PhiEquivalent M (M.pReduced P)`) + two
    private mutual helpers
    `derivativeWeight_pReduced` / `derivativeWeightProd_pReduced`.
  * Deliverable B — refactored the inline
    `paddedEuler.PEquivalent paddedEuler` example to consume the
    cycle 186 named theorem `paddedEuler_pEquivalent_pReduced`.

## Approach

### Priority 0 — GPFS health probe (5 min)

* Pre-flight `ps -u $USER -o pid,stat,wchan,etime,comm | grep "^[ ]*[0-9]+ +D"`
  returned no D-state processes (cycle 183's zombie-find pattern is
  not present today).
* `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
  exited 124 with near-zero CPU after exactly 300s — **7th
  consecutive timeout**. Logged the seventh timeout in
  `.prover-state/issues/cycle_182_gpfs_slowness.md`. Pivoted to
  Priority 2.

### Priority 2 Deliverable A — `PhiEquivalent.of_pReducesTo`

The implication `PReducesTo M M' → PhiEquivalent M M'` is implicit in
Butcher's §380 narrative ("P-reducible methods agree on elementary
weights") but is not stated as a numbered result. Proof structure:

* **Two private mutual helpers**
  `derivativeWeight_pReduced` (over `RootedTree`) and
  `derivativeWeightProd_pReduced` (over `List RootedTree`), proving:

  ```
  M.derivativeWeight i t = (M.pReduced P).derivativeWeight (P.block i) t
  ```

  for every rooted tree `t` and every stage `i : Fin s`. Mirrors
  exactly the mutual recursion pattern of `derivativeWeight` /
  `derivativeWeightProd` defined in `OpenMath/Chapter3/Section312.lean`
  (Lean accepts the structural mutual termination via the same
  `RootedTree.mk children` / `t :: ts` descent).

* **Per-step elementary-weight preservation** `pReduced_phiEquivalent`
  combines the helpers with `Finset.sum_fiberwise` (mathlib's
  fiberwise sum decomposition) to regroup
  `Σ_{i : Fin s} M.b i * M.derivativeWeight i t` into the reduced sum
  `Σ_{I : Fin sBar} (M.pReduced P).b I * (M.pReduced P).derivativeWeight I t`,
  using `pReduced_A_apply` / `pReduced_b_apply` for the regrouped
  matrix and weight coefficients.

* **Main theorem** `PhiEquivalent.of_pReducesTo` is a 4-line
  induction on the `RKTableau.PReducesTo` reflexive-transitive
  closure: `refl` ⇒ `PhiEquivalent.refl`; `step` ⇒
  `PhiEquivalent.trans (pReduced_phiEquivalent _ hVia) IH`.

### Priority 2 Deliverable B — inline-example refactor

Replaced a 13-LOC `have hReduced ...; have hEquiv ... ; exact ...`
chain with a 6-LOC `exact paddedEuler_pEquivalent_pReduced.…`
invocation reusing cycle 186's named theorem. Net: **−9 LOC**.

## Result

**SUCCESS** — both deliverables shipped, all new public theorems
axiom-clean, file compiles in ~19s cold / ~7s warm.

* Public theorems added in `OpenMath/Chapter3/Section381.lean`:
  * `OpenMath.Chapter3.Section381.pReduced_phiEquivalent`
  * `OpenMath.Chapter3.Section381.PhiEquivalent.of_pReducesTo`
* Private helpers: `derivativeWeight_pReduced`,
  `derivativeWeightProd_pReduced` (mutual block).
* Axiom check (`lean_verify`): both public theorems return
  `[propext, Classical.choice, Quot.sound]` only — no axioms beyond
  Lean's defaults.
* Sorry count: still 0 across the project.

## Faithfulness check

For each new `theorem` introduced this cycle:

* **`pReduced_phiEquivalent`** —
  * Reference: Butcher §380 page 302 narrative on P-reducibility — the
    motivation for the reduced method is that it computes the same
    elementary weights as the original. Not a numbered result; this
    is a helper formalising the implicit step.
  * Lean type captures: same content (Φ-equivalence between `M` and
    `M.pReduced P` under `IsPReducibleVia`).
  * Hypothesis strength: `M.IsPReducibleVia P` (row-sum constancy
    on each block) is exactly the textbook hypothesis required to
    define `pReduced` and is the minimal hypothesis for the
    elementary-weight identity. Cannot be weakened.

* **`PhiEquivalent.of_pReducesTo`** —
  * Reference: Butcher §380 pages 302–303 narrative ("the method can
    be replaced by a method with fewer stages…"). Implicit in def:381B
    + def:381D + def:381F discussion; not a numbered theorem.
  * Lean type captures: same content (any `PReducesTo` chain
    preserves elementary weights).
  * Hypothesis strength: `RKTableau.PReducesTo M M'` (reflexive-
    transitive closure of P-reduction) is the minimal hypothesis for
    Φ-equivalence on the P-side. The 0-reduction analogue would
    require extending `PReducesTo` with a 0-step constructor; that
    extension is the natural follow-up once `def:381E`'s full
    reduced-method construction lands.

* **`derivativeWeight_pReduced`** / **`derivativeWeightProd_pReduced`**
  (private helpers) — internal lemmas for `pReduced_phiEquivalent`,
  no textbook ID.

* **Tautology / identity / definition-smuggling / hypothesis-strength
  checks**:
  * Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`)
    returned only the pre-existing `Section514.lean:601 exact h_norm_obligation`
    entry (cosmetic-rename false positive listed in
    `tautology_scanner_false_positives.md`); no new tautologies
    introduced this cycle.
  * No proof reduces to `exact h` / `:= id` / `:= h_<name>`.
  * No new `def`s or `structure`s introduced — only theorems,
    operating on already-shipped definitions; no smuggling possible.
  * Hypotheses match textbook intent verbatim (see per-theorem
    notes above).

## Dead ends

None — Deliverable A landed on the first compile attempt after one
syntactic-fix iteration:

* First compile surfaced two issues: (1) docstring attached to a
  `mutual` block keyword (Lean rejects with "unexpected token
  'mutual'; expected 'lemma'"); (2) `conv_lhs => ext j` failed on
  goals of the form `∑ j, …` (since `Finset.sum` is not a function
  arrow — `conv ext` only descends through `λ`-binders).
* Fix: moved docstrings inside the `mutual` block onto each
  individual private theorem, and replaced the two `conv_lhs => ext`
  patterns with explicit `Finset.sum_congr rfl (fun j _ => …)`
  + named `have hSumRewrite` rewrites. Compiled cleanly.

## Discovery

* **`Finset.sum_fiberwise`** (Mathlib
  `Algebra/BigOperators/Group/Finset/Basic.lean`) is the canonical
  fiberwise-sum decomposition for mathlib in this project's version.
  Signature:

  ```
  Finset.sum_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → M)
      [Fintype κ] [DecidableEq κ] :
      ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i
  ```

  Applied to `s := Finset.univ`, `g := P.block` re-groups
  `∑ j : Fin s, …` into `∑ J : Fin sBar, ∑ j ∈ filter (P.block · = J), …`.
  Useful any time a sum over `Fin s` needs to factor through a
  partition `block : Fin s → Fin sBar` — likely needed again for
  Deliverable A's 0-reduction analogue and for `def:381E`'s reduced-
  method construction.

* **Mutual `theorem` blocks** in the structural-recursion style
  mirror the corresponding mutual `def` (here: `derivativeWeight` /
  `derivativeWeightProd` from Section312); Lean accepts the
  termination via the same `RootedTree.mk children` / `t :: ts`
  descent. Docstrings must attach to the individual theorems, not
  the `mutual` keyword.

* **`conv_lhs => ext j`** does NOT descend through
  `Finset.sum`'s λ-binder. Use `Finset.sum_congr rfl (fun j _ => …)`
  + an explicit `have hSumRewrite` instead — same effect, accepted
  by the elaborator.

## Suggested next approach

Decision tree for cycle 188:

* **If Priority 0 Section441 GPFS smoke test passes (<5 min, EXIT=0)**:
  ship Phase C.2 per `lem_441A_phase_C_scoping.md` — copy
  `.prover-state/cycle_182_draft_section441.lean` over HEAD,
  apply the cycle 184 line-1529 namespace fix
  (`M.αPoly_complex_root_norm_ge_one_of_stable` →
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`),
  compile, and `lean_verify` the three new public theorems.

* **If Priority 0 still times out (8th time)**:
  several productive Section381 / §380 follow-ups:
  1. **0-reduction analogue**: extend `RKTableau.PReducesTo` with a
     `zero` constructor (`M.IsZeroReducibleVia inP1 → PReducesTo
     (M.zeroReduced inP1) M'' → PReducesTo M M''`), then add a
     `zeroReduced_phiEquivalent` lemma + extend `of_pReducesTo`'s
     induction to the new constructor. The `zeroReduced` definition
     is already in place (`OpenMath/Chapter3/Section381.lean:234`),
     so the work is purely the Φ-preservation argument: deleting
     `P₀` stages does not change `Σ_i b_i Φᵢ(t)` because every
     deleted stage has `b i = 0`. Estimated 30–50 LOC.
  2. **`def:381E` reduced-method construction**: see
     `.prover-state/issues/reduced_method_deferred.md`. The fixed-
     point construction ("P-reduce then 0-reduce, iterated until
     irreducible") is the high-priority infrastructure piece for
     `def:381F`'s textbook formulation; multi-cycle.
  3. **`thm:381G` (irreducible methods are stage-distinguishable)**
     or **`thm:381H` (Φ-equivalence iff equivalent reduced
     methods)** — both are §380 numbered theorems consuming the
     `PhiEquivalent` / `PReducesTo` infrastructure; read their JSONs
     before scoping.

* **If both Priority 0 and a Priority 2 deliverable stall**: planner
  re-scoping cycle warranted (8th GPFS timeout makes this a
  multi-week pattern; the loop-maintainer escalation in
  `cycle_182_gpfs_slowness.md` may need a different remediation).
