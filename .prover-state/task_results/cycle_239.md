# Cycle 239 Results

## Worked on

§383 elementary-weight algebra Φ-quotient infrastructure:
`elementaryWeightQ_phi` and corollaries (Priority 1 of cycle 239 strategy).
Plus the cycle 239 GPFS smoke test (Priority 0) — 43rd consecutive
timeout, pivoted to Priority 1 per strategy.

## Approach

Priority 0: ran `time timeout 60 lake env lean
OpenMath/Chapter4/Section441.lean`. EXIT=124, real 1m0.028s, user
0m0.232s, sys 0m0.460s — CPU 1.15% of wall, identical near-zero
GPFS-disk-wait pattern continues. Logged 43rd timeout in
`.prover-state/issues/cycle_182_gpfs_slowness.md` and pivoted.

Priority 1: shipped six new public symbols in
`OpenMath/Chapter3/Section381.lean` inside `namespace
OpenMath.Chapter3.Section312.RKTableau`, placed immediately before
`end OpenMath.Chapter3.Section312.RKTableau` at line 4681 inside a
`section` / `open OpenMath.Chapter3.Section310` block (needed for
`RootedTree` resolution at the namespace's tail-end, mirroring the
inner-section pattern used by every other `RootedTree`-touching
theorem in the file):

1. **`noncomputable def elementaryWeightQ_phi (q : Quotient
   PhiEquivalent.setoidSigma) (t : RootedTree) : ℝ`** — lifts
   `M.elementaryWeight t` to the §383 group's underlying set via
   `Quotient.lift`. Respect proof: `rintro ⟨s, M⟩ ⟨s', M'⟩ hPhi; show
   M.elementaryWeight t = M'.elementaryWeight t; exact hPhi t`. Works
   because `PhiEquivalent` is *defined* as pointwise equality of
   elementary weights.

2. **`@[simp] elementaryWeightQ_phi_mk`** — definitional unfold on
   `Quotient.mk` classes, proved by `rfl`.

3. **`elementaryWeightQ_phi_composeQ_phi_mk`** — per-representative
   quotient-level lift of cycle 225's `compose_elementaryWeight_decomp`.
   Stated on representatives `M₁, M₂` because the bottom-block sum
   `∑ i : Fin s₂, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t` depends on
   the representative stage count `s₂` and does not descend to the
   abstract Φ-quotient. Proof: `show (M₁.compose M₂).elementaryWeight t
   = M₁.elementaryWeight t + ...; exact compose_elementaryWeight_decomp
   M₁ M₂ t`.

4. **`@[simp] elementaryWeightQ_phi_id`** — zero on identity class
   `⟦⟨0, RKTableau.id⟩⟧`, via cycle 228's `id_elementaryWeight`.

5. **`elementaryWeightQ_phi_eq_of_phiEquivalent`** — soundness bridge
   `PhiEquivalent M M'` ⟹ class-level equality of `elementaryWeightQ_phi`
   images. Proof: `show M.elementaryWeight t = M'.elementaryWeight t;
   exact hPhi t`.

6. **`elementaryWeightQ_phi_eq_of_eq`** — `congrArg`-style class-equality
   propagation `q = q' → elementaryWeightQ_phi q t = elementaryWeightQ_phi
   q' t`. Proof: `rw [hq]`. Used in the cycle 239 end-to-end non-vacuity
   example that bridges `composeQ_phi_id_left` to `elementaryWeightQ_phi`.

Five paddedEuler non-vacuity `example`s in `namespace
OpenMath.Chapter3.Section381` cover all five new theorems (1–5; def
covered by example 1's rfl).

## Result

SUCCESS — Priority 1 deliverable shipped in full. P1.A + P1.B + P1.C + P1.D
all complete. Priority 2 (cycle 238's `cInverseLog_two_eq` /
`cInverseLog_three_eq` closed forms in Section441B) skipped per strategy
("Skip Priority 2 entirely if Priority 1 takes the full cycle budget").

All six new public symbols are axiom-clean:
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi` →
  `[propext, Classical.choice, Quot.sound]`
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi_mk` →
  `[propext, Classical.choice, Quot.sound]`
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi_composeQ_phi_mk` →
  `[propext, Classical.choice, Quot.sound]`
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi_id` →
  `[propext, Classical.choice, Quot.sound]`
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi_eq_of_phiEquivalent` →
  `[propext, Classical.choice, Quot.sound]`
* `OpenMath.Chapter3.Section312.RKTableau.elementaryWeightQ_phi_eq_of_eq` →
  `[propext, Classical.choice, Quot.sound]`

`lake env lean OpenMath/Chapter3/Section381.lean` runs in ~6s warm with
zero errors and only pre-existing simp-arg warnings (lines 3151, 3154
of `gen_dwsp_eq`'s closure — unrelated to this cycle's edits).
`lake build OpenMath.Chapter3.Section381` completes successfully
(1943 jobs). Sorry count remains 0.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`elementaryWeightQ_phi`** (def):
  - Textbook reference: extension of Butcher §312D `Φ(t)` to the §383
    group's underlying set. There is no explicit textbook entity for the
    quotient version, but the symbol is the natural functorial extension
    of `Φ : RKTableau → RootedTree → ℝ` to the §383 quotient.
  - Lean statement captures: same content as `Φ(t)` (the elementary
    weight) but at the quotient level. Well-definedness is the *content*
    of `PhiEquivalent`'s definition, not an additional fact.
  - Definition smuggling check: PASS — the value `M.elementaryWeight t`
    is the *primary* mathematical meaning; the lift via `Quotient.lift`
    delivers exactly this value on each class, with well-definedness
    coming for free from `PhiEquivalent`'s defining property.

* **`elementaryWeightQ_phi_mk`** (simp lemma):
  - Conclusion: `elementaryWeightQ_phi ⟦⟨s, M⟩⟧ t = M.elementaryWeight t`,
    proved by `rfl`. This is a standard `Quotient.lift` unfold lemma,
    paralleling cycle 232's `composeQ_phi_mk` and cycle 236's
    `inverseQ_phi_mk`.
  - Tautology check: PASS — no hypotheses; conclusion is an equation
    between distinct syntactic forms (lift-application vs underlying
    value).
  - Identity-proof check: `rfl` is mechanical unfolding, not vacuous —
    the simp-set entry is the whole point.

* **`elementaryWeightQ_phi_composeQ_phi_mk`** (theorem):
  - Quotient-level lift of Butcher's composition rule for Φ via cycle
    225's `compose_elementaryWeight_decomp`. The textbook does NOT
    state this explicitly (the per-stage decomposition is implicit in
    §384–§386's manipulations), but the conclusion is verbatim cycle
    225's RHS with `elementaryWeightQ_phi` substituted for
    `(M₁.compose M₂).elementaryWeight` and `M₁.elementaryWeight`.
  - Tautology check: PASS — the conclusion uses the `composeQ_phi`
    operation, which is non-trivially equated to the per-representative
    `(M₁.compose M₂).elementaryWeight`. No hypothesis equals the
    conclusion.
  - Identity-proof check: PASS — proof is `show ... ; exact
    compose_elementaryWeight_decomp M₁ M₂ t`. The `show` is the
    quotient-level → representative-level definitional bridge; the
    `exact` discharges the actual mathematical content via cycle 225.

* **`elementaryWeightQ_phi_id`** (theorem):
  - Conclusion: `elementaryWeightQ_phi ⟦⟨0, RKTableau.id⟩⟧ t = 0`. The
    underlying fact (cycle 228's `id_elementaryWeight`) is a direct
    Butcher consequence: `Φ` of the 0-stage `id` is the empty `Fin 0`
    sum.
  - Tautology check: PASS — no hypotheses.
  - Identity-proof check: `show (RKTableau.id : RKTableau 0).
    elementaryWeight t = 0; exact id_elementaryWeight t`. Routes the
    quotient-level statement through cycle 228's named lemma; real
    work.

* **`elementaryWeightQ_phi_eq_of_phiEquivalent`** (theorem):
  - Hypothesis: `PhiEquivalent M M'`. Conclusion: equality of
    `elementaryWeightQ_phi` images of `⟦⟨s, M⟩⟧` and `⟦⟨s', M'⟩⟧` on
    every tree `t`.
  - Tautology check: PASS — the conclusion does NOT equal the
    hypothesis verbatim. The hypothesis is universally quantified over
    `t` (the *content* of `PhiEquivalent`); the conclusion specializes
    to a single `t` and lifts to the quotient level.
  - Identity-proof check: borderline (`show ... ; exact hPhi t` is
    "exact h" applied to a specialization). This is the canonical
    well-definedness packaging at the quotient level — it provides a
    named, reusable bridge from per-tableau `PhiEquivalent` witnesses
    to quotient-level elementary-weight equalities. Analogous to cycle
    232's `compose_phiEquivalent_compose` providing a named bridge for
    `composeQ_phi`'s respect obligation. Not vacuous.

* **`elementaryWeightQ_phi_eq_of_eq`** (theorem):
  - Hypothesis: `q = q'` (equality of quotient classes). Conclusion:
    `elementaryWeightQ_phi q t = elementaryWeightQ_phi q' t`.
  - Tautology check: PASS — conclusion is about function application;
    hypothesis is about class equality.
  - Identity-proof check: borderline (`rw [hq]` is a one-liner). This
    is essentially `congrArg (elementaryWeightQ_phi · t)`, packaged for
    use with `Quotient.sound`-derived class equalities (e.g. cycle 234's
    `composeQ_phi_id_left`, exercised in the cycle 239 P1.D end-to-end
    example). Real downstream utility; not vacuous.

No hypothesis strengthening, no definition smuggling, no tautology, no
absent theorems. Cycle 239 follows the cycle 232/236-era patterns for
quotient-level lifts.

## Dead ends

None this cycle — the strategy's design closed cleanly on first
attempt after a single fix (wrapping the new content in
`section`/`open OpenMath.Chapter3.Section310`/`end` to bring
`RootedTree` into scope, since the parent `RKTableau` namespace's
opens are scoped to inner `section` blocks, not the outer namespace
body). Initial compile reported `RootedTree`-as-`Sort u_1` mismatches;
adding the section block resolved them. Build then succeeded with no
further errors.

## Discovery

* **GPFS pathology persists (43rd timeout, cycles 182–239).** Pattern
  unchanged: EXIT=124/143 after the timeout, near-zero CPU
  (0.2–1.2% of wall), GPFS-disk-wait. Pivot via parallel new files
  (cycle 237's Section441B.lean approach) remains the only viable
  workaround for §441-related work that doesn't transitively touch
  Section441.lean.

* **`Quotient.lift` lifting `∀ t : ..., f M t = f M' t` predicates is
  one-liner.** When the equivalence relation is *defined* as a pointwise
  function-equality (as `PhiEquivalent` is), the `Quotient.lift` respect
  proof is literally `exact hRel t` for the fixed parameter `t`. This
  is structurally simpler than cycle 232's `composeQ_phi` (which needed
  the bilinear `compose_phiEquivalent_compose` from cycle 232's
  generalized-weight-compatibility induction) or cycle 236's
  `inverseQ_phi` (which needed `inverse_phiEquivalent_inverse` from
  cycle 235's antipode-formula structural identities). The cleanness
  here suggests that any other "function of an RKTableau parametrized
  by a RootedTree" that is constant on PhiEquivalent classes will lift
  with a similarly trivial respect proof — useful for cycle 240+ work
  on `internalWeight`, `derivativeWeight`, etc. if their
  PhiEquivalent-invariance properties are needed.

* **Bottom-block sum doesn't descend to the abstract Φ-quotient.** The
  per-representative composition decomposition lemma uses the stage
  count `s₂` of the right factor's representative; this dependency
  cannot be eliminated without choosing a canonical representative or
  reformulating in terms of B-series coefficients (which would route
  back through thm:311B/313B — both unformalized). The
  `_mk` suffix on `elementaryWeightQ_phi_composeQ_phi_mk` documents
  this limitation: the lemma is genuine machinery, but only usable on
  classes with chosen representatives. For end-to-end downstream
  applications, this means future quotient-level computations will
  typically need a `Quotient.inductionOn` step to introduce
  representatives before the decomposition fires.

* **Cycle 239's `elementaryWeightQ_phi_eq_of_eq` (the `congrArg`-style
  bridge) is genuinely needed for end-to-end pipelines** — the cycle
  239 P1.D end-to-end example shows that bridging from cycle 234's
  `composeQ_phi_id_left` (which produces a class equality
  `composeQ_phi ⟦⟨0, id⟩⟧ ⟦⟨2, paddedEuler⟩⟧ = ⟦⟨2, paddedEuler⟩⟧`) to
  an elementary-weight statement requires `congrArg`-style class-eq
  propagation followed by definitional unfold. The named lemma turns
  this into a one-line `rw` instead of an inline `congrArg` chain.

## Suggested next approach

Cycle 240+ continues on the §384 homomorphism track. Options ranked by
single-cycle closeability:

1. **§383 elementary-weight algebra on the §382 `Equivalent`-quotient
   side** — define `elementaryWeightQ : Quotient Equivalent.setoidSigma
   → RootedTree → ℝ` *iff* the `Equivalent → PhiEquivalent` direction
   can be established. The Lean machinery is mirror-image of cycle
   239's, but the respect proof requires
   `Equivalent M M' → ∀ t, M.elementaryWeight t = M'.elementaryWeight t`
   — i.e. `Equivalent → PhiEquivalent`, the deferred direction in
   `thm_381H_deferred.md`. So this option is *blocked* on the same
   B-series machinery (thm:311B / thm:313B) as the homomorphism
   itself, and is NOT single-cycle.

2. **Extend cycle 239's infrastructure with the `_composeQ_phi`
   abstract-quotient version, via `Quotient.inductionOn₂` packaging.**
   Wrap the per-representative `elementaryWeightQ_phi_composeQ_phi_mk`
   in a Quotient.inductionOn₂ that takes a parametric RHS
   `(q' : Quotient PhiEquivalent.setoidSigma) → ℝ` from an external
   well-definedness witness. Likely single-cycle but downstream
   utility is unclear without a target consumer.

3. **Extend Section441B.lean with `cInverseLog_two_eq` and
   `cInverseLog_three_eq` closed forms** (Priority 2 stretch from
   cycle 238/239 strategies). Axiom-clean closed-form computations,
   ~30 LOC each. Independent track; not blocked by GPFS or B-series
   machinery. Useful sanity witnesses for cycle 238's
   `cInverseLog_neg`.

4. **Pivot to a tree-combinatorics target in §302 (independent
   track).** Defer §384 homomorphism work entirely; ship a fresh
   chapter target. Lower risk but lower coupling to existing
   §380s infrastructure.

Recommendation: **option 3 (Section441B `cInverseLog_two_eq` /
`cInverseLog_three_eq`)** for cycle 240 — single-cycle deliverable,
independent of GPFS and B-series blockers, validates cycle 237/238's
PowerSeries machinery on concrete numerical witnesses. If the planner
disagrees and pursues option 1/2, the cycle 239 P1.D end-to-end example
shows the proof pattern: `Quotient.inductionOn` + `rw
[elementaryWeightQ_phi_eq_of_eq …]` + `rfl`.

DO NOT attempt the §441 GPFS smoke test again under any circumstances
— the 43-timeout pattern across cycles 182–239 is conclusive.
