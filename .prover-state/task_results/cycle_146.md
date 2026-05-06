# Cycle 146 Results

## Worked on
- `OpenMath.Chapter5.Section510.padded2DEulerGLM_not_isAStable` —
  Priority 1 (per planner): r = 2 negative non-vacuity witness for
  `def:520E` (A-stability), strengthening cycle 136's r = 1 witness
  `explicitEulerGLM_not_isAStable`.
- `OpenMath.Chapter5.Section510.padded2DEulerGLM_not_isLStable` —
  Priority 1 (per planner): r = 2 negative non-vacuity witness for
  `def:520F` (L-stability), strengthening cycle 137's r = 1 witness
  `explicitEulerGLM_not_isLStable`.

Together these saturate the four-corner non-vacuity coverage for both
predicates at r = 2 (paired with cycle 143's positive r = 2 witnesses
`padded2DBackwardEulerGLM_isAStable` / `padded2DBackwardEulerGLM_isLStable`).

## Approach
**`padded2DEulerGLM_not_isAStable`** (~20 lines):

1. Specialise the A-stability predicate at `z = -3`, using
   `Re(-3) = -3 ≤ 0` (closed left half-plane).
2. From the cycle 134 closed-form `padded2DEulerGLM_stabilityFunction`
   `Φ(w, z) = w · (w - (1 + z))`, evaluate
   `Φ(-2, -3) = -2 · (-2 - (1 + -3)) = -2 · 0 = 0` via `ring`.
3. Compute `‖(-2 : ℂ)‖ = 2 > 1` via
   `norm_neg` + `Complex.norm_ofNat` (cycle 136's pattern).
4. Apply Theorem 520D direction (2)
   `GeneralLinearMethod.instabilityRegion_supseteq_outside_disc`
   (cycle 126) as a black box: `∃ w, ‖w‖ > 1 ∧ Φ(w, z) = 0` ⇒
   `z ∈ instabilityRegion = (stabilityRegion)ᶜ`.
5. Membership in both `stabilityRegion` (from A-stability) and its
   complement (from step 4) is a contradiction.

**`padded2DEulerGLM_not_isLStable`** (1 line): one-liner mirroring
cycle 137's `explicitEulerGLM_not_isLStable` exactly — since
`IsLStable := IsAStable ∧ ρ(M(·)) → 0 cocompactly`, the negation
follows from the A-stability conjunct via `.1` projection and
`padded2DEulerGLM_not_isAStable`.

**Insertion deviation from planner**: the planner suggested inserting
both theorems at line 1369 (immediately after `padded2DEulerGLM_isRKStable`
and before the Theorem 520D section). I instead inserted them at the end
of the file (after `end InstabilityRegion520D`, before
`end OpenMath.Chapter5.Section510`) so the proof can call
`instabilityRegion_supseteq_outside_disc` as a black box. Inserting at
the planner's spot would have required forward-referencing the
`private theorem stabilityFunction_eq_zero_iff_mem_spectrum` and
replicating the `spectrum.pow_mem_pow` machinery (~30 LOC of inline
duplication). The end-of-file placement reduces the proof to ~10 lines
of actual logic. Documented in the inline section header comment.

## Result
**SUCCESS** — both theorems compile axiom-clean.

* `lake env lean OpenMath/Chapter5/Section520.lean` — clean compile,
  no errors, no warnings.
* `#print axioms padded2DEulerGLM_not_isAStable`:
  `[propext, Classical.choice, Quot.sound]` (the standard set).
* `#print axioms padded2DEulerGLM_not_isLStable`:
  `[propext, Classical.choice, Quot.sound]` (the standard set).
* No new sorry's introduced; sorry count remains at 0 across `OpenMath/`.

## Faithfulness check

**`padded2DEulerGLM_not_isAStable`** — *negative non-vacuity witness*
for `def:520E`. No new definition; just a refutation of `IsAStable`
applied to a concrete GLM (`padded2DEulerGLM`, defined in cycle 133).

- Entity ID and textbook statement (`extraction/formalization_data/entities/def_520E.json`):
  > A general linear method is 'A-stable' if M(z) is power-bounded for
  > every z in the left half complex plane.
- Lean statement captures: same content (refutation form). The theorem
  states `¬ padded2DEulerGLM.IsAStable`, exhibiting `z = -3` (closed
  left half-plane) outside the stability region.
- No divergence. The witness proves that A-stability is genuinely
  refutable at r = 2, complementing cycle 136's r = 1 refutation. The
  stability region is the textbook closed unit disc centred at -1
  (`R(z) = 1 + z`), and `-3` is at distance 2 from -1 — strictly
  outside.

**`padded2DEulerGLM_not_isLStable`** — *negative non-vacuity witness*
for `def:520F`. No new definition; just a refutation.

- Entity ID and textbook statement (`extraction/formalization_data/entities/def_520F.json`):
  > A general linear method is L-stable if it is A-stable and
  > ρ(M(∞)) = 0.
- Lean statement captures: same content (refutation form). `IsLStable`
  is encoded as the conjunction `IsAStable ∧ Tendsto (ρ ∘ M) cocompact (𝓝 0)`,
  so `¬ A-stable ⇒ ¬ L-stable` by ∧-projection.
- No divergence. The proof reuses the A-stability refutation since
  L-stability ⇒ A-stability is built into the predicate definition.

**No new `def`, `class`, or `structure` declarations introduced this
cycle.** Both new theorems are negative non-vacuity witnesses against
existing predicates `IsAStable` and `IsLStable`. No risk of definition
smuggling, tautology, identity-only proofs, or hypothesis-strength
inflation.

**No `axiom` or `constant` declarations introduced.**

## Dead ends
None — Priority 1 closed on first attempt with the chosen approach
(black-box use of `instabilityRegion_supseteq_outside_disc`). The
planner's two suggested routes (Route A spectrum-radius lower bound,
Route B direct entry-wise computation) would also have worked but
both require ~3× the LOC of the chosen approach.

The placement deviation (end-of-file vs. line 1369) was the only
judgment call; I chose placement that keeps the proof short and reuses
existing infrastructure. The theorems remain easily discoverable via
grep on `padded2DEulerGLM`.

## Discovery
- **`instabilityRegion_supseteq_outside_disc` (cycle 126) is a clean
  black-box for negative A-stability witnesses when a closed-form
  stability function is available.** Any future negative A-stability
  witness can follow this exact 4-step pattern: (a) exhibit `z` in the
  closed left half-plane, (b) exhibit a `w` with `‖w‖ > 1` zeroing
  `Φ(w, z)`, (c) apply the lemma, (d) note the membership-vs-complement
  contradiction. This is materially shorter than the cycle 136 r = 1
  template (~25 LOC), which inlined the spectrum machinery before
  Theorem 520D was available.
- `(M.stabilityRegion)ᶜ` membership unfolds to `¬ M.stabilityRegion`
  membership in Lean 4 without an explicit `Set.mem_compl_iff` rewrite —
  `exact h_in hz_stab` typechecks directly when `h_in : z ∈ Sᶜ` and
  `hz_stab : z ∈ S`. Useful pattern for any future
  `stabilityRegion`-vs-`instabilityRegion` clash.

## Suggested next approach

The four-corner non-vacuity coverage matrix for `def:520E` and
`def:520F` is now saturated at both r = 1 and r = 2. The natural next
steps for the planner to consider:

1. **`thm:550A` n = 5 stepping stone via Aristotle**: Priority 2 of
   this cycle (the `doublyCompanionMatrix_det_factorization_n_five`
   stepping stone). I did NOT submit this Aristotle batch this cycle —
   Priority 1 dominated the budget and CLAUDE.md restricts to one
   30-min sleep window per cycle. A future cycle should either submit
   it as Aristotle Priority 1 or attempt a manual proof reusing cycle
   145's `Matrix.det_succ_row_zero` + `det_fin_three` template
   (~250 LOC, possible heartbeats concern).
2. **General-`n` `thm:550A` infrastructure**: still deferred per
   `.prover-state/issues/thm_550A_general_n.md`; concrete-`n` ladder
   now n = 1, 2, 3, 4 axiom-clean. Might be worth scaffolding a
   `Matrix.det_succ_row_zero`-induction template now that the n = 4
   manual proof has revealed the cofactor pattern.
3. **`def:521A` non-vacuity strengthening**: similar four-corner
   matrix exercise for `HasStabilityOrder`. The current witnesses are
   bare; might benefit from at least one *substantive* positive and
   one negative witness pair.
4. **`def:530B` (Order relative to starting method)**: still deferred
   per cycle 145's strategy. Requires Taylor-expansion infrastructure
   for the SM-vs-ES residual; multi-cycle scope.
5. **`thm:535A` (Underlying one-step method)**: an unblocked Chapter 5
   theorem that has not yet received attention — could be a fresh
   target.

Priority 3 (housekeeping check on `.prover-state/issues/thm_550A_general_n.md`)
was not needed: the n = 4 closure is referenced in cycle 145's commit
message and the issue file's status is current.
