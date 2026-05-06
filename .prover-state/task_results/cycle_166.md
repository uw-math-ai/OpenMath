# Cycle 166 Results

## Worked on

* `thm:454A` "A G-stable linear multistep method is A-stable" — opened
  Butcher §454 with predicate + refutability witness + bridging
  infrastructure. Theorem 454A itself **not** formalised this cycle;
  see Path 3 fallback below.
* New file `OpenMath/Chapter4/Section454.lean`.
* Updated `OpenMath/Chapter4.lean` to include the new section.

## Approach

Followed cycle 166 strategy with graceful degradation Path 1 → Path 2 →
Path 3.

* **Step 1** (predicate): Defined
  `LinearMultistepMethod.IsAStable {k}` in
  `OpenMath.Chapter4.Section404` namespace, using Butcher's §454
  proof's stated boundary-locus form: `∀ w : ℂ, ‖w‖ < 1 → β(w) ≠ 0
  → 0 < (α(w) / β(w)).re`. Lifted via `Polynomial.aeval w (αPoly M)`
  with `αPoly` from §410 (cycle 074). ✓ landed.
* **Step 2** (algebraic identity): Drafted
  `algebraic_identity_454A` with auxiliary lemmas
  `dotProduct_vecMulVec_map_lift`, `gTopLeft_quadForm_eq`,
  `gBottomRight_quadForm_eq`. **STALLED** — `lake env lean` ran for
  10+ min without producing output (likely Lean's elaboration hit a
  blowup on dependent if-then-else under
  `Fin.sum_univ_castSucc`/`Fin.sum_univ_succ`). Two retries had the
  same behaviour.
* **Step 3** (`gStable_isAStable`): Did not attempt; depends on
  Step 2.
* **Step 4** (witnesses):
  - `bdf2LMM_isAStable`: dropped (depends on Step 3).
  - `explicitEulerLMM_not_isAStable`: ✓ landed. Manually proved by
    exhibiting `w = -9/10 ∈ ℂ` and showing
    `α(w)/β(w) = -19/9` has negative real part, contradicting
    `IsAStable`.
* **Step 5** (Aristotle): submitted batch (project_id
  `89e8a962-b3eb-4f7d-b397-c77bf18773d4`) with all 5 sorries.
  After 35+ min, still at 11% complete; not waiting blocked the
  cycle.
* **Step 6** (housekeeping): Did **not** update lean_status's
  thm:454A row (still `unformalized`); did **not** flip plan.md row.

**Bridging infrastructure shipped** (used by future cycle 167's
Stage 2/3 proof):
* `vanW`, `vanW₁` — Vandermonde test vectors `Fin (k+1) → ℂ` and
  `Fin k → ℂ`.
* `aeval_αPoly_eq` — `aeval w (αPoly M) = Σ alphaVec j · wʲ`
  bridging the §410 polynomial form and the §451 vector form.
* `aeval_βPoly_eq` — similarly for `βPoly`.

## Result

**Path 3 fallback shipped.** Score: +1 (definition + refutability
witness + bridging infrastructure is real progress on a fresh
section file with no regression risk; Section454 builds clean).

## Faithfulness check

### `LinearMultistepMethod.IsAStable`

* Entity: thm:454A (the predicate is the *target* of the theorem,
  formalised as the boundary-locus criterion Butcher's proof uses).
* Textbook statement (`extraction/formalization_data/entities/thm_454A.json`):
  > "A $G$-stable linear multistep method is $A$-stable."
* Butcher §454 proof's stated criterion:
  > "We use the criterion that if `|w| < 1`, then `z = α(w)/β(w)` is
  > in the right half-plane."
* Lean statement captures: same content. The boundary-locus form is
  what Butcher *uses*, not the stability-region characterisation.
  Documented in the docstring; the equivalence with "stability
  region contains closed left half-plane" is a non-trivial
  maximum-modulus / boundary-locus statement that we explicitly
  defer.

### `aeval_αPoly_eq` / `aeval_βPoly_eq`

* These are **bridging lemmas**, not entities. They state that
  evaluating `αPoly M` (resp. `βPoly M`) at `w : ℂ` equals the
  sum `Σ alphaVec j · wʲ` (resp. `Σ betaVec j · wʲ`).
* Faithfulness: this is exactly the relationship between the §410
  polynomial form and the §451 vector form claimed in Butcher
  §451's matrix-`M(G)` derivation; no smuggling.

### `explicitEulerLMM_not_isAStable`

* Negative non-vacuity for `IsAStable` (no entity ID). The
  refutability witness is `w = -9/10 + 0i`, which gives
  `α(w)/β(w) = -19/9`, real part `-19/9 < 0`, contradicting
  `IsAStable`.
* Faithfulness: this is a sanity check that `IsAStable` is not
  vacuously true. Explicit Euler is well-known to NOT be A-stable
  (Hairer-Wanner II.4 examples), and this matches the textbook
  intuition.

### Definition smuggling check (per CLAUDE.md)

The §454 paragraph "we use the criterion that if `|w| < 1`, then
`z = α(w)/β(w)` is in the right half-plane" *names* the criterion
Butcher uses; the criterion is a known *equivalent* of A-stability
(Butcher §351), but the equivalence proof is non-trivial. We have
NOT defined "A-stability" abstractly and then proved the
equivalence; we have defined `IsAStable` *as* the boundary-locus
criterion and explicitly documented that this is the form Butcher's
§454 proof uses. The definition's docstring is explicit about the
deferred equivalence. **No smuggling.**

## Dead ends

* **Direct unfolded proof of `algebraic_identity_454A`**: the proof
  unfolds `M.gMatrix`, `gTopLeft`, `gBottomRight` and applies
  `Fin.sum_univ_castSucc`/`Fin.sum_univ_succ` to split off the
  boundary cases (i = Fin.last k for gTopLeft, i = 0 for
  gBottomRight). Lean appears to elaborate the resulting nested
  dependent if-then-else over `Fin (k+1) × Fin (k+1)` with two
  layers of `dif_neg` very slowly (10+ min, no output). The proof
  may still be correct; the issue is Lean's term-elaboration
  performance on the unfolded matrix entries.

* **Aristotle batch**: still at 11% after 35+ min. Useful proofs
  (if any) would arrive after the cycle deadline. Not blocking.

## Discovery

* `Matrix.PosSemidef` over ℂ requires `open scoped ComplexOrder`
  to surface the `PartialOrder ℂ` instance. Without this, even
  stating `(A.map (algebraMap ℝ ℂ)).PosSemidef` fails type-class
  synthesis with `failed to synthesize PartialOrder ℂ`.
* `Fin.sum_univ_castSucc` + `dif_neg` for boundary i = Fin.last k
  combined with `Matrix.dotProduct` / `Matrix.mulVec` *unfolded*
  appears to be a Lean elaboration hot-spot. Future quadratic-form
  proofs over `Fin (k+1)` should factor the boundary lemmas into
  separate named theorems with their own `lake env lean` round
  rather than unfolding inline.

## Suggested next approach

See `.prover-state/issues/thm_454A_stage_2_3_stall.md`. Recommended
Path A:

1. **Cycle 167**: factor `gTopLeft_quadForm_eq` and
   `gBottomRight_quadForm_eq` as standalone lemmas in
   `Section451.lean` (or a fresh `Section451Aux.lean`). Aristotle-batch
   them.
2. **Cycle 167 (or 168)**: prove `algebraic_identity_454A` using
   the named quadratic-form lemmas + `aeval_αPoly_eq` /
   `aeval_βPoly_eq` (already shipped in cycle 166).
3. **Cycle 168 (or 169)**: prove `complexLift_posSemidef_of_real_posSemidef`
   and `complexLift_re_dotProduct_pos_of_real_posDef` as standalone
   theorems. These are real → ℂ PSD/PD lifts via re/im
   decomposition.
4. **Cycle 169 (or 170)**: combine into `gStable_isAStable` and
   `bdf2LMM_isAStable`. Flip plan.md row to `[x]` and update
   lean_status.

Alternative: bypass the quadratic-form identity and prove
`gStable_isAStable` directly via `Matrix.fromBlocks` formalism
(strategy Option B in the issue file) — heavier setup, possibly
cleaner term form. Try Path A first.
