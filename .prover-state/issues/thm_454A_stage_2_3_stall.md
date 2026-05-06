# Issue: thm:454A Stages 2/3 stall (cycle 166)

## Blocker

Cycle 166 shipped Path 3 of the cycle 166 strategy: the
`IsAStable` predicate plus the refutability witness
`explicitEulerLMM_not_isAStable`, but **not** `algebraic_identity_454A`
(Step 2) nor `gStable_isAStable` (Step 3 = Theorem 454A itself).

The cycle's draft proof of `algebraic_identity_454A` reached
`lake env lean` but compilation kept timing out at 10+ min before
producing any error or success. Suspected root cause: the proof
unfolds `M.gMatrix`, `gTopLeft`, `gBottomRight` simultaneously and
manipulates dependent if-then-else under `Fin.sum_univ_castSucc` /
`Fin.sum_univ_succ`. Lean's elaboration of `simp only [..., gTopLeft,
Matrix.of_apply, ...]` plus the if-then-else discharge via
`dif_pos` / `dif_neg` evidently blows up on the nested matrix-vector
unfoldings.

## Context

* File: `OpenMath/Chapter4/Section454.lean` (cycle 166).
* Cycle 166 strategy: `.prover-state/strategy.md` (Path 1 →
  Path 2 → Path 3 graceful-degradation order).
* What landed in cycle 166:
  - `LinearMultistepMethod.IsAStable` (predicate, faithful to
    Butcher §454 boundary-locus form).
  - `aeval_αPoly_eq`, `aeval_βPoly_eq` (bridge §410 polynomial
    evaluations to §451 vector dot products).
  - `vanW`, `vanW₁` (Vandermonde test vectors used by the §454
    proof).
  - `explicitEulerLMM_not_isAStable` (negative non-vacuity).
* What did NOT land:
  - `algebraic_identity_454A`: the §451e quadratic-form identity.
  - `complexLift_posSemidef_of_real_posSemidef` and
    `complexLift_re_dotProduct_pos_of_real_posDef`: the real → ℂ
    PSD/PD lifts.
  - `gStable_isAStable`: Theorem 454A.
  - `bdf2LMM_isAStable`: BDF2 corollary.

## What was tried

* Direct proof of `algebraic_identity_454A` via auxiliary lemmas:
  - `dotProduct_vecMulVec_map_lift` — sesquilinear factorisation.
  - `gTopLeft_quadForm_eq` — `star W ⬝ᵥ ((gTopLeft G).map ι *ᵥ W) =
    star W₁ ⬝ᵥ (G.map ι *ᵥ W₁)`.
  - `gBottomRight_quadForm_eq` — `star W ⬝ᵥ ((gBottomRight G).map ι
    *ᵥ W) = ‖w‖² · (star W₁ ⬝ᵥ (G.map ι *ᵥ W₁))`.

  Each of these required `Fin.sum_univ_castSucc` / `Fin.sum_univ_succ`
  decomposition, plus `dif_neg` on the boundary cases, plus
  index-coercion reasoning. The proof script terminated in two
  10-min `lake env lean` runs without producing output.

* Submitted Aristotle batch (project_id
  `89e8a962-b3eb-4f7d-b397-c77bf18773d4`) covering all 5 sorries
  but it remained at 11% complete after 35+ minutes; not waiting
  blocked the cycle.

## Possible solutions for cycle 167

### Option A (preferred): factor `gTopLeft_quadForm_eq` /
`gBottomRight_quadForm_eq` into separate single-fact files

* Land them as standalone lemmas in `Section451.lean` (or a fresh
  `Section451Aux.lean`) where they are not under the time pressure
  of the `algebraic_identity_454A` proof.
* Once available as named lemmas, `algebraic_identity_454A`'s
  body becomes a short ring-style combination plus the `1 - ‖w‖²`
  rearrangement.
* Estimated effort: 1–1.5 cycles.

### Option B: use Mathlib's `Matrix.fromBlocks` formalism

* Reformulate `gTopLeft G = Matrix.fromBlocks G 0 0 0` (sum of
  `(Fin k) ⊕ Fin 1` blocks) under a `Fin (k+1) ≃ Fin k ⊕ Fin 1`
  equivalence. Same for `gBottomRight G = Matrix.fromBlocks 0 0 0
  G`.
* Mathlib has `Matrix.fromBlocks_mulVec` and the dot product
  computation reduces to four `Sum.elim`-driven sums that may
  collapse cleaner than the current dependent-if approach.
* Estimated effort: 1.5–2 cycles, dominated by the equivalence
  setup.

### Option C: skip `algebraic_identity_454A` and prove
`gStable_isAStable` directly

* The Butcher §454 proof is a ~5-line argument; in Lean, with the
  right lemmas (PSD lift + a "1 - ‖w‖² > 0" lemma), it could go
  through end-to-end without naming the quadratic-form identity.
* Risk: monolithic proof harder to debug; the cycle 166 stall
  suggests `Fin (k+1)` quadratic forms over a complex matrix are
  the real bottleneck regardless of how they're packaged.
* Estimated effort: same as Option A but worse modularity.

### Option D: chunk `gStable_isAStable` over `k`

* Prove for fixed small `k` (1, 2, 3) by `decide`/`fin_cases`/
  explicit matrix manipulations.
* Sufficient for `bdf2LMM_isAStable` (k = 2).
* Faithfulness penalty: it's not the *general* Theorem 454A;
  it's the BDF2 corollary directly. Mark as a placeholder, not as
  thm:454A formalised.

## Recommendation

Path A. Cycle 167 should:
1. Add `gTopLeft_quadForm_eq` and `gBottomRight_quadForm_eq` as
   standalone named theorems in `Section451.lean` (each with
   their own `lake env lean` round). Aristotle-batch them.
2. Add `algebraic_identity_454A` as a short proof using these
   plus `aeval_αPoly_eq` / `aeval_βPoly_eq` (already shipped).
3. Add `complexLift_posSemidef_of_real_posSemidef` and
   `complexLift_re_dotProduct_pos_of_real_posDef` as standalone
   named theorems (likely a separate file `Section454Aux.lean`).
4. Combine into `gStable_isAStable` and `bdf2LMM_isAStable`.

The cycle 166 deliverables are not wasted: `IsAStable`,
`aeval_αPoly_eq`, `aeval_βPoly_eq`, `vanW`, `vanW₁`, and
`explicitEulerLMM_not_isAStable` all carry forward unchanged.

## Cycle 167 update

**Path A landed**: cycle 167 shipped `gTopLeft_quadForm_eq` and
`gBottomRight_quadForm_eq` as standalone named theorems in
`Section454.lean` (alongside ten private boundary-case
sub-lemmas), and refactored `Section451.gTopLeft` /
`Section451.gBottomRight` to be polymorphic in the scalar ring
`R` (only `[Zero R]` needed). Both main theorems are
axiom-clean (`[propext, Classical.choice, Quot.sound]`); BDF2
witnesses in `Section451.lean` rebuilt without modification.

**Stage 2 status**: ✓ DONE.

**Stage 3 status**: still open.
`algebraic_identity_454A` was NOT attempted in cycle 167
(Priority 3 stretch goal deferred — Priority 2 took the cycle
budget after a `simp only [Matrix.dotProduct]` dead end).
Cycle 168 should now have a short path:

1. Assemble `algebraic_identity_454A` from the two new
   quadratic-form lemmas + `aeval_αPoly_eq` / `aeval_βPoly_eq`
   + the `vanW.succ = w • vanW.castSucc` shift identity.
2. Add the two complex-lift PSD/PD helpers
   (`complexLift_posSemidef_of_real_posSemidef`,
   `complexLift_re_dotProduct_pos_of_real_posDef`) — likely a
   fresh `Section454Aux.lean`.
3. Combine into `gStable_isAStable` and the BDF2 corollary
   `bdf2LMM_isAStable`.

**Pattern that worked (Path A): named-decomposition with
≤5-line sub-lemmas in `private` scope.** If cycle 168 hits any
further elaboration stall on `algebraic_identity_454A`, the
remediation is to factor *that* proof into the same
named-decomposition pattern.

**Pitfall to avoid**: `simp only [Matrix.dotProduct]` does not
fire — `dotProduct` is at root namespace in current Mathlib,
not `Matrix.dotProduct`. Use `show ∑ i, _ * _ = _` to expose
the sum form directly, then `Fin.sum_univ_castSucc` /
`Fin.sum_univ_succ`.
