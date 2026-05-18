# Cycle 369 strategy

## Context and current state

Cycle 368 shipped `elementaryWeightQ_phi_inv_broom₃` (closed form for
`Φ_{η⁻¹}` at the order-3 tree `broom₃ = mk [vertex, vertex]`) plus the
`powRep_sum_eq_of_agreement_at_broom₃_zero` m=0 corollary, both
axiom-clean. **§422 streak: 34 consecutive axiom-clean cycles (336–368).**

The Route B Hypothesis (closed-form-per-tree witness ladder) is now
supported by three data points:
- **vertex** (cycle 366): `Φ_{η⁻¹}(τ) = −Φ_η(τ)` (trivial via cycle 341 P2).
- **cherry** (cycle 367): `Φ_{η⁻¹}(cherry) = Φ_η(τ)² − Φ_η(cherry)`.
- **broom₃** (cycle 368): `Φ_{η⁻¹}(broom₃) = −Φ_η(τ)³ + 2·Φ_η(τ)·Φ_η(cherry) − Φ_η(broom₃)`.

Sub-lemma A's general body (`powRep_sum_eq_of_strict_subtree_agreement`
at `OpenMath/Chapter4/Section422.lean:2272`) remains the only sorry
(grandfathered from cycle 365). Cycle 368 task results recommend
**Option A**: attempt the inductive `t.order` formulation of Sub-lemma A.

## Priority 1 — Option A: m=0 inductive Sub-lemma A scaffold (PRIMARY)

**Target deliverable**: a new public theorem at the **m=0 specialization**
(no `powRep` heterogeneity), proved by **strong induction on `t.order`**:

```lean
theorem elementaryWeightQ_phi_inv_eq_of_closed_subtree_agreement
    (t : RT) (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi η_q⁻¹ t = elementaryWeightQ_phi η_q'⁻¹ t
```

This is precisely Sub-lemma A specialised at `m = 0` (so the exponent
`-(((m+1):ℕ):ℤ) = -1` reduces to plain inverse, sidestepping `powRep`'s
heterogeneous-stage obstacle that blocked cycle 365's general body).

**Why this works at m=0 where the general case fails**: per cycle 365 /
cycle 366 task results, the heterogeneity obstacle is specifically that
`Quotient.inductionOn₂ η_q η_q'` followed by cycle 361's `_zpow_negSucc_mk`
expansion exposes `(M.powRep (m+1)).2` and `(M'.powRep (m+1)).2` —
different stage counts when `M.1 ≠ M'.1`. At **m=0**, `η_q^(-1) = η_q⁻¹`
expands directly via cycle 358's `elementaryWeightQ_phi_inv_mk` (no
`powRep` involved); the representatives `M` and `M'` each have their own
fixed stage count and the substitution is per-representative.

### Recipe (strategy §B)

1. **Setup**: `Quotient.inductionOn₂` on `η_q` and `η_q'` produces
   representatives `⟨s, M⟩` and `⟨s', M'⟩`. Translate `h_closed` via
   cycle 239's `elementaryWeightQ_phi_mk` to a per-representative form:
   `∀ u, u.order ≤ t.order → M.elementaryWeight u = M'.elementaryWeight u`.

2. **Reduce to a representative-level lemma**: state and prove

   ```lean
   theorem inverse_elementaryWeight_eq_of_closed_subtree_agreement
       {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') (t : RT)
       (h : ∀ u, u.order ≤ t.order → M.elementaryWeight u = M'.elementaryWeight u) :
       M.inverse.elementaryWeight t = M'.inverse.elementaryWeight t
   ```

   This is the workhorse. Prove by **strong induction on `t.order`**
   using `(measure RootedTree.order).wf.induction` or the
   `WellFoundedRelation RootedTree := measure RootedTree.order` instance
   from cycle 343 (`OpenMath/Chapter3/Section301.lean:177`).

3. **Inductive step** for `t = mk children`. Goal:
   `M.inverse.elementaryWeight (mk children) = M'.inverse.elementaryWeight (mk children)`.

   The cycle 366/367/368 closed forms suggest the cleanest path:
   - Unfold via `elementaryWeight` + `derivativeWeight` definitions, OR
   - Note `Φ_{⟦M⟧⁻¹}(t) = M.inverse.elementaryWeight t` (cycle 239 `_mk`),
     so the goal coincides with cycle 358's
     `elementaryWeightQ_phi_inv_mk` representative formula:
     ```
     M.inverse.elementaryWeight t = −∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t
     ```
     and analogously for `M'`.

   **Substantive step**: show that the RHS depends only on
   `M.elementaryWeight u` for `u.order ≤ t.order`. This factors as:
   (a) reduce `M.derivativeWeightWithSrc M.inverse i t` to a polynomial in
       `M.inverse.elementaryWeight (children)` plus `M.A i j` row-sums;
   (b) `M.inverse.elementaryWeight c` for `c ∈ children` is bridged by the
       **inductive hypothesis** (since `c.order < t.order`);
   (c) the `M.A i j` row-sums and `M.b i` weights are encoded inside
       `M.elementaryWeight` at appropriate trees (e.g.
       `M.elementaryWeight (mk children) = ∑ᵢ M.b i · ∏_c M.derivativeWeight i c`).

   **Key realization**: the cycle 366/367/368 closed forms ARE this
   per-tree polynomial expression. So the inductive step at `t = mk children`
   essentially says:
   `M.inverse.elementaryWeight (mk children) = P(M.elementaryWeight at subtrees)`
   where `P` is some polynomial. By the IH applied to each child and
   `h` applied at `t` itself, both `M` and `M'` evaluate `P` at the same
   arguments, so they coincide.

4. **Concrete inductive step pattern** (per the cycle 368 `broom₃` recipe
   generalized):

```lean
intro t IH
induction t with
| mk children =>
  -- IH : ∀ s, s.order < (mk children).order → ... → ... = ...
  -- (This won't work directly because RootedTree's recursor isn't
  --  structural-on-order. Use the WellFoundedRelation approach instead.)
  sorry
```

The **`induction t` won't fire structurally** because `RootedTree` has
a list-of-RootedTree constructor, NOT a structural induction on order.
Use `(measure RootedTree.order).wf.induction t` explicitly, OR cycle 343's
explicit `WellFoundedRelation`.

5. **Cycle 362's substitution lemma DOES NOT directly apply**:
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` substitutes
   the *source* tableau (M₁) while keeping the *inner* tableau (M₂)
   fixed. Our induction varies BOTH (M and M' have different inner
   tableaux). So cycle 362 is a corollary at best, not the bridge.

   The clean way: at each step, expand `M.derivativeWeightWithSrc M.inverse
   i t` recursively via the `derivativeWeightWithSrcProd` cons-case. Each
   layer of recursion produces:
   - `M.inverse.elementaryWeight child` (apply IH since `child.order < t.order`).
   - `M.A i j · (recursive call at next child)`.

   The `M.A i j` weights appear via `M.derivativeWeight i child` and
   `M.elementaryWeight (... involving child ...)`. Both can be bridged
   through `h` at appropriate subtrees.

### LOC budget for P1

~120–180 LOC. Composed of:
- Representative-level lemma statement (~10 LOC).
- Strong-induction setup via `WellFoundedRelation` (~15 LOC).
- Inductive step: tree unfold + IH application + closed-form computation
  (~70–120 LOC, mirroring the cycle 368 broom₃ recipe structure).
- Quotient-level wrapper via `Quotient.inductionOn₂` (~15 LOC).
- One non-vacuity `example` (~15 LOC).

### Time-box for P1

**60 minutes** of focused effort. If after that the inductive step's
algebraic identity hasn't compiled cleanly, **pivot to P2** without
attempting further. Do NOT leave a sorry behind — either ship cleanly
or pivot. **Streak preservation is the dominant constraint.**

### Risk assessment for P1

**HIGH**. The inductive step needs to expose
`M.inverse.elementaryWeight t` as a polynomial in subtree elementary
weights via a uniform algebraic argument. The cycle 367/368 closed
forms were tree-specific algebraic identities; abstracting them into a
single inductive proof requires either:
(a) An auxiliary `derivativeWeightWithSrc_inverse_eq_polynomial` lemma
    capturing the per-tree expansion uniformly, OR
(b) A clever induction whose IH consumes "subtree elementary weights
    agree" directly.

If (a) doesn't shape up in ~30 min, the proof is multi-cycle. **Pivot
fast.**

## Priority 2 — Option B fallback: `mk [cherry]` closed form

If P1 stalls within the time-box, ship the fourth tree-witness:

### Target deliverables

1. `elementaryWeightQ_phi_inv_mkCherry` — closed form for
   `Φ_{η⁻¹}(mk [cherry])` where `mk [cherry]` is the order-3 tree with
   a single child that is itself `cherry`.

2. `powRep_sum_eq_of_agreement_at_mkCherry_zero` — m=0 corollary.

3. Two non-vacuity `example`s on `explicitEuler` (closed-form witness +
   reflexive m=0 witness).

### Derivation of the `mk [cherry]` closed form

`mk [cherry] = mk [mk [vertex]]` is order-3 (root + cherry-child of 2
vertices). Per cycle 358's `_inv_mk`:
```
Φ_{⟦M⟧⁻¹}(mk [cherry]) = −∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i (mk [cherry])
```

Two-layer unfold of `derivativeWeightWithSrcProd M.inverse i [cherry]`:
- Outer (cons-case at `cherry :: []`): yields
  `M.inverse.elementaryWeight cherry + ∑ⱼ M.A i j · M.derivativeWeightWithSrc M.inverse j cherry`
  multiplied by `derivativeWeightWithSrcProd M.inverse i [] = 1`.
- Inner (`derivativeWeightWithSrc M.inverse j cherry`): from cycle 367
  `h_dws_cherry`: `M.inverse.elementaryWeight vertex + ∑ₖ M.A j k`.

Substitute cycle 367 results:
- `M.inverse.elementaryWeight vertex = −M.elementaryWeight vertex` (cycle 367 `h_inv_v`, equivalently cycle 341 P2 at representative level).
- `M.inverse.elementaryWeight cherry = (M.elementaryWeight vertex)² − M.elementaryWeight cherry` (cycle 367 main theorem at representative level via cycle 239 `_mk`).

Let `v := M.elementaryWeight vertex`, `c := M.elementaryWeight cherry`,
`w := M.elementaryWeight (mk [cherry])`, `Aᵢ := ∑ⱼ M.A i j`.

Paper derivation (DO THIS IN SCRATCH BEFORE CODING):

```
M.derivativeWeightWithSrc M.inverse i (mk [cherry])
  = (v² − c) + ∑ⱼ M.A i j · (−v + Aⱼ)
  = v² − c − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ

−Φ_{η⁻¹}(mk [cherry]) = ∑ᵢ M.b i · (v² − c − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ)
                      = v² · v − c · v − v · c + w
                                              [using v = ∑ⱼ M.b j, c = ∑ᵢ M.b i · Aᵢ, w = ∑ᵢ M.b i · ∑ⱼ M.A i j · Aⱼ]
                      = v³ − 2vc + w

Φ_{η⁻¹}(mk [cherry]) = −v³ + 2vc − w
```

**Claimed closed form**:
```
Φ_{η_q⁻¹}(mk [cherry]) = −(Φ_η(τ))³ + 2·Φ_η(τ)·Φ_η(cherry) − Φ_η(mk [cherry])
```

**Note**: this is **structurally identical** to cycle 368's broom₃
closed form (both order-3, both involve v³, vc, and Φ_η(t) itself).
This is mildly surprising but consistent with the Connes-Kreimer Hopf
algebra structure: `broom₃` and `mk [cherry]` are different rooted
trees but have isomorphic skeletons modulo orientation, so their
inverse-coproduct contributions coincide. **Verify the paper
derivation independently before coding.** If the derivation differs
from the claim above, ship whatever the correct closed form is.

### Recipe for P2 (mirrors cycle 368 broom₃ recipe verbatim)

1. Reuse cycle 367 helpers `h_inv_v`, `h_vertex`, `h_dws_cherry`,
   `h_cherry`. Add cycle 367 `elementaryWeightQ_phi_inv_cherry` for
   the inner-cherry expansion as `h_inv_cherry`.
2. Add new helpers:
   - `h_dws_mkCherry i :
     M.derivativeWeightWithSrc M.inverse i (mk [cherry])
       = (v² − c) + ∑ⱼ M.A i j · (Aⱼ − v)`
     via two-layer `derivativeWeightWithSrcProd` unfold + cycle 367
     `_inv_cherry` substitution + `derivativeWeightWithSrcProd []`
     base case.
   - `h_mkCherry : M.elementaryWeight (mk [cherry])
       = ∑ᵢ M.b i · ∑ⱼ M.A i j · Aⱼ` via direct elementaryWeight unfold
     (one layer of `derivativeWeightProd`).
3. Per-summand `ring` expansion of `(v² − c) − v · Aᵢ + ∑ⱼ M.A i j · Aⱼ`,
   sum-distribute via `Finset.sum_add_distrib` /
   `Finset.sum_sub_distrib` + `← Finset.mul_sum`, back-substitute via
   `← h_mkCherry, ← h_cherry, ← h_vertex`, then `ring`.

### LOC budget for P2

~200–250 LOC including helpers, docstrings, and non-vacuity examples
(slightly longer than cycle 368's broom₃ ship at ~220 LOC because of
one additional inner-cherry layer).

### Time budget for P2

90 minutes maximum. The recipe is mechanical (cycle 368 template); if
it takes longer something is wrong with the paper derivation.

## What NOT to attempt this cycle

1. **Do NOT attempt the original Sub-lemma A general body**
   (`powRep_sum_eq_of_strict_subtree_agreement`, line 2272). Cycle 365
   established the heterogeneous-`powRep`-stage obstacle; cycle 366
   documented it as multi-cycle. The m=0 specialization (P1 above)
   sidesteps this by avoiding `powRep` entirely. **Do NOT touch the
   line 2272 sorry** — it is grandfathered and should remain.

2. **Do NOT attempt general-m closed forms** (cycle 367 §C.2 stretch
   target: `powRep_inv_cherry_closed_form` at all `m`). This requires
   a `Φ_{η₁·η₂}(cherry)` decomposition lemma that is itself
   multi-cycle.

3. **Do NOT pursue order-4 trees this cycle**. The four trees of order
   ≤ 3 are: `vertex` (order 1), `cherry` (order 2), `broom₃` (order 3),
   `mk [cherry]` (order 3). Order-4 (e.g. `bushy = mk [vertex, vertex,
   vertex]`, `mk [vertex, cherry]`) is deferred to cycle 370+.

4. **Do NOT modify `scripts/autonomous_loop.py`** — supervisor /
   prompt-builder issues are loop-maintainer territory per
   `.prover-state/issues/tautology_scanner_false_positives.md`.

5. **Do NOT attempt to compile `Section441.lean`**. 43+ consecutive
   GPFS timeouts per `cycle_182_gpfs_slowness.md`. Skip.

6. **Do NOT pivot to a fresh entity outside §422** this cycle. The
   §422 streak is at 34 cycles and the witness ladder is making
   concrete progress. Pivoting now (e.g. to `def:451A`,
   `thm:535A`) interrupts that momentum. If P1 and P2 both fail
   (which would be surprising), file an issue and pivot in cycle 370.

## Failed approaches recorded in attempts.md (DO NOT repeat)

From cycles 365/366 task results, the following approaches to
Sub-lemma A's general body DO NOT WORK and should not be retried:

- **Cycle 365 Sub-approach 4.a** (strong induction on `t.order` + cycle
  362 substitution): cycle 362 substitutes only the source tableau M₁,
  keeping inner tableau M₂ fixed; LHS/RHS of Sub-lemma A differ
  precisely in the inner tableau, so the substitution cannot fire
  cross-side.
- **Cycle 365 Sub-approach 4.b** (induction on m at quotient level):
  base case m=0 after `Quotient.inductionOn₂` + cycle 358 `_inv_mk`
  expansion yields heterogeneous sums over Fin s vs Fin s' with
  differing b-coefficients and inner-tableau arguments — same obstacle.
- **Cycle 366 cross-cancellation** via `η^(m+1) · η^(-(m+1)) = 1`:
  positive-power parametricity is itself open with the same
  heterogeneity.

P1's m=0 specialization works around this by avoiding `powRep` entirely
— at m=0, `η^(-1) = η⁻¹` expands per-representative without producing
the heterogeneous-stage sums. **The representative-level inductive
lemma `inverse_elementaryWeight_eq_of_closed_subtree_agreement` is
genuinely a new approach not yet attempted.**

## Verification protocol

After each ship:
1. `lake env lean OpenMath/Chapter4/Section422.lean` — must exit 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must remain 5
   (4 docstring references + 1 grandfathered Sub-lemma A body).
3. `#print axioms` on each new public theorem — must return
   `[propext, Classical.choice, Quot.sound]` only (NO `sorryAx`).
4. **Streak preservation**: §422 axiom-clean streak 34 → 35 if either
   P1 or P2 closes; 34 → 33 (BROKEN) if either ships with a sorry or
   fails to compile.

## Faithfulness checklist

For each new theorem:
- **Tautology check**: closed forms must not be trivially provable
  (cycle 367 `elementaryWeightQ_phi_inv_cherry` is a real 3-variable
  polynomial identity, not a tautology).
- **Definition smuggling check**: the polynomial closed forms (or the
  P1 inductive statement) are *consequences* of cycle 358 `_inv_mk`'s
  representative formula plus the recursive structure of
  `derivativeWeightWithSrcProd` — they are theorems about the
  structure, not definitions of new named concepts. No
  `lean_status.json` entries are claimed.
- **Hypothesis strength check** for P1: `h_closed : ∀ s, s.order ≤
  t.order → ...` is the closed-subtree (not strict-subtree) form per
  cycle 365's choice. Confirmed correct per cycle 365 task results.
- **Identity check** for P2: the closed form's RHS is a non-trivial
  degree-3 polynomial in three variables; `exact` against any of the
  cycle 358/362/366/367/368 helpers is impossible. No tautology risk.

## Cycle 370+ outlook (after cycle 369)

- **If P1 closes cleanly**: cycle 370+ can extend to **general `m`** via
  a separate `powRep`-aware argument layered on the m=0 result, OR
  attempt Phase D.3.d (`underlyingOneStepMethod_aux` recursion) using
  the m=0 result as the inductive base. Big win: m=0 closure of
  Sub-lemma A is sufficient for many `Eq422a` consumers.
- **If P2 closes**: cycle 370 candidate is `bushy = mk [vertex, vertex,
  vertex]` (the order-4 even-fan tree, parallel to broom₃ at one level
  higher), OR `mk [broom₃]` (depth-2 broom). Both validate the
  Route B closed-form pattern further. After 5 trees, the inductive
  formulation should be much clearer.
- **Sub-lemma A general body** (line 2272) remains grandfathered until
  either a multi-cycle Route A infrastructure pass closes it, OR
  Phase D.3.d is shown to require only the m=0 specialization (in
  which case the general body can be retired and the sorry removed).

## Reference cross-links

- Cycle 368 closed form template (broom₃):
  `OpenMath/Chapter4/Section422.lean:2538–2693` (theorem) and
  `2695–2750` (m=0 corollary).
- Cycle 367 cherry template (for P2's reuse):
  `OpenMath/Chapter4/Section422.lean:2376–2476` (theorem).
- Cycle 358 representative-level `_inv_mk`:
  `OpenMath/Chapter4/Section422.lean:582` (signature).
- Cycle 362 source-tableau substitution lemma:
  `OpenMath/Chapter3/Section381.lean:2803+`
  (`derivativeWeightWithSrc_eq_of_strict_subtree_agreement`).
- Cycle 343 `WellFoundedRelation RootedTree`:
  `OpenMath/Chapter3/Section301.lean:177`.
- Sub-lemma A grandfathered sorry: line 2272 of Section422.lean.
- Cycle 366 task results: rationale for Priority 2 graceful degradation
  pattern (this cycle's P2 fallback).
- `def_422B_phase_D_3_scoping.md` §A.0.2 — pinned `D` operator decision
  (NOT affected by this cycle's work).

## Bottom line

**Primary ship**: P1 Option A — representative-level inductive
inverse-elementaryWeight parametricity at m=0 (~120–180 LOC,
time-boxed 60 min, axiom-clean target).

**Fallback ship**: P2 Option B — `mk [cherry]` closed form + m=0
witness (~200–250 LOC, mechanical port of cycle 368 broom₃ recipe).

Either deliverable preserves the §422 streak at 35 consecutive
axiom-clean cycles. **Do NOT ship both** — focus discipline matters;
the cycle 369 worker picks one and executes cleanly. If P1 closes
under time-box and there's time remaining, document the result in
`def_422B_phase_D_3_scoping.md` cycle 369 update. Otherwise commit to
P2 and pivot without remorse.

**Risk note**: P1 is HIGH risk; if 30 min in there's no clear inductive
shape, pivot to P2 immediately. The cycle 366 cherry-witness ship cost
~40 min in retrospect; cycle 368 broom₃ cost ~60 min. P2's `mk [cherry]`
is mechanically similar to broom₃ — budget similarly. Picking P2
upfront is a perfectly acceptable strategic choice if the worker has
any doubt about P1's tractability; the witness ladder remains useful
infrastructure for cycle 370+.
