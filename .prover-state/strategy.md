# Cycle 370 Strategy — §422 Phase D.3.b Step 2: `bushy` (order-4 broom) closed form

## TL;DR

Ship the order-4 broom `bushy = mk [vertex, vertex, vertex]` closed form for
`Φ_{η_q⁻¹}(bushy)` plus its m=0 corollary. **This is Option B from the cycle
369 task results' "Suggested next approach"**, chosen because it (1) tests
the cycle 368 Discovery hypothesis `(Aᵢ − v)^k` for broom-of-k, (2) is
mechanical extension of cycle 368's broom₃ recipe (one extra child), (3) is
single-cycle and low-risk, (4) maintains the 35-cycle axiom-clean streak.

## §A — Priority 0: no Aristotle results to incorporate

The task results report no Aristotle submissions are in flight. Skip
Aristotle work this cycle.

## §B — Target deliverables

### B.1 — Primary: `elementaryWeightQ_phi_inv_bushy` (closed form)

**Statement** (derived in §B.2 below, NOT trusted to a hypothesis):

```lean
theorem elementaryWeightQ_phi_inv_bushy
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ bushy =
      (elementaryWeightQ_phi η_q vertex)^4
        − 3 · (elementaryWeightQ_phi η_q vertex)^2 · elementaryWeightQ_phi η_q cherry
        + 3 · elementaryWeightQ_phi η_q vertex · elementaryWeightQ_phi η_q broom₃
        − elementaryWeightQ_phi η_q bushy
```

The worker MUST verify this closed form on paper (§B.2) before any Lean
coding, and MUST cross-check on `explicitEuler` (§B.3) before opening
the Lean editor.

### B.2 — Paper derivation (MANDATORY before any Lean coding)

`bushy = mk [vertex, vertex, vertex]`. The
`derivativeWeightWithSrcProd` recursion at `[vertex, vertex, vertex]` is
a 3-layer cons-case unfold. At each leaf (vertex),
`derivativeWeightWithSrc M.inverse j vertex = 1` (cycle 366
`derivativeWeightWithSrc_vertex`).

Using cycle 368's per-leaf factor
`M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j · 1 = -v + Aᵢ`
where `v := M.elementaryWeight vertex`, `Aᵢ := ∑ⱼ M.A i j`:

```
M.derivativeWeightWithSrc M.inverse i bushy = (-v + Aᵢ)^3 = (Aᵢ − v)^3

Φ_{⟦M⟧⁻¹}(bushy) = −∑ᵢ M.b i · (Aᵢ − v)^3
```

Expand `(Aᵢ − v)^3 = Aᵢ^3 − 3·Aᵢ^2·v + 3·Aᵢ·v^2 − v^3`:

```
Φ_{⟦M⟧⁻¹}(bushy)
  = −∑ᵢ M.b i · (Aᵢ^3 − 3·Aᵢ^2·v + 3·Aᵢ·v^2 − v^3)
  = −∑ᵢ M.b i · Aᵢ^3 + 3v · ∑ᵢ M.b i · Aᵢ^2 − 3v^2 · ∑ᵢ M.b i · Aᵢ + v^3 · ∑ᵢ M.b i
```

Identify each sum against elementary-weight closed forms:
- `∑ᵢ M.b i · Aᵢ^3 = M.elementaryWeight bushy` (via §312
  `elementaryWeight_eq + derivativeWeight_mk` recursion at
  `bushy = mk [vertex, vertex, vertex]`).
- `∑ᵢ M.b i · Aᵢ^2 = M.elementaryWeight broom₃` (cycle 368 internal
  derivation — verify in cycle 368's proof body to confirm this naming
  matches `RootedTree.broom₃ = mk [vertex, vertex]`).
- `∑ᵢ M.b i · Aᵢ = M.elementaryWeight cherry` (cycle 367 closed form,
  noting `cherry = mk [vertex]`).
- `∑ᵢ M.b i = M.elementaryWeight vertex` (definitional: `vertex = mk []`).

So:
```
Φ_{⟦M⟧⁻¹}(bushy) = −w + 3v·b − 3v²·c + v³·v
                  = v^4 − 3v²·c + 3v·b − w
```
where `v := Φ_η(vertex)`, `c := Φ_η(cherry)`, `b := Φ_η(broom₃)`,
`w := Φ_η(bushy)`.

### B.3 — Sanity check on `explicitEuler`

`explicitEuler : RKTableau 1` has `s = 1`, `b = ![1]`, `A = !![0]`.
So `Aᵢ = ∑ⱼ M.A i j = 0` for the unique stage `i = 0`.

- `v = Φ_M(vertex) = ∑ᵢ M.b i = 1`.
- `c = Φ_M(cherry) = ∑ᵢ M.b i · Aᵢ = 1 · 0 = 0`.
- `b = Φ_M(broom₃) = ∑ᵢ M.b i · Aᵢ^2 = 1 · 0 = 0`.
- `w = Φ_M(bushy) = ∑ᵢ M.b i · Aᵢ^3 = 1 · 0 = 0`.
- RHS = `1^4 − 3·1^2·0 + 3·1·0 − 0 = 1`.

Direct LHS via cycle 358 `_inv_mk`:
```
Φ_{⟦explicitEuler⟧⁻¹}(bushy) = −∑ᵢ M.b i · (Aᵢ − v)^3
                              = −1 · (0 − 1)^3 = −(−1) = 1 ✓
```

**If the worker's `explicitEuler` calculation disagrees with this, STOP
and re-derive on paper.** Do not proceed to Lean until the closed form
is paper-verified.

### B.4 — Lean ship recipe

Mirror cycle 368's broom₃ recipe in `Section422.lean` with these changes:

1. **`RootedTree.bushy` availability**: plan.md §"Cycle 269 update" of the
   `RootedTree`-aliases section confirms `bushy := mk [vertex, vertex,
   vertex]` was introduced as a `Section310` alias. Use it directly via
   `RootedTree.bushy` qualification. Mathlib's `_root_.RootedTree`
   namespace (per cycle 369 Discovery) has no `bushy` member, so no
   collision is expected. **If compile fails on namespace resolution**,
   use the fully-qualified `OpenMath.Chapter3.Section310.RootedTree.bushy`
   form.

2. **Helper lemmas** (in the `Quotient.inductionOn` body, modeled after
   cycle 368 §C.4):
   - `h_inv_v : M.inverse.elementaryWeight vertex = −M.elementaryWeight vertex`
     (cycle 341 P2, reuse verbatim from cycle 367/368).
   - `h_vertex : M.elementaryWeight vertex = ∑ᵢ M.b i` (reuse cycle 367/368
     verbatim — definitional after `elementaryWeight_eq + derivativeWeight_mk
     + Fin.sum_univ_zero`).
   - `h_cherry : M.elementaryWeight cherry = ∑ᵢ M.b i · ∑ⱼ M.A i j`
     (reuse cycle 367/368 verbatim).
   - `h_broom₃ : M.elementaryWeight broom₃ = ∑ᵢ M.b i · (∑ⱼ M.A i j)^2`.
     **WORKER: inspect cycle 368's `elementaryWeightQ_phi_inv_broom₃` proof
     body to locate this derivation.** It will be either an inline `have`
     or a private helper. Reuse if accessible; otherwise re-derive inline
     via `elementaryWeight_eq + derivativeWeight_mk + h_dw_cherry`-style
     two-layer unfold (note `broom₃ = mk [vertex, vertex]`, so
     `derivativeWeightProd` at `[vertex, vertex]` reduces to
     `(∑ⱼ M.A i j) · (∑ₖ M.A i k)` per the per-leaf product structure).
   - `h_bushy : M.elementaryWeight bushy = ∑ᵢ M.b i · (∑ⱼ M.A i j)^3` (NEW,
     three-layer unfold analogous to `h_broom₃` extended by one child).
   - `h_dws_bushy i : M.derivativeWeightWithSrc M.inverse i bushy =
     (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^3`. **The key 3-fold
     cons-case unfold via `derivativeWeightWithSrcProd`**. Three-step:
     outer cons-case at `vertex :: [vertex, vertex]` yields per-leaf factor
     `(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j · 1)` times the
     `derivativeWeightWithSrcProd` at `[vertex, vertex]`. The latter
     unfolds similarly to yield the same factor squared. Combined: the
     factor cubed.

3. **Main `h_sum` block**: expand `(M.inverse.elementaryWeight vertex + Aᵢ)^3`
   via `h_inv_v` (which gives `(-v + Aᵢ)^3`) and `ring`. Then
   sum-distribute via `Finset.sum_add_distrib + Finset.sum_sub_distrib`,
   then `← Finset.mul_sum` (three applications: one each for the
   `v^3`, `3v^2`, `3v` constants), then back-substitute via
   `← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex`, then final `ring`.

   Structurally identical to cycle 368's `h_sum` block — broom₃ had 2
   extractable constants for `(Aᵢ − v)^2` expansion; bushy has 3 for
   `(Aᵢ − v)^3`.

4. **m=0 corollary** `powRep_sum_eq_of_agreement_at_bushy_zero`: 3-line
   `rw` chain mirroring cycle 368's broom₃ corollary (the line near the
   end of the broom₃ ship). Takes FOUR agreement hypotheses (vertex,
   cherry, broom₃, bushy) matching the closed form's four factors.

5. **Two `example` non-vacuity witnesses** on `explicitEuler`:
   - Closed-form witness: `Φ_{⟦explicitEuler⟧⁻¹}(bushy) = 1` (per paper
     verification in §B.3). Proof: `rw [elementaryWeightQ_phi_inv_bushy]`
     then `simp [explicitEuler]` then `norm_num`.
   - Reflexive m=0 witness with `η_q = η_q' = ⟦explicitEuler⟧`, agreement
     hypotheses discharged by `rfl, rfl, rfl, rfl`.

### B.5 — Estimated LOC delta

Per cycle 368 precedent (broom₃ shipped at ~219 LOC delta), bushy should
add ~250 LOC (one extra constant-extraction layer + the new `h_broom₃`
helper if not reusable + new `h_bushy` helper + one extra
back-substitution rewrite). Section422.lean: 3063 → ~3300 LOC.

## §C — Risk assessment

### R1 — `h_broom₃` availability (LOW–MEDIUM)

Cycle 368's `Section422.lean` shipped `elementaryWeightQ_phi_inv_broom₃`
which **internally** derived `M.elementaryWeight broom₃ = ∑ᵢ M.b i · Aᵢ^2`.
**Worker must read cycle 368's proof body** to determine whether this is
in a reusable form (a `have` block extractable by `extract_have` style)
or needs inline re-derivation. **If reusable**, hoist to a top-level
`private theorem` first, then reference in this cycle's bushy proof. **If
not reusable** (e.g. uses tightly-bound locals), re-derive inline —
mechanical 2-layer `Finset.sum_congr` over `[vertex, vertex]` via
`derivativeWeightProd`.

### R2 — `Aᵢ` notation (LOW)

Cycle 367/368 used `∑ⱼ M.A i j` directly throughout (no `let Aᵢ := ...`
binding). Continue this convention. Do NOT introduce a `let` for `Aᵢ` —
Lean's `ring` tactic handles the nested `∑` notation without naming.

### R3 — `(Aᵢ − v)^3` expansion (LOW)

`ring` should handle the cubic expansion directly. If it stalls (unlikely
at this size), fall back to manual `pow_succ × 3 + mul_add + sub_mul`
chain. Cycle 368 closed `(Aᵢ − v)^2` via `ring` in a single step; cubic
case is structurally the same.

### R4 — `RootedTree.bushy` namespace collision (LOW)

Per cycle 369 Discovery, Mathlib's `_root_.RootedTree.mk` collides with
our `OpenMath.Chapter3.Section310.RootedTree.mk`. But `RootedTree.bushy`
is a constructor-less member of our namespace (cycle 269), and Mathlib's
`RootedTree` namespace has no `bushy` member. So `RootedTree.bushy`
should resolve correctly. **If compile fails**, use
`OpenMath.Chapter3.Section310.RootedTree.bushy` explicitly.

### R5 — `h_dws_bushy` three-layer unfold (LOW–MEDIUM)

The 3-fold cons-case unfold of `derivativeWeightWithSrcProd` at
`[vertex, vertex, vertex]` requires three sequential `show ... from
derivativeWeightWithSrcProd_cons` rewrites (or equivalent). Cycle 368's
broom₃ proof showed how 2-fold cons-case works; the 3-fold case is
structurally identical with one extra wrap. **If the unfold pattern is
unclear**, read cycle 368's `h_dws_broom₃` derivation and add one extra
layer.

## §D — What NOT to attempt this cycle

1. **Do NOT retry Sub-lemma A's general inductive body** (the m=0 case
   from cycle 365). Cycle 365/366/367/368/369 all deferred this; the
   grandfathered sorry remains untouched. This is multi-cycle Phase
   D.3.c work for later.

2. **Do NOT extend to `mk [broom₃]` or `mk [vertex, cherry]`** this cycle.
   These are also order-4 trees and natural cycle 371+ targets. Pick ONE
   order-4 tree per cycle to maintain single-cycle discipline and
   preserve the axiom-clean streak.

3. **Do NOT attempt Phase D.3.c** (`underlyingOneStepMethod_aux`). This
   is the downstream consumer of the witness ladder, but requires
   multi-cycle scoping. The cycle 369 task results suggest considering
   it, but only AFTER the witness library is more mature. Five+ data
   points is the minimum justified for re-attempting Sub-lemma A's
   general body; even then a separate planning cycle should re-scope.

4. **Do NOT introduce new `axiom` or `constant` declarations**.

5. **Do NOT raise `maxHeartbeats` above 200000**. If the `ring` step on
   `(Aᵢ − v)^3` expansion stalls, decompose into named intermediate
   helpers (see R3 fallback).

6. **Do NOT submit to Aristotle this cycle**. The proof is mechanical
   extension of cycle 368's recipe; Aristotle adds latency without value.

7. **Do NOT compile or modify `OpenMath/Chapter4/Section441.lean`**. The
   43rd consecutive GPFS timeout is documented per
   `.prover-state/issues/cycle_182_gpfs_slowness.md` — skip §441 entirely.

8. **Do NOT use `RootedTree.mk [RootedTree.vertex, RootedTree.vertex,
   RootedTree.vertex]` as the literal for `bushy`**. Use the existing
   `RootedTree.bushy` alias (cycle 269) to avoid the Mathlib namespace
   collision per cycle 369 Discovery.

## §E — Acceptance criteria

Cycle 370 ships successfully when ALL of the following hold:

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5 (4
   docstring references + 1 grandfathered Sub-lemma A body sorry).
   **Code-level sorry count = 1, unchanged from HEAD.**
3. `#print axioms elementaryWeightQ_phi_inv_bushy` returns
   `[propext, Classical.choice, Quot.sound]` (axiom-clean).
4. `#print axioms powRep_sum_eq_of_agreement_at_bushy_zero` returns
   `[propext, Classical.choice, Quot.sound]` (axiom-clean).
5. Two non-vacuity `example`s on `explicitEuler` compile.
6. Updated `.prover-state/issues/def_422B_phase_D_3_scoping.md` with a
   "Cycle 370 update" subsection documenting:
   - The bushy closed-form theorem statement.
   - Update to the §422 streak counter (35 → **36** consecutive
     axiom-clean cycles for 336–370).
   - Confirmation/refinement of cycle 368's `(Aᵢ − v)^k` Discovery
     hypothesis based on the bushy paper derivation. (Specifically: the
     binomial expansion produces a polynomial in
     `Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃), Φ_η(bushy)`, validating
     the Discovery as a per-row identity that lifts to a 4-term
     elementary-weight closed form for broom-of-3.)

## §F — Suggested cycle 371+ horizon

After cycle 370 ships, the worker's task results should suggest:

1. **`mk [broom₃]`** (vertical extension of broom₃, depth-2 ladder) —
   tests cycle 369's depth-extension pattern beyond cherry.
2. **`mk [vertex, cherry]`** (first asymmetric order-4 tree) — exercises
   a genuinely NEW closed-form structure (mixed-child).
3. After 6–7 clean witnesses, re-attempt Sub-lemma A's general inductive
   body with a fresh multi-cycle scoping document.

## §G — Cycle 370 worker entry point checklist

1. Read this strategy fully.
2. Read cycle 368's `elementaryWeightQ_phi_inv_broom₃` ship in
   `OpenMath/Chapter4/Section422.lean` (the broom₃ block; locate via
   grep for `elementaryWeightQ_phi_inv_broom₃`) as the primary recipe
   template.
3. **Paper-derive `Φ_{η⁻¹}(bushy)` closed form per §B.2** before opening
   Lean. Cross-check on `explicitEuler` per §B.3.
4. Confirm `RootedTree.bushy` is in the namespace (grep
   `OpenMath/Chapter3/Section310.lean`).
5. Inspect cycle 368's internal `h_broom₃`-style derivation — decide
   whether to hoist to a public/private helper or re-derive inline.
6. Write `elementaryWeightQ_phi_inv_bushy` per §B.4 recipe.
7. Write `powRep_sum_eq_of_agreement_at_bushy_zero` m=0 corollary.
8. Write two non-vacuity `example`s on `explicitEuler`.
9. Verify via `lake env lean` and `#print axioms`.
10. Update `def_422B_phase_D_3_scoping.md` per §E.6.
11. Write `.prover-state/task_results/cycle_370.md` documenting the ship.
12. Commit and push per CLAUDE.md.
