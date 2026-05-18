# Cycle 386 Strategy — §422 Phase α'.4.0: 10th Family C witness

## TL;DR

Ship the **10th Family C witness** `elementaryWeightQ_phi_inv_mkBroomCherry`
in `OpenMath/Chapter4/Section422.lean` — the closed form for
`Φ_{η_q⁻¹}(mk [broom₃, cherry])` (order 6, σ = 1, **asymmetric**
two-non-leaf-children), plus the m=0 Sub-lemma A corollary. Cycle 386 is
the Phase α'.4.0 entry point per the cycle 385 scoping doc §7
(`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`).

**LOC budget**: ~250 LOC. **Streak**: 48 substantive + 2 doc cycles
(336–385). Ship axiom-clean, 0 new sorries, preserve streak.

## Context

* **No pending Aristotle results.** Do NOT submit to Aristotle this
  cycle — the closed-form-witness proofs are pure manual closures of
  the cycle 384 template; Aristotle has historically struggled with
  the per-summand `ring` distribution + `← Finset.mul_sum` factoring
  this proof requires.
* **Single grandfathered sorry** at `Section422.lean:2279`
  (`powRep_sum_eq_of_strict_subtree_agreement` general body, cycle 365).
  Closure path: Phase α'.4 (cycles 386–388) + Phase β/γ extension.
  Do NOT attempt to close this sorry — it is multi-cycle ahead.
* **Cycle 385** shipped the Family C scoping doc (621 lines,
  markdown-only). Cycle 386 executes its §7 entry point.

## Priority 1 — DELIVERABLE: `elementaryWeightQ_phi_inv_mkBroomCherry`

### Target tree

`mk [broom₃, cherry]` — asymmetric two-non-leaf-children, order 6, σ = 1.

* `broom₃ = mk [vertex, vertex]` (order 3, σ = 2)
* `cherry = mk [vertex]` (order 2, σ = 1)
* Parent order: `3 + 2 + 1 = 6`.
* σ(parent): children are distinct (`broom₃ ≠ cherry`), so σ = 1.

### Mandatory step: paper-derive the closed form BEFORE writing Lean

**Do not skip this step.** Cycle 384's surprise (`Φ_η(mk [vertex, cherry])`
surfacing in the bilinear block) was unanticipated; cycle 386 has
analogous risk. Spend 30–60 min on paper-derivation first.

Approach: apply cycle 358's `elementaryWeightQ_phi_inv_mk` formula:

```
Φ_{η_q⁻¹}(mk [broom₃, cherry])
  = − Σⱼ b_j · (M.inverse.elementaryWeight broom₃ + Σₖ A_jk · F_broom₃(k))
         · (M.inverse.elementaryWeight cherry + Σₖ A_jk · F_cherry(k))
```

where:
* `F_broom₃(k) = M.inverse.derivativeWeight k broom₃` — unfolds via
  cycle 368's `h_dws_broom₃`.
* `F_cherry(k) = M.inverse.derivativeWeight k cherry` — unfolds via
  cycle 367's `h_dws_cherry`.

Distribute the product into four blocks (per scoping doc §3.2):

* **Block (1)** const·const: `inv_broom₃ · inv_cherry · Σⱼ b_j`
  = `(−v³ + 2vc − b') · (v² − c) · v`.
* **Block (2)** const·A-sum: `inv_broom₃ · Σⱼ b_j · Σₖ A_jk · F_cherry(k)`
  = `inv_broom₃ · Φ_η(mk [cherry])` = `(−v³ + 2vc − b') · m`.
* **Block (3)** A-sum·const: `inv_cherry · Σⱼ b_j · Σₖ A_jk · F_broom₃(k)`
  = `inv_cherry · Φ_η(mk [broom₃])` = `(v² − c) · M_broom₃`.
  **NEW KERNEL** `M_broom₃ = Φ_η(mk [broom₃])`.
* **Block (4)** A-sum·A-sum: bilinear cross-term — surfaces a kernel
  combining the two child structures. Likely `Φ_η(mk [vertex, broom₃])`
  (the order-5 asymmetric tree from the scoping doc's discussion) and/or
  cycle 372's `Φ_η(mk [vertex, cherry])`. **Paper-derive this exactly
  before writing Lean.**
* **Self-term**: `−bc` where `bc = Φ_η(mk [broom₃, cherry])`.

Use `⟦explicitEuler⟧` (where every elementary weight equals 1) as a
cross-check: the closed form must evaluate to a specific rational
(predicted `1` by parity with cycles 371/372/384, but compute it).

### Lean proof recipe (cycle 384 template, asymmetric variant)

Cycle 384's proof body lives at `Section422.lean:4655–4961`. Mirror it
line-by-line with these changes:

1. `Quotient.inductionOn` on `η_q` → `⟨s, M⟩` (identical to 384).
2. Setup `let`-bindings for the elementary weights `v, c, b', m,
   M_broom₃, bc` and any new kernel from Block (4).
3. Reuse `h_inv_v`, `h_vertex`, `h_dws_cherry` (cycle 367), and
   introduce `h_dws_broom₃` (cycle 368-style) plus
   `h_inv_broom₃` (cycle 368's `elementaryWeightQ_phi_inv_broom₃`
   representative-lift, per cycle 369 pattern).
4. Expand `derivativeWeightWithSrc M.inverse i (mk [broom₃, cherry])`
   via the cons-case unfold (one outer `derivativeWeightProd_cons`,
   then per-child the cycle 368/367 `h_dws_*` unfolds).
5. Per-summand: distribute the bilinear product
   `(inv_broom₃ + S_broom₃(i)) · (inv_cherry + S_cherry(i))` via
   `Finset.sum_congr rfl (fun i _ => by ring)`. (`ring` does NOT
   distribute scalars over `Finset.sum` directly — see cycle 371
   Discovery memory entry.)
6. Sum distribution: `Finset.sum_add_distrib` / `Finset.sum_sub_distrib`
   to split into per-block sums.
7. `← Finset.mul_sum` × N to factor each constant out of its sum.
8. Back-substitute via `← h_<kernel>` for each named contribution
   (cycle 372 Discovery: consolidate shared constants where possible
   to avoid duplicate `← h_<...>` calls).
9. `ring` closes the final algebraic combination.

### Acceptance criteria for Priority 1

* New public theorem `elementaryWeightQ_phi_inv_mkBroomCherry`
  axiom-clean (`[propext, Classical.choice, Quot.sound]`).
* New m=0 corollary `powRep_sum_eq_of_agreement_at_mkBroomCherry_zero`
  axiom-clean. Agreement hypotheses: vertex, cherry, broom₃,
  mk [cherry], mk [broom₃], mk [broom₃, cherry], plus any new kernel
  surfaced by Block (4).
* Two non-vacuity `example`s on `⟦explicitEuler⟧`:
  - Closed-form witness pinning to a specific rational (compute it
    from the paper-derivation; do not guess).
  - m=0 reflexive witness via `rfl × N`.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` unchanged at 5
  (4 docstring + 1 grandfathered code sorry).
* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
* `#print axioms` on both new theorems returns
  `[propext, Classical.choice, Quot.sound]`.

## Priority 2 — STRETCH (only if Priority 1 ships clean with slack)

Ship `elementaryWeightQ_phi_inv_mkCherryBroom` for `mk [cherry, broom₃]`
(children in reversed order) — the R2 symmetry-pair confirmation per
scoping doc §6.2.

* LOC budget: ~100 LOC (proof mirrors Priority 1 with factor order
  swapped).
* The closed form should be **identical** modulo argument order in the
  `mk [...]` self-term, since `PhiEquivalent` quotients out child
  permutations at the §383 quotient level — but Lean's `RootedTree.mk`
  is `List`-based, not `Multiset`-based, so the two trees are NOT
  definitionally equal and need a separate witness.

**If Priority 1 takes the full cycle budget, skip Priority 2.** Better
to ship one clean witness than two rushed ones.

## Priority 3 — Bookkeeping (after Priority 1)

1. **`extraction/formalization_data/lean_status.json`** `def:422B` row:
   `cycle_completed_at` 385 → 386, status `partial`, append note:
   "Cycle 386 ships 10th Family C witness `Φ_{η_q⁻¹}(mk [broom₃, cherry])`
   (asymmetric two-non-leaf-children order-6, σ = 1) + m=0 Sub-lemma A
   corollary. Block (4) bilinear cross-term surfaces [new kernel name].
   Section422.lean ~6520 → ~6770 LOC. §422 streak: 49 substantive + 2
   doc (cycles 336–386)."
2. **`plan.md`** `def:422B` row: append cycle 386 note in the
   established compound-paragraph pattern.
3. **`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`**
   §5.1 / §6 — append a "Cycle 386 update" subsection documenting:
   - Exact closed form (the 10+ kernel polynomial with coefficients).
   - New kernels surfaced (Block (3) and Block (4) surprises).
   - Whether the predicted form matched empirical reality.
   - LOC delta.
   - Cycle 387 outlook implications (does Phase α'.4.1 recursive
     design have enough data points now?).

## What NOT to do this cycle

* **Do NOT skip the paper-derivation step.** Mandatory 30–60 min
  before any Lean. The cycle 384 surprise must not recur unflagged.

* **Do NOT attempt to ship `inversePolyTree` recursive definition this
  cycle** (Phase α'.4.1, scoped to cycle 387+). The scoping doc §5
  orders α'.4.0 (one more data point) before α'.4.1 (recursive ship).

* **Do NOT attempt to close the cycle 365 grandfathered sorry at
  `Section422.lean:2279`.** Multi-cycle ahead (α'.4 + β/γ).

* **Do NOT pivot to a fresh entity** (`def:451A`, `thm:535A`,
  `thm:541A`, `def:442A`). The §422 streak is productive; pivot
  opportunity is post-Phase α'.4.2 (cycle 389+).

* **Do NOT use `simp [recursive-def, name-eq-thm-*, ...]` patterns.**
  Cycle 382 memory entry `feedback_simp_recursive_def_overunfolds.md`:
  `simp` over-unfolds recursive defs before name theorems can fold
  back. Use targeted `rw [name-eq-thm-...]` then `simp [arithmetic]; ring`.

* **Do NOT submit to Aristotle.** Pure manual closure cycle.

* **Do NOT use `ring` to distribute scalars over `Finset.sum`** (cycle
  371 memory entry). Use `Finset.sum_congr rfl (fun i _ => by ring)`
  then `Finset.sum_add_distrib` / `Finset.sum_sub_distrib` to split.

* **Do NOT raise `maxHeartbeats` above 200000.** If the proof body
  stalls, decompose into named private helpers (e.g. extract Block (4)
  bilinear cross-term as a separate lemma).

* **Do NOT introduce `axiom` / `constant` declarations.**

* **Do NOT introduce sorries.** Cycle 386's deliverable bar is
  "ship axiom-clean or ship nothing" (cycle 200/201 rollback
  precedent).

* **Do NOT compile `OpenMath/Chapter4/Section441.lean`.** 43+ GPFS
  timeouts since cycle 182 per `cycle_182_gpfs_slowness.md`. Section441
  is unrelated to cycle 386's deliverable.

## Risk assessment

| Risk | Severity | Mitigation |
|---|---|---|
| Paper-derivation step skipped, Lean attempt stalls | HIGH | Mandatory 30–60 min paper-derivation BEFORE Lean. Cross-check against `⟦explicitEuler⟧` evaluation. |
| Block (4) bilinear cross-term unexpectedly complex | MEDIUM | Mirror cycle 384's `mk [cherry, cherry]` proof body (Section422.lean:4655–4961) line-by-line. |
| New kernel surfaced (`mk [vertex, broom₃]` or other) | MEDIUM | Expected — this is the *purpose* of cycle 386. Document in scoping doc cycle 386 update; kernel becomes new agreement hypothesis. |
| LOC budget overrun (>350 LOC) | LOW | If hitting 400 LOC, ship Priority 1 only (skip Priority 2 stretch). |
| §422 streak break via accidental sorry/axiom | LOW | Pre-flight `lean_verify` after each named theorem; abort branch and decompose if any sub-helper needs `sorry`. |
| `derivativeWeightProd_cons` unfolding shape mismatch | LOW | Cycle 368/367 templates already verified the cons-case unfolds; reuse verbatim. |

## Concrete Lean structure (template, fill in closed form from paper-derivation)

```lean
theorem elementaryWeightQ_phi_inv_mkBroomCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
      (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry])
      = -- PAPER-DERIVE: closed form in v, c, b', m, M_broom₃, bc,
        --              plus any new kernel from Block (4)
        sorry  -- replace with actual closed form
        := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- let-bindings for elementary weights
  set v := M.elementaryWeight RootedTree.vertex with hv_def
  set c := M.elementaryWeight RootedTree.cherry with hc_def
  set b' := M.elementaryWeight RootedTree.broom₃ with hbroom_def
  set m := M.elementaryWeight (RootedTree.mk [RootedTree.cherry])
    with hmkCherry_def
  set M_broom₃ := M.elementaryWeight (RootedTree.mk [RootedTree.broom₃])
    with hmkBroom_def
  -- ... additional kernels as paper-derivation determines
  -- Cycle 358 LHS expansion:
  rw [elementaryWeightQ_phi_inv_mk]
  -- Cycle 368/367 inner-factor unfolds, cycle 371/372 distribution
  -- pattern, cycle 372 constant-consolidation for shared sums:
  ...
  ring

theorem powRep_sum_eq_of_agreement_at_mkBroomCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : ...) (h_cherry : ...) (h_broom₃ : ...)
    (h_mkCherry : ...) (h_mkBroom₃ : ...) (h_mkBroomCherry : ...)
    -- plus any new kernel from Block (4)
    : elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry])
    = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
        (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry]) := by
  have h_inv : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
    ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := fun ζ => by
    rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_inv, h_inv]
  rw [elementaryWeightQ_phi_inv_mkBroomCherry,
      elementaryWeightQ_phi_inv_mkBroomCherry]
  rw [h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkBroom₃,
      h_mkBroomCherry] -- and any new kernel from Block (4)

example : elementaryWeightQ_phi
    ((⟦⟨1, RKTableau.explicitEuler⟩⟧
      : Quotient PhiEquivalent.setoidSigma)⁻¹)
    (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry])
  = -- COMPUTE from closed form at v = c = b' = m = ... = 1
    sorry := by
  rw [elementaryWeightQ_phi_inv_mkBroomCherry]
  simp [explicitEuler, RKTableau.explicitEuler,
        Fin.sum_univ_one, Matrix.of_apply]
  norm_num

example (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
      (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry])
    = elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
      (RootedTree.mk [RootedTree.broom₃, RootedTree.cherry]) :=
  powRep_sum_eq_of_agreement_at_mkBroomCherry_zero η_q η_q
    rfl rfl rfl rfl rfl rfl -- one rfl per agreement hypothesis
```

## Cycle 387+ outlook

After cycle 386 lands the 10th Family C witness, cycle 387 options:

* **α'.4.1** (recommended): ship recursive `inversePolyTree` (Variant
  V4) + `bichildPolynomial` helper, with calibration witnesses across
  all 10 ladder trees. ~300–500 LOC, may span 2 cycles. Per scoping
  doc §5.2.

* **α'.4.0 stretch** (alternative): one more Family C data point if
  cycle 386 reveals the Block (4) bilinear cross-term is more complex
  than predicted. Candidates: `mk [vertex, broom₃]` (k=2, leaf +
  non-leaf, order 5) or `mk [broom₃, broom₃]` (k=2, symmetric two-
  broom, order 7).

* Pivot to fresh entity if cycle 386 hits unexpected difficulty. But
  §422 has high compound momentum; pivot is cycle 389+ territory.

Phase E sealing of `def:422B` continues to be projected for the 390s
given Sub-lemma A's general body is the multi-cycle blocker. Stay the
course on the §422 track.
