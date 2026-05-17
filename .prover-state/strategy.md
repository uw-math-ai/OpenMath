# Strategy for Cycle 359

## §A. State at start of cycle

* **Sorry count**: 0 (clean repo at HEAD `b2b689a`).
* **No Aristotle results pending.**
* **No active stuck-on blocker.**
* **In-progress entity**: `def:422B` (underlying one-step method, §422
  Ch.4) — Phase D.3 partial. Cycle 358 shipped Phase D.3.a.{1,2}
  (`elementaryWeightQ_phi_mul_mk` and `_inv_mk`) generalising cycle
  341 P1/P2 from `RootedTree.vertex` to arbitrary trees. D.3.a.3
  (zpow at arbitrary trees) was explicitly deferred with a concrete
  strategy documented in
  `.prover-state/issues/def_422B_phase_D_3_scoping.md` §5
  "Cycle 358 update — D.3.a partial ship".

## §B. Cycle 359 target — Phase D.3.a.3

Ship **`RKTableau.powRep` + quotient-equality lemma + recursive
D.3.a.3 zpow identity** in `OpenMath/Chapter4/Section422.lean`,
appended immediately after cycle 358's `elementaryWeightQ_phi_inv_mk`
block (around line 1742).

### Why this target

* It is the **unique remaining Phase D.3.a sub-deliverable** before
  Phase D.3.b (linear coefficient extraction) can proceed. The
  scoping doc §5 phase table shows D.3.a.3 as the cycle 359 slot
  with all downstream phases (D.3.b/c/d, Phase E) gated behind it.
* The cycle 358 worker's Discovery section pinned down the precise
  structural obstacle (no canonical `η_q^m` representative makes
  `pow_succ`-induction fail to telescope at arbitrary `t`) AND the
  fix (introduce `powRep` as the canonical representative).
* Single-cycle achievable (~80 LOC per cycle 358 estimate). The
  shape mirrors cycle 341 P3 with `powRep`-indexed bottom-block
  references replacing the implicit `η_q^m` representative.

## §C. Concrete approach

### Step 1 — `RKTableau.powRep` recursive construction (~15 LOC)

In `OpenMath/Chapter3/Section381.lean` (NOT Section422, since this
is `RKTableau`-typed infrastructure that belongs with `compose` /
`inverse` / `id`), inserted after cycle 222's `inverseQ_phi_mk` at
line ~4278, before the §383 `Group` instance section starts at
line ~4294.

```lean
/-- *Phase D.3.a.3 infrastructure (cycle 359):* the explicit `m`-fold
self-composition of an `RKTableau` `M` as a Σ-typed value, packaging
both the resulting stage count (`0` for `m = 0`, then `s · m` for
`m ≥ 1`) and the assembled tableau. Used as the canonical
representative for `⟦M⟧^m` in the §383 quotient group.

Base case `powRep 0 M = ⟨0, RKTableau.id⟩` matches cycle 219's
identity element. Recursive case `powRep (m+1) M` composes the
previous power with one more copy of `M` via cycle 209's
`RKTableau.compose`. -/
noncomputable def RKTableau.powRep {s : ℕ} (M : RKTableau s) :
    ℕ → Σ s' : ℕ, RKTableau s'
  | 0 => ⟨0, RKTableau.id⟩
  | m + 1 =>
    let prev := M.powRep m
    ⟨prev.1 + s, prev.2.compose M⟩
```

Use `let` (not nested `match`) for the recursive case to keep the
projection clean. `noncomputable` because `RKTableau.compose` is
noncomputable.

### Step 2 — quotient-equality lemma (~25 LOC)

In the same location, after `powRep`:

```lean
/-- *Phase D.3.a.3 infrastructure (cycle 359):* the `powRep`
representative correctly realises the quotient-level `m`-fold
power. By induction on `m`:
* `m = 0`: `⟦powRep 0 M⟧ = ⟦⟨0, RKTableau.id⟩⟧ = 1 = ⟦⟨s, M⟩⟧^0`.
* `m = k+1`: `⟦powRep (k+1) M⟧ = ⟦(powRep k M).2.compose M⟧
  = ⟦powRep k M⟧ * ⟦⟨s, M⟩⟧ = ⟦⟨s, M⟩⟧^k * ⟦⟨s, M⟩⟧ = ⟦⟨s, M⟩⟧^(k+1)`.
The middle equality uses `Quotient.mk` of a `composeQ_phi`-applied
class (definitional through `Quotient.lift₂_mk` in `composeQ_phi`'s
body); the final step is `pow_succ`. -/
theorem RKTableau.powRep_quotient_eq {s : ℕ} (M : RKTableau s) (m : ℕ) :
    Quotient.mk PhiEquivalent.setoidSigma (M.powRep m)
      = (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ m := by
  induction m with
  | zero =>
    show Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ = _
    rw [pow_zero]
    rfl
  | succ k ih =>
    show Quotient.mk PhiEquivalent.setoidSigma
          ⟨(M.powRep k).1 + s, (M.powRep k).2.compose M⟩ = _
    rw [pow_succ, ← ih]
    rfl
```

**Risk on the final `rfl`**: if `composeQ_phi`'s unfold is not
definitional through the `instMul_phi` typeclass at the Σ-projection
level, fall back to an explicit `show` reframing:
```lean
    show composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma (M.powRep k))
                     (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) = _
    rfl
```
Cycle 218 has `composeQ` working as `noncomputable def
composeQ : Quotient setoidSigma → Quotient setoidSigma → Quotient setoidSigma
:= Quotient.lift₂ (fun p q => Quotient.mk' ⟨p.1 + q.1, p.2.compose q.2⟩) ...`,
so `composeQ_phi ⟦a⟧ ⟦b⟧` reduces by `Quotient.lift₂_mk` to
`⟦⟨a.1 + b.1, a.2.compose b.2⟩⟧` definitionally.

### Step 3 — D.3.a.3 natural-number form (~30 LOC)

Back in `OpenMath/Chapter4/Section422.lean`, appended after cycle
358's `elementaryWeightQ_phi_inv_mk` (around line 1742, before the
§"Phase C — Eq422a condition predicate" block if any, or before the
trailing `end` namespace declaration):

```lean
/-- *Phase D.3.a.3 (cycle 359):* generalisation of cycle 341 P3
(`elementaryWeightQ_phi_zpow_vertex`) from `RootedTree.vertex` to
arbitrary `t`, in *recursive* form. Unlike the vertex case (which
admits the closed form `(n : ℝ) · Φ_η(τ)`), at arbitrary `t` the
recursion uses the canonical representative `powRep` (cycle 359's
new infrastructure) for the bottom-block source method at each step.

By induction on `m` via D.3.a.1 (`elementaryWeightQ_phi_mul_mk`)
plus cycle 359's `powRep_quotient_eq` to identify `⟦powRep k M⟧`
with `⟦⟨s, M⟩⟧^k`. -/
theorem elementaryWeightQ_phi_pow_succ_mk {s : ℕ} (M : RKTableau s)
    (m : ℕ) (t : RT) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ (m + 1)) t
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ m) t
        + ∑ i : Fin s, M.b i *
            M.derivativeWeightWithSrc (M.powRep m).2 i t := by
  -- Step A: ⟦M⟧^(m+1) = ⟦M⟧^m * ⟦M⟧ via pow_succ
  rw [pow_succ]
  -- Step B: ⟦M⟧^m = ⟦powRep m M⟧ via cycle 359's powRep_quotient_eq (reversed)
  rw [← powRep_quotient_eq M m]
  -- Step C: apply D.3.a.1 with M₁ := (powRep m M).2, M₂ := M.
  -- The `show` reframes the `*` to the explicit `composeQ_phi` form
  -- that D.3.a.1 consumes (this matches the cycle 358 pattern).
  show elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma (M.powRep m) *
         Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t = _
  rw [elementaryWeightQ_phi_mul_mk (M.powRep m).2 M t]
  -- Step D: rewrite Φ_{⟦powRep m M⟧}(t) back to Φ_{⟦M⟧^m}(t) on RHS
  rw [powRep_quotient_eq M m]
```

**Risk note on Step D**: the `rw` in Step D rewrites the LHS
factor `⟦powRep m M⟧` in `elementaryWeightQ_phi ⟦powRep m M⟧ t` to
`⟦M⟩^m`. The goal pattern after Step C is `elementaryWeightQ_phi
⟦powRep m M⟧ t + Σᵢ ... = elementaryWeightQ_phi ⟦M⟧^m t + Σᵢ ...`.
The `rw [powRep_quotient_eq M m]` should fire on the LHS to
introduce `⟦M⟧^m` and produce a reflexive equation. If the `rw`
patterns don't match, use `congr 1; exact congrArg
(fun q => elementaryWeightQ_phi q t) (powRep_quotient_eq M m)` as
fallback.

### Step 4 — DEFER ℤ-form to cycle 360

**DO NOT** ship the ℤ-form (`elementaryWeightQ_phi_zpow_mk`) in
cycle 359. The cycle 358 task results §"Suggested next approach"
mentions the ℤ-extension but the exact form ("`extend to n : ℤ via
case split on Int.ofNat / Int.negSucc composing D.3.a.2 (inverse)
with the natural-number version`") is under-specified. The right
shape depends on how D.3.b (cycle 360 target) consumes it; pinning
the signature against D.3.b's actual need is cleaner than guessing
in cycle 359.

If after Steps 1–3 + 5 there is still cycle budget, optionally ship
a *single named ℤ-form* statement as **stretch**, but only if it
discharges in ≤ 10 LOC via direct case split on `Int.ofNat`/`negSucc`.
If the proof requires more than that, stop and defer to cycle 360.

### Step 5 — non-vacuity (~15 LOC)

Two/three `example`s at the end of the cycle 358 block:

```lean
/-- *Cycle 359 non-vacuity:* `powRep` base case on `explicitEuler`. -/
example : RKTableau.powRep RKTableau.explicitEuler 0
    = ⟨0, RKTableau.id⟩ := rfl

/-- *Cycle 359 non-vacuity:* `powRep` first step stage-count on
`explicitEuler` (s = 1, so m = 1 should give s' = 0 + 1 = 1). -/
example : (RKTableau.powRep RKTableau.explicitEuler 1).1 = 1 := rfl

/-- *Cycle 359 non-vacuity:* end-to-end D.3.a.3 ℕ-form on
`explicitEuler` at `m = 0`, `t = cherry`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) ^ (0 + 1)) RootedTree.cherry
      = elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ 0) RootedTree.cherry
        + ∑ i : Fin 1, RKTableau.explicitEuler.b i *
            RKTableau.explicitEuler.derivativeWeightWithSrc
              (RKTableau.explicitEuler.powRep 0).2 i RootedTree.cherry :=
  elementaryWeightQ_phi_pow_succ_mk RKTableau.explicitEuler 0 RootedTree.cherry
```

If `RT` doesn't resolve `RootedTree.cherry`, use
`OpenMath.Chapter3.Section310.RootedTree.cherry` (fully qualified).

## §D. What NOT to do — explicit blacklist

1. **DO NOT attempt to lift cycle 341 P3 directly via `pow_succ`
   induction at arbitrary `t`.** The cycle 358 worker confirmed
   this fails because the bottom-block at each `pow_succ` step
   depends on the specific representative of `η_q^m`, and there is
   no canonical representative without `powRep`. This is the
   structural reason for the `powRep` detour.

2. **DO NOT introduce the strawman spurious `-Φ_M(t)` term in
   D.3.a.3** (analog of the cycle 358 strawman error in D.3.a.2
   that the cycle 358 worker corrected). The correct form for
   `Φ_{⟦M⟧^(m+1)}(t)` involves only `Φ_{⟦M⟧^m}(t)` plus the
   single Σ-term, NOT any extra `Φ_M(t)` term. The recipe `rw
   [pow_succ]; rw [← powRep_quotient_eq]; apply mul_mk; rw
   [powRep_quotient_eq]` produces this clean form automatically.

3. **DO NOT attempt D.3.b (linear coefficient extraction) in this
   cycle.** Per scoping doc §5 phase table, D.3.b is the cycle 360
   deliverable and requires D.3.a.3 in place. The cycle 343/358
   single-deliverable cadence applies.

4. **DO NOT ship the ℤ-form aggressively.** See Step 4. Defer to
   cycle 360 once D.3.b's needs are clear. Cycle 359 ships ℕ-form
   only.

5. **DO NOT place `powRep` and `powRep_quotient_eq` in
   `Section422.lean`.** They are `RKTableau`-typed infrastructure
   that belongs in `Section381.lean` next to `compose` / `inverse` /
   `id` / `composeQ_phi` / `inverseQ_phi`. Section422 may consume
   them via the existing `import` chain.

6. **DO NOT introduce `sorry`, `axiom`, or `constant`.** Sorry-first
   scaffolds for sub-phases get rolled back per the cycle 200/201
   rollback precedent (`thm:381H` deferred direction) and the cycle
   149/150 rollback precedent (`def:530B` operator body).

7. **DO NOT raise `maxHeartbeats` above 200000.** If
   `powRep_quotient_eq`'s inductive step stalls, decompose into a
   separate `powRep_succ_mk_eq` simp lemma extracting the `.succ`-step
   `composeQ_phi`-unfold.

8. **DO NOT modify cycle 358's `elementaryWeightQ_phi_{mul,inv}_mk`
   signatures.** They are axiom-clean and consumed by D.3.a.3. Any
   modification breaks the cycle 358 deliverable.

9. **DO NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
   43+ consecutive GPFS-blocked timeouts since cycle 182 (per
   `cycle_182_gpfs_slowness.md`). The §422 work does NOT depend on
   Section441, so this is not a blocker — but do not test-compile it.

## §E. Risk assessment

### Risks that may fire

* **R1 (medium)**: the `rfl` at the end of `powRep_quotient_eq`'s
  succ case may not fire if `composeQ_phi`'s definitional unfold
  through `instMul_phi` doesn't reduce the `Quotient.mk` of a
  Σ-typed pair to the expected `composeQ_phi`-applied form. **Mitigation**:
  fallback in Step 2 (explicit `show` reframing exposing
  `composeQ_phi`).
* **R2 (medium)**: the `rw [← powRep_quotient_eq]` in Step 3 may
  fail to fire because the goal pattern after `pow_succ` may have
  the form `_ * _` and not contain the literal `⟦⟨s, M⟩⟧^m`
  pattern. **Mitigation**: use `conv_lhs => rw [← ...]` to localise,
  or restate the proof flow as "rewrite RHS first to introduce
  `powRep` then apply mul_mk".
* **R3 (low)**: `noncomputable` propagation through `powRep`'s
  recursive definition may trigger unexpected `Decidable` lookup
  failures. **Mitigation**: use `noncomputable def` consistently
  (matches cycle 222's `inverseQ` pattern).
* **R4 (low)**: `Section422.lean`'s `RT` private abbrev may not
  recognise `RootedTree.cherry` in non-vacuity examples. **Mitigation**:
  use fully-qualified `OpenMath.Chapter3.Section310.RootedTree.cherry`.

### Risks that should NOT fire (per cycle 222/232/236/358 precedent)

* `RKTableau.compose` (cycle 209) and `composeQ_phi` (cycle 232) are
  both axiom-clean and well-tested through cycles 233–358.
* `Quotient.lift` / `Quotient.mk` / `Quotient.sound` are Mathlib-stable.
* `pow_succ` / `pow_zero` (`Monoid.npow_succ` / `_zero`) work through
  `Group.toMonoid` instance derivation from cycle 236's `instGroup_phi`.

## §F. Cycle 359 ship checklist

1. **Edit `OpenMath/Chapter3/Section381.lean`**: insert `powRep`
   and `powRep_quotient_eq` after cycle 222's `inverseQ_phi_mk`
   block (line ~4278), before the §383 `Group` instance section
   (line ~4294).
2. **Edit `OpenMath/Chapter4/Section422.lean`**: append D.3.a.3
   `elementaryWeightQ_phi_pow_succ_mk` after cycle 358's
   `elementaryWeightQ_phi_inv_mk` block (line ~1742).
3. **Verify**: `lake env lean OpenMath/Chapter3/Section381.lean`
   exits 0. Then `lake env lean OpenMath/Chapter4/Section422.lean`
   exits 0.
4. **Axiom check** via `#print axioms` (or `lean_verify`):
   * `OpenMath.Chapter3.Section312.RKTableau.powRep` (a `def`;
     axiom dependence may be empty or `[Classical.choice]` only)
   * `OpenMath.Chapter3.Section312.RKTableau.powRep_quotient_eq`
   * `OpenMath.Chapter4.Section422.elementaryWeightQ_phi_pow_succ_mk`
   All theorems should depend only on `[propext, Classical.choice, Quot.sound]`.
5. **Sorry count**: must remain 0. `grep -c sorry
   OpenMath/Chapter4/Section422.lean` returns 0; same for Section381.
6. **Aggregator check**: `lake env lean OpenMath/Chapter3.lean` and
   `lake env lean OpenMath/Chapter4.lean` both exit 0 (catches
   downstream regressions).
7. **Update `extraction/formalization_data/lean_status.json`**:
   `def:422B` row `cycle_completed_at: 358 → 359`, note appended
   with cycle 359's ship details (powRep + powRep_quotient_eq +
   pow_succ_mk).
8. **Update `plan.md`**: `def:422B` paragraph appended with cycle
   359 update.
9. **Update
   `.prover-state/issues/def_422B_phase_D_3_scoping.md`**: §5 phase
   table mark D.3.a.3 as ✅ shipped cycle 359; append a "Cycle 359
   update" subsection (analogous to cycle 358's update); advance
   "Cycle 360 entry point" to D.3.b.
10. **Write `.prover-state/task_results/cycle_359.md`** with
    standard sections (Worked on / Approach / Result / Faithfulness
    check / Dead ends / Discovery / Suggested next approach).

## §G. Graceful degradation

If `powRep_quotient_eq` proves harder than expected (R1 or R2 fires
hard, both fallbacks fail):

* **Plan B**: ship only `powRep` (Step 1) + the two non-vacuity
  examples for `powRep` (Step 5 first half), plus
  `powRep_quotient_eq` *split* into a private helper
  `powRep_succ_mk_compose` (the succ-step `composeQ_phi`-unfold
  isolated) + the main `powRep_quotient_eq` consuming it. Goal:
  keep both Section381 and Section422 axiom-clean (no sorries).
  D.3.a.3 itself (`elementaryWeightQ_phi_pow_succ_mk`) slips to
  cycle 360.

* **Plan C** (if Plan B also stalls): ship only `powRep` + an
  Aristotle submission of `powRep_quotient_eq` (with all of cycle
  358 + 209 + 222 + 232 + 236 as cited template lemmas).
  Single-poll cycle 360. Section422 remains untouched; cycle 359
  ships infrastructure only.

Cycle 360+ planner makes the call based on Aristotle's return.

## §H. After cycle 359 — the §422 horizon

Per the scoping doc §5 phase table (cycle 358 update):

| Cycle | Phase | Deliverable | LOC |
|---|---|---|---|
| **359** | D.3.a.3 | powRep + recursive zpow identity | ~80 |
| 360 | D.3.b | linear coefficient extraction (textbook claim "coefficient of η(t) in η⁻ⁱ(t) is i·(-1)^r(t)") | ~100 |
| 361 | D.3.c | `sum_i_alpha_ne_zero_of_stable` (ρ'(1) ≠ 0 from ρ-stability + simple roots) | ~80 |
| 362 | D.3.d | `underlyingOneStepMethod_aux` recursive solver + spec lemma | ~120 |
| 363 | Phase E | lift to quotient + seal `def:422B` | ~50 |

Estimated 5 cycles from now to seal `def:422B`. The §422 streak
(cycles 336–359) now stands at 24 consecutive cycles, all
axiom-clean. Compound investment payoff is high; the cycle 358
worker correctly flagged that pivot temptations should be weighed
against the proximity of Phase E sealing.

**No pivot recommended for cycle 359.** Stay on `def:422B`.
