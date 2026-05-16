# Cycle 339 strategy — `def:422B` Phase B: `Group.zpow` non-vacuity

## §A. Context

Cycle 338 shipped Phase A.0.2 of `def:422B`, closing the on-tree
elementary-weight signature of `D_element`:

* `D_element_elementaryWeight_higher_order` — `Φ_D(t) = 0` for
  `t.order ≥ 2`.
* `D_element_elementaryWeight` — Phase A.0.2 capstone packaging
  cycle 337's `_vertex` (`Φ_D(τ) = 1`) and B.1, matching Butcher
  §387's `Φ_D` exactly on `T`.
* `D_phi_mul` — `D_phi (η * η') = η * D_phi η'` simp lemma via
  `mul_assoc` in cycle 236's `instGroup_phi`.

Section422.lean: 133 → ~220 LOC. Sorry count 0. Phase A is complete.

Per `.prover-state/issues/def_422B_path.md` §5 / §7 and cycle 338's
"Suggested next approach", **the next deliverable is Phase B**:
`Group.zpow` API non-vacuity on `Quotient PhiEquivalent.setoidSigma`.

There are no Aristotle results pending and no blocker issues
reported. Sorry count is 0. The cycle 338 supervisor verdict and
recent §344 streak break have left the project in a clean state with
clear forward momentum on the §422 LMM↔§383-group bridge.

## §B. Priority 1 (P1) — Phase B: Group.zpow sanity ship

**Goal**: Verify Mathlib's `Group.zpow_natCast`, `zpow_neg_one`,
`zpow_zero`, `zpow_one`, and related integer-power lemmas fire
correctly on `Quotient PhiEquivalent.setoidSigma`, and ship 2–4
small non-vacuity sanity theorems exercising `D_element`'s integer
powers.

**Location**: append to `OpenMath/Chapter4/Section422.lean` after the
existing `D_phi_mul` simp lemma.

**Concrete deliverables** (~30–60 LOC total):

### B.1 — `D_element_zpow_zero`

```lean
@[simp]
theorem D_element_zpow_zero : D_element ^ (0 : ℤ) = 1 := zpow_zero _
```

Trivial verification that the `Group` instance's `zpow` reduces at
`n = 0` to the group identity. One-liner.

### B.2 — `D_element_zpow_one`

```lean
@[simp]
theorem D_element_zpow_one : D_element ^ (1 : ℤ) = D_element := zpow_one _
```

Trivial verification that `zpow` reduces at `n = 1` to `D_element`
itself. One-liner.

### B.3 — `D_element_zpow_neg_one`

```lean
theorem D_element_zpow_neg_one :
    D_element ^ (-1 : ℤ) = D_element⁻¹ := zpow_neg_one _
```

Verification that `zpow` at `n = -1` reduces to the group inverse.
This exercises cycle 236's `inverseQ_phi` lift through `Group.zpow`.
One-liner.

### B.4 — `D_element_zpow_two` (computational sanity)

Demonstrate that `D_element ^ (n : ℤ)` can be computed when `n` is a
concrete numeral, e.g.:

```lean
example : D_element ^ (2 : ℤ) = D_element * D_element := by
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) from rfl, zpow_add]
  simp [D_element_zpow_one]
```

Or via `zpow_natCast`:

```lean
example : D_element ^ (2 : ℤ) = D_element * D_element := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
  rfl
```

Use whichever closes. The goal is to confirm Mathlib's `Group.zpow`
unfolds cleanly for downstream Phase C use (which will need terms
like `D_element ^ (-(i + 1 : ℤ))` for equation (422a)).

### B.5 (optional stretch) — `paddedEuler` non-vacuity

If LOC budget permits, ship one example computing
`⟦⟨2, paddedEuler⟩⟧ ^ (-1 : ℤ)` and verifying it equals
`⟦⟨2, paddedEuler.inverse⟩⟧` via `inverseQ_phi`. This exercises the
heterogeneous-stage path and confirms the `Group.zpow` API works
beyond `D_element`.

```lean
example :
    (⟦⟨2, RKTableau.paddedEuler⟩⟧ :
      Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma)
      ^ (-1 : ℤ)
      = ⟦⟨2, RKTableau.paddedEuler.inverse⟩⟧ := by
  rw [zpow_neg_one]
  rfl  -- or `simp [inverseQ_phi_mk]`
```

## §C. Proof recipe

The deliverables above are each ≤5 LOC. The recipe is:

1. **For B.1–B.3**: Direct application of Mathlib's `zpow_zero`,
   `zpow_one`, `zpow_neg_one` lemmas. If these names have drifted,
   verify via `lean_loogle "_ ^ (0 : ℤ) = 1"` / `lean_loogle "_ ^
   (-1 : ℤ)"` early in the cycle.

2. **For B.4**: Test both `zpow_add` + arithmetic and
   `zpow_natCast` + `pow_succ` paths via `lean_multi_attempt` if
   needed. The cleanest closure is usually `rfl` after a
   `zpow_natCast` cast (since `(2 : ℕ) → ℤ` is definitional and
   `pow` for groups unfolds via `Monoid.npow_succ`).

3. **For B.5**: Use `inverseQ_phi_mk` (cycle 236's `@[simp]` unfold)
   to reduce `⟦⟨2, paddedEuler⟩⟧⁻¹ = ⟦⟨2, paddedEuler.inverse⟩⟧`,
   then chain via `zpow_neg_one` + standard inverse manipulations.

## §D. What NOT to attempt this cycle

* **Do NOT attempt Phase C (`Eq422a` predicate)** —
  `.prover-state/issues/def_422B_path.md` §5 lists this as a separate
  cycle (~50–100 LOC), and it depends on Phase B's zpow API being
  in place. Cycle 340 target.

* **Do NOT attempt Phase D (inductive solver for η)** — multi-cycle
  work per the scoping doc §5; well-founded recursion on
  `RootedTree.order` requires careful planning and is explicitly
  flagged as "must NOT be attempted as a single deliverable" per the
  cycle 149/150 (`def:530B` operator-body sorry-first) and cycle
  200/201 (`thm:381H` deferred direction) rollback precedents.

* **Do NOT introduce a sorry-first scaffold for Phase C or D**. The
  rollback precedents mean any sorry that lacks a credible
  single-cycle close will be reverted. Phase B's deliverables are
  each axiom-clean targets, no sorry.

* **Do NOT attempt the `elementaryWeightQ_phi`-multiplicativity
  bridge over `composeQ_phi`** (Phase A.0.3 optional). The cycle 338
  task results explicitly noted this is "deferred unless a
  downstream consumer demands it"; Phase B (zpow API) does not
  consume it.

* **Do NOT raise `maxHeartbeats` above 200000**. The Phase B
  deliverables are all single-tactic / few-line proofs; no heartbeat
  pressure expected.

* **Do NOT modify `Section422.lean`'s existing cycle 336–338 work**
  (`D_element`, `D_phi`, `D_phi_one`, `D_element_elementaryWeight_vertex`,
  `D_element_elementaryWeight_higher_order`, `D_element_elementaryWeight`,
  `D_phi_mul`). All are axiom-clean and load-bearing for Phase B.

* **Do NOT compile `Section441.lean`** — 43+ consecutive GPFS
  timeouts per `.prover-state/issues/cycle_182_gpfs_slowness.md`. Not
  relevant to cycle 339's §422 work.

* **Do NOT try to compute `D_element^n` by unfolding `D_element`
  manually**. Stay at the `Group.zpow` abstraction level — Mathlib's
  lemmas do the work. Manual unfolding to `⟦⟨1, RKTableau.explicitEuler⟩⟧`
  and computing `(explicitEuler).inverse` would balloon LOC and
  duplicate cycle 236's `inverseQ_phi` work.

## §E. Mathlib hooks to verify early

Run `lean_local_search` / `lean_loogle` once at the start of cycle
339 to confirm these names at HEAD:

| Goal | Candidate lemma | File |
|---|---|---|
| `g ^ (0 : ℤ) = 1` | `zpow_zero` | `Mathlib.Algebra.GroupPower.Basic` |
| `g ^ (1 : ℤ) = g` | `zpow_one` | same |
| `g ^ (-1 : ℤ) = g⁻¹` | `zpow_neg_one` | same |
| `g ^ ((n : ℕ) : ℤ) = g ^ n` | `zpow_natCast` | same |
| `g ^ (m + n : ℤ) = g ^ m * g ^ n` | `zpow_add` | same |

If any names have drifted (e.g. `zpow_neg_one` may be `zpow_neg_one'`
or `Group.zpow_neg_one` in recent Mathlib), adjust accordingly. The
`instGroup_phi` instance (cycle 236) provides the `Group` typeclass,
so all `Group.zpow` lemmas should fire on `Quotient
PhiEquivalent.setoidSigma` without further setup.

If `lean_loogle` is rate-limited, fall back to `lean_local_search
"zpow"` or grep Mathlib directly:
```
grep -rn "theorem zpow_zero\|theorem zpow_one\|theorem zpow_neg_one\|theorem zpow_natCast" \
    .lake/packages/mathlib/Mathlib/Algebra/GroupPower/
```

## §F. Ship checklist

Cycle 339 should ship:

1. **B.1–B.4**: 4 axiom-clean theorems / examples at
   `OpenMath/Chapter4/Section422.lean`, appended after `D_phi_mul`.
2. **B.5 (optional)**: 1 `paddedEuler` non-vacuity example if budget
   permits.
3. **lean_status.json**: `def:422B` row updated to bump cycle
   reference to 339; status remains `partial` (Phase B is
   infrastructure, not a textbook entity closure).
4. **plan.md**: append cycle 339 note to the `[~] def:422B` row
   documenting Phase B closure.
5. **task_results/cycle_339.md** — standard sections (Worked on,
   Approach, Result, Faithfulness check, Dead ends, Discovery,
   Suggested next approach).
6. **Run `lake env lean OpenMath/Chapter4/Section422.lean`** to
   verify clean compile.
7. **Run `#print axioms` on each new theorem** to confirm
   `[propext, Classical.choice, Quot.sound]` only.

LOC budget: ~30–60 LOC across Section422.lean. Well under any
budget concern.

## §G. Outlook beyond cycle 339

After Phase B lands, cycle 340 ships Phase C (`Eq422a` predicate +
non-vacuity sanity check), and cycle 341+ begins Phase D (the
inductive η-solver, multi-cycle with sub-phase decomposition per
the scoping doc §5: D.1 base case at `τ`, D.2 well-founded recursion
infrastructure, D.3 inductive step). See
`.prover-state/issues/def_422B_path.md` §5 for the full 6-phase
roadmap toward sealing `def:422B`. Phase E (lift to quotient + seal)
and optional Phase F (connect to thm:422A existence) close the chain.
