# Cycle 364 Strategy — Ship the `linearResidualAt` Coefficient Fix

## §A. Context (one paragraph)

Cycle 363's P2 audit discovered that cycle 360's `linearResidualAt`
coefficient `i·(-1)^t.order` is **mathematically wrong** at even
`r(t) ≥ 2`. Empirical Φ-computation at `(i, t) = (1, cherry)` on two
distinct methods (`explicitEuler` and Heun, both with `η(vertex) = 1`)
shows cycle 360's definition is NOT strict-subtree-dependent — its
value differs between methods at fixed `η(vertex)`. The actual
coefficient of `η(t)` in `η⁻ⁱ(t)` under our §383 Φ-quotient encoding
is **`-i`**, constant in `r(t)`. Cycle 363 P1
(`sum_i_alpha_ne_zero_of_stable_preconsistent`) is unaffected — its
non-vanishing claim concerns the absolute value of the coefficient,
which is `|−i| = i`.

Cycle 364's job is to ship the definition fix as a **single focused
cycle**. The fix is mechanical: change one sign in the `def`, update
4 closed-form theorems and ~4 non-vacuity `example`s. No new content,
no new theorems, no algebraic discovery. The fix is a prerequisite
for cycle 365+ Phase D.3.b parametricity Step 2; per cycle 363
Discovery §4, the corrected definition makes the Step 2 cancellation
structurally clean (whereas cycle 360's incorrect definition made it
intractable).

## §B. Priority 1 (MANDATORY) — Apply the definition fix

### B.1 Change `linearResidualAt` definition

File: `OpenMath/Chapter4/Section422.lean`. Locate via
`grep -n "noncomputable def linearResidualAt"` (cycle 360 shipped it
around line 1867; line number may have drifted).

**Current (cycle 360):**
```lean
noncomputable def linearResidualAt (i : ℕ)
    (η_q : Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma)
    (t : RT) : ℝ :=
  elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
    - (i : ℝ) * (-1)^t.order * elementaryWeightQ_phi η_q t
```

**Replace with:**
```lean
noncomputable def linearResidualAt (i : ℕ)
    (η_q : Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma)
    (t : RT) : ℝ :=
  elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
    + (i : ℝ) * elementaryWeightQ_phi η_q t
```

Two sign changes from the original:
1. `- (i : ℝ) * (-1)^t.order * ...` → `+ (i : ℝ) * ...`.
2. The `(-1)^t.order` factor is removed entirely.

**Why this is correct**: per cycle 363 P2 audit, the coefficient of
`η(t)` in `η⁻ⁱ(t)` is `-i` (constant in `r(t)`), so the residual
"`η⁻ⁱ(t)` minus its `η(t)`-linear part" equals
`η⁻ⁱ(t) - (-i·η(t)) = η⁻ⁱ(t) + i·η(t)`. The corrected definition
matches.

**Update the docstring** to remove the `(-1)^t.order` reference and
add a note pointing to `.prover-state/issues/def_422B_phase_D_3_scoping.md`
§10 (the cycle 363 audit) for the algebraic justification. Suggested
new docstring (replace whatever cycle 360 wrote):

```
The linear residual at `t` of `η_q^(-i)` as a polynomial in `η_q(t)`.
By the audit at `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10,
the coefficient of `η_q(t)` in `Φ_{η_q^(-i)}(t)` is `-i` (constant in
`r(t)`, under our §383 Φ-quotient encoding). Hence the residual

  linearResidualAt i η_q t := Φ_{η_q^(-i)}(t) + i·Φ_{η_q}(t)

extracts the part of `Φ_{η_q^(-i)}(t)` depending only on
strict subtrees of `t`. (Cycle 364 redefinition; cycle 360's original
form had `- i·(-1)^t.order·Φ_{η_q}(t)`, which mismatches our
quotient-encoded coefficient at even `r(t) ≥ 2`.)
```

### B.2 Update 4 closed-form theorems

After the definition change, **four theorems** built on top of
`linearResidualAt` need their statements and proofs updated. Each is
a mechanical sign-fix; proofs remain `unfold linearResidualAt;
... ; push_cast; ring`-class.

#### B.2.1 `coeff_eta_t_in_eta_zpow_neg` (cycle 360 sub-deliverable 1)

**Current statement** (find via
`grep -n "coeff_eta_t_in_eta_zpow_neg"`):
```
Φ_{η_q^(-i)}(t) = i·(-1)^t.order·Φ_{η_q}(t) + linearResidualAt i η_q t
```

**Replace with:**
```
Φ_{η_q^(-i)}(t) = -(i : ℝ)·Φ_{η_q}(t) + linearResidualAt i η_q t
```

Proof body should remain `unfold linearResidualAt; ring` (the new
`linearResidualAt` has `+ i·η_q(t)` baked in, so this is the
arithmetic `Φ_{η_q^(-i)}(t) = -i·η_q(t) + (Φ_{η_q^(-i)}(t) + i·η_q(t))`,
closed by `ring`).

#### B.2.2 `linearResidualAt_vertex_eq_zero` (cycle 360 sub-deliverable 2 base case)

**Statement remains the same shape** (residual at vertex is zero),
but the proof simplifies:

Old proof recipe:
```
unfold linearResidualAt
rw [elementaryWeightQ_phi_zpow_vertex]
have h_ord : RT.vertex.order = 1 := rfl
rw [h_ord]
push_cast; ring
```

New proof recipe (the `h_ord` rewrite is no longer needed since the
`(-1)^t.order` factor is gone):
```
unfold linearResidualAt
rw [elementaryWeightQ_phi_zpow_vertex]
push_cast; ring
```

Both yield `linearResidualAt i η_q τ = 0` since cycle 341 P3 gives
`Φ_{η_q^n}(τ) = n·Φ_{η_q}(τ)` so `Φ_{η_q^(-i)}(τ) = -i·Φ_{η_q}(τ)`,
and adding `+i·Φ_{η_q}(τ)` yields 0.

#### B.2.3 `linearResidualAt_one_mk_eq` (cycle 360 sub-deliverable 2 closed form at i=1)

**Current statement** has shape:
```
linearResidualAt 1 ⟦M⟧ t
  = -(∑ⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t)
    - (-1)^t.order · M.elementaryWeight t
```

**Replace with:**
```
linearResidualAt 1 ⟦M⟧ t
  = -(∑ⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t)
    + M.elementaryWeight t
```

Two changes: drop `(-1)^t.order`, flip sign of the
`M.elementaryWeight t` term (was `-`, now `+`).

Proof remains: `unfold linearResidualAt` + `Nat.cast_one + zpow_neg_one`
bridge + cycle 358's `elementaryWeightQ_phi_inv_mk` + cycle 226's
`elementaryWeightQ_phi_mk` + `push_cast; ring`. The `push_cast; ring`
step absorbs the sign change automatically.

#### B.2.4 `linearResidualAt_succ_mk_eq` (cycle 361 general closed form at i=m+1)

**Current statement** has shape:
```
linearResidualAt (m+1) ⟦M⟧ t
  = -(∑ⱼ (M.powRep (m+1)).2.b j · …)
    - (m+1 : ℝ) · (-1)^t.order · M.elementaryWeight t
```

**Replace with:**
```
linearResidualAt (m+1) ⟦M⟧ t
  = -(∑ⱼ (M.powRep (m+1)).2.b j · …)
    + (m+1 : ℝ) · M.elementaryWeight t
```

Same two changes as B.2.3: drop `(-1)^t.order`, flip sign of the
`M.elementaryWeight t` term.

Proof remains: `unfold linearResidualAt` + `h_pow` rfl bridge to
`Int.negSucc m` + ℤ-form lift (`elementaryWeightQ_phi_zpow_negSucc_mk`)
+ `elementaryWeightQ_phi_mk` + `push_cast; ring`.

### B.3 Update non-vacuity `example`s

Find via `grep -n "^example" OpenMath/Chapter4/Section422.lean` — look
for examples that reference `linearResidualAt`. Cycle 360 shipped 4
examples; cycle 361 shipped 4 more. Each example's RHS numerical
value may change to match the new definition.

For each example:
1. Read the example's current claim (e.g. cycle 361's vertex-sanity
   `linearResidualAt 3 ⟦explicitEuler⟧ vertex = 0`).
2. Recompute the RHS under the new definition.
3. Update the example body if the value changed.

Pre-flight predictions from the audit:
- Examples at `t = vertex`: residual remains `0` (vertex case is
  unchanged — the cancellation `-i·η(τ) + i·η(τ) = 0` holds in both
  the old and new definitions, since `vertex.order = 1` makes
  `(-1)^1 = -1` and `-i·(-1)·η(τ) = i·η(τ)`, identical to the new
  `+i·η(τ)` term modulo a sign flip in the surrounding bracket).
- Examples at `t = cherry` (order 2): values WILL change because
  cycle 360's form mismatched at even `r(t)`. For `explicitEuler`
  at `t = cherry` with `i = 1`: cycle 363 audit gives the new value
  as `1` (vs cycle 360's value of `1` per the audit table — actually
  both forms happen to give 1 on `explicitEuler` because
  `η(cherry) = 0` collapses the difference; check Heun cases for
  the real divergence).

If unsure about a given example's new numerical value, use the cycle
363 P2 audit recipe (audit doc §10) to compute it. For
`explicitEuler`: `η(vertex) = 1`, `η(cherry) = 0`, so
`linearResidualAt' 1 ⟦explicitEuler⟧ cherry = 1`.

If any example becomes false under the new definition AND there is
no obvious replacement that lands cleanly within a 10-min budget,
**delete the example** with an inline comment noting it was removed
in cycle 364 due to the definition change. Do NOT leave a broken
example in place.

### B.4 Verify

After all edits:
1. `lake build OpenMath.Chapter4.Section422` — must exit 0.
   Expected wall-time ~250 s based on cycle 363's measurement.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must be 0.
3. Axiom check on the 4 updated theorems via a `/tmp/axiom_check.lean`
   scratch file (cycle 363 worker's CAVEAT: `lake env lean` does NOT
   refresh the cached olean, so axiom checks against newly-edited
   symbols can fail with "Unknown constant" until `lake build`
   regenerates the cache):
   ```
   import OpenMath.Chapter4.Section422
   #print axioms OpenMath.Chapter4.Section422.linearResidualAt_vertex_eq_zero
   #print axioms OpenMath.Chapter4.Section422.coeff_eta_t_in_eta_zpow_neg
   #print axioms OpenMath.Chapter4.Section422.linearResidualAt_one_mk_eq
   #print axioms OpenMath.Chapter4.Section422.linearResidualAt_succ_mk_eq
   ```
   All four should return `[propext, Classical.choice, Quot.sound]`.

## §C. Priority 2 (STRETCH, only if §B closes by minute 90)

### C.1 Add two explicit "audit-validation" examples

These pin the new definition's values at the two methods from cycle
363's audit (`explicitEuler` and Heun's 2-stage method), providing
permanent regression witnesses against any future sign confusion:

```lean
-- Audit validation (cycle 363 P2 doc §10): explicitEuler has
-- η(vertex) = 1, η(cherry) = 0, so
-- linearResidualAt 1 ⟦explicitEuler⟧ cherry = η(vertex)² = 1
-- (since η⁻¹(cherry) = η(vertex)² − η(cherry), and the residual
-- after adding +i·η(t) = +η(cherry) = 0 yields η(vertex)² = 1).
example :
    linearResidualAt 1
      (Quotient.mk _ ⟨1, OpenMath.Chapter3.Section312.RKTableau.explicitEuler⟩)
      RT.cherry
    = 1 := by
  rw [linearResidualAt_one_mk_eq]
  -- discharge via explicitEuler closed-form computation
  ...
```

If discharging this example requires non-trivial
`derivativeWeightWithSrc` unfolding that exceeds 20 minutes,
**OMIT the example**. The cycle 363 audit doc already documents the
values; cycle 364 does not need to re-witness them in Lean. The C.1
ship is optional and contingent on its closing in <30 minutes total.

### C.2 Update `.prover-state/issues/def_422B_phase_D_3_scoping.md`

Append a "Cycle 364 closure" subsection to §10 documenting:
- That the definition fix shipped.
- That all 4 closed-form theorems were updated.
- That cycle 365+ can now attempt Phase D.3.b parametricity Step 2
  per §10 "Recommended cycle 364 plan" → Step 2.

~5–10 lines of markdown. Ship iff §B closes cleanly.

## §D. What NOT to attempt

1. **Do NOT attempt Phase D.3.b parametricity Step 2 in cycle 364.**
   The cycle 363 audit explicitly schedules it for cycle 365+. Even
   under the corrected definition, Step 2 still requires the
   `(m+1)·η(t)` cancellation argument (cycle 363 Discovery §4) which
   is multi-cycle infrastructure. Cycle 364's atomicity (a single
   focused definition fix) is the discipline.

2. **Do NOT redefine or re-audit `linearResidualAt`'s textbook
   meaning.** Per cycle 363 P2 analysis Discovery §2, the textbook's
   `(-1)^{r(t)-1}` factor is spurious under our quotient encoding;
   the corrected form is `-i`. Cycle 364 takes this as established
   and does not re-derive it.

3. **Do NOT touch cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`.**
   It is a structural property of `derivativeWeightWithSrc` and is
   independent of `linearResidualAt`'s coefficient choice (cycle 363
   Discovery §3). Leave it as-is in `Section381.lean`.

4. **Do NOT introduce `sorry`/`axiom`/`constant`.** The cycle 200/201
   rollback precedent applies: if any of the 4 closed-form theorems
   fails to close axiom-clean with the proposed `push_cast; ring`
   recipe, decompose into smaller named lemmas rather than sorry-ing.
   If even decomposition stalls within the 90-min budget, **ROLL
   BACK** the cycle 364 changes via `git checkout --
   OpenMath/Chapter4/Section422.lean` and ship a smaller §A-only
   scoping update to the issue file.

5. **Do NOT touch §441.** GPFS slowness on `Section441.lean` is the
   43rd+ consecutive timeout per `cycle_182_gpfs_slowness.md`.
   Cycle 364's work is entirely in `Section422.lean` (which compiles
   in ~250 s per cycle 363's task results).

6. **Do NOT pivot to a fresh entity.** §422 has shipped 29 consecutive
   axiom-clean cycles (336–363) with §B as the unique blocker before
   Phase E sealing. Cycle 364's definition fix is the single highest-
   ROI deliverable for the next several cycles; pivoting would waste
   the cycle 363 audit's preparation.

7. **Do NOT change `Section381.lean`.** All cycle 364 edits are in
   `OpenMath/Chapter4/Section422.lean`. The `Section381.lean`
   infrastructure (cycle 358's `_inv_mk`, cycle 359's `powRep` /
   `powRep_quotient_eq`, cycle 362's strict-subtree-agreement lemma)
   is consumed but unchanged.

8. **Do NOT submit Aristotle jobs this cycle.** The fix is too small
   and mechanical to benefit from Aristotle's premise-selection
   strength; manual closure is faster. (If Phase D.3.b Step 2 needs
   Aristotle in cycle 365+, that's a separate decision.)

## §E. Risk register

* **R1** (low): `push_cast; ring` does not close a closed-form theorem
  after the sign change. *Mitigation*: try `push_cast; linarith`
  variants, or `linear_combination` with an explicit witness, or
  decompose into a private helper proving the per-term arithmetic.
  Budget 15 min per theorem before escalating.

* **R2** (low): a non-vacuity `example` becomes false under the new
  definition AND the corrected value is hard to discharge.
  *Mitigation*: delete the example with a comment pointing to cycle
  364; the cycle 363 audit doc already documents the correct values
  for the `explicitEuler` + Heun computations.

* **R3** (very low): the `lake build` time exceeds 5 minutes.
  *Mitigation*: build only `OpenMath.Chapter4.Section422` (not full
  `OpenMath.Chapter4`); the downstream `Chapter4.lean` aggregator
  recompiles cleanly on the next cycle.

* **R4** (very low): the cycle 363 P2 audit's coefficient claim
  (`coefficient = -i`) is itself wrong. *Mitigation*: the audit
  documented two-method numerical witnesses (`explicitEuler` and
  Heun) with `η(vertex) = 1` and divergent `η(cherry)`; under cycle
  360's definition the residual differed between methods, under the
  corrected definition it agrees. This is dispositive; the audit is
  correct. If R4 fires anyway, ROLL BACK and re-audit.

* **R5** (low): `lake env lean` vs `lake build` cache confusion (cycle
  363 worker's observation). *Mitigation*: ALWAYS use `lake build
  OpenMath.Chapter4.Section422` before `#print axioms` queries. Do
  not trust `lake env lean` to refresh oleans for downstream
  consumers.

## §F. Estimated LOC delta

* B.1 (definition + docstring): +5 / -3 (net +2).
* B.2.1 (`coeff_eta_t_in_eta_zpow_neg`): +1 / -2 (net -1).
* B.2.2 (`linearResidualAt_vertex_eq_zero`): +0 / -3 (net -3).
* B.2.3 (`linearResidualAt_one_mk_eq`): +2 / -2 (net 0).
* B.2.4 (`linearResidualAt_succ_mk_eq`): +2 / -2 (net 0).
* B.3 (~4–8 examples): variable, ±5 each, net ±0 to ±20.
* C.1 (optional): +20.
* C.2 (optional): +10 markdown in scoping doc.

**Total expected**: net -5 to +20 LOC in `Section422.lean`. File size
remains approximately constant around 2150 LOC. Bookkeeping work
in lean_status.json / plan.md / task_results adds ~30 lines markdown.

## §G. Cycle 364 ship checklist

Before declaring cycle complete:

1. ☐ §B.1 — `linearResidualAt` redefined with new docstring.
2. ☐ §B.2 — 4 closed-form theorems updated (statement + proof).
3. ☐ §B.3 — non-vacuity examples updated or deleted as needed.
4. ☐ §B.4 — `lake build OpenMath.Chapter4.Section422` exits 0.
5. ☐ §B.4 — `grep -c sorry` = 0.
6. ☐ §B.4 — `#print axioms` on all 4 updated theorems returns
   `[propext, Classical.choice, Quot.sound]`.
7. ☐ `lean_status.json` — `def:422B` row unchanged (`partial`;
   the definition fix is internal Phase D.3.b refactoring, not a
   status bump).
8. ☐ `plan.md` — `[~] def:422B` row may gain a cycle 364 closure
   note documenting the redefinition.
9. ☐ `.prover-state/task_results/cycle_364.md` — standard sections
   per CLAUDE.md template, including a faithfulness-check entry for
   the redefined `linearResidualAt` (citing cycle 363 P2 audit).
10. ☐ If §C executed: `.prover-state/issues/def_422B_phase_D_3_scoping.md`
    appended with "Cycle 364 closure" subsection.

§422 axiom-clean streak target: **29 → 30** consecutive cycles
(336–364).

## §H. Cycle 365+ entry point (read-ahead, not for this cycle)

After cycle 364 ships, the cycle 365 planner should attempt **Phase
D.3.b parametricity Step 2** under the corrected definition:

```lean
theorem linearResidualAt_depends_only_on_strict_subtrees (i : ℕ)
    {η_q η_q' : Quotient PhiEquivalent.setoidSigma} (t : RT)
    (h : ∀ s : RT, s.order < t.order →
         elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```

Per cycle 363 Discovery §4, the cancellation argument is now
structurally clean: the `+(i+1)·M.elementaryWeight t` term in the
corrected `linearResidualAt_succ_mk_eq` cancels exactly against the
`-(i+1)·M.elementaryWeight t` contribution implicit in the powRep-sum
(via cycle 235-style identities lifted to composite representatives).
Estimated 150–250 LOC for cycle 365; may decompose into a dedicated
"composite inverse decomposition" sub-lemma. This is NOT cycle 364's
work.

After Step 2 lands:
* **Cycle 366** (Phase D.3.d): `noncomputable def underlyingOneStepMethod_aux`
  + spec lemma. ~80–120 LOC.
* **Cycle 367** (Phase E): lift to quotient, seal `def:422B`,
  `thm:422A` existence falls out. ~60–100 LOC.

Phase E sealing now projected for cycle 367 (was 366 in cycle 363's
estimate; one cycle slip from the cycle 364 redefinition).
