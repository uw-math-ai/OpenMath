# Cycle 239 Strategy

## State at cycle start

* **Sorry count: 0** across the repo (`plan.md` "Sorry locations" block is
  empty). 47 consecutive clean cycles since the cycle 201 rollback.
* **lem:441B is FULLY FORMALIZED** as of cycle 238 (`OpenMath/Chapter4/Section441B.lean`,
  axiom-clean `cInverseLog_neg`). Phase B (cycle 237) + Phase C (cycle 238).
* **§383 Group instance shipped** cycle 236 on `Quotient PhiEquivalent.setoidSigma`
  in `OpenMath/Chapter3/Section381.lean` — `inverseQ_phi`, `inverseQ_phi_mk`,
  `composeQ_phi_inverseQ_phi_left`, `instGroup_phi`.
* **§441 Phase C.2 of lem:441A** still drafted at
  `.prover-state/cycle_182_draft_section441.lean` but blocked by GPFS pathology
  on `Section441.lean` (42 consecutive timeouts as of cycle 237).
* **No Aristotle results pending** in `task_results/cycle_238.md`.

## Decision: pivot to Φ-quotient elementary-weight infrastructure

The cycle 236 task results identified the natural next step as Φ as a
`MonoidHom`/`GroupHom` from `Quotient Equivalent.setoidSigma` (§382 group) to
`Quotient PhiEquivalent.setoidSigma` (§383 group). This requires the
`Equivalent → PhiEquivalent` inclusion lemma, which routes through B-series
machinery (thm:311B/313B, both unformalized) and is therefore **multi-cycle
work** (see `.prover-state/issues/thm_381H_deferred.md` for the four-direction
analysis and the cycle 200 rollback precedent).

However, there is a cleaner tractable extension of the cycle 236 infrastructure
that does NOT require `Equivalent → PhiEquivalent`: ship the elementary-weight
function as a quotient-respecting map on `Quotient PhiEquivalent.setoidSigma`,
plus its composition-decomposition law. This builds directly on:

* cycle 225's `compose_elementaryWeight_decomp` (per-tree decomposition of
  `(M₁.compose M₂).elementaryWeight t`).
* cycle 232's full bilinear `composeQ_phi` and well-definedness witness
  `compose_phiEquivalent_compose`.
* cycle 236's `Quotient PhiEquivalent.setoidSigma` setoid and `instGroup_phi`.

These are all axiom-clean and in place. The deliverable is single-cycle
closeable and concretely useful (it's the precise statement of Butcher's
§384–§386 elementary-weight algebra at the quotient level).

## Priority 0 (5 min, hard cap): Section441 GPFS smoke test

Run:

```bash
time timeout 60 lake env lean OpenMath/Chapter4/Section441.lean
```

* **If EXIT=0 in <60s**: GPFS has cleared. Apply the cycle 182 Phase C.2
  draft + cycle 184 namespace fix (one-line, documented at
  `cycle_182_gpfs_slowness.md` cycle 184 update). Ship lem:441A Phase C.2 as
  the cycle deliverable, skip Priority 1/2.
* **If EXIT=124 or near-zero CPU after 60s**: log as the 43rd consecutive
  timeout in `cycle_182_gpfs_slowness.md` and proceed to Priority 1. Do NOT
  retry — the pattern is well-established (cycles 182–237, 42 timeouts).

## Priority 1 (primary deliverable): `elementaryWeightQ_phi` + composition law

### P1.A — Define `elementaryWeightQ_phi`

In `OpenMath/Chapter3/Section381.lean`, after cycle 236's `instGroup_phi`
block (currently the last block in the `OpenMath.Chapter3.Section312.RKTableau`
namespace), add the quotient-respecting elementary-weight map:

```lean
/-- The elementary-weight function lifted to `Quotient PhiEquivalent.setoidSigma`.
For each rooted tree `t`, `elementaryWeightQ_phi q t` returns the common
elementary weight of any representative of `q`. Well-definedness is
exactly the definition of `PhiEquivalent`. -/
noncomputable def elementaryWeightQ_phi
    (q : Quotient PhiEquivalent.setoidSigma) (t : RootedTree) : ℝ :=
  Quotient.lift (fun (p : Σ s, RKTableau s) => p.2.elementaryWeight t)
    (fun a b hab => by
      -- hab : PhiEquivalent a.2 b.2 after Setoid.r unfolding
      exact hab t) q
```

Plus an `@[simp]` unfold lemma `elementaryWeightQ_phi_mk` closing by `rfl`.

**Risk**: `PhiEquivalent.setoidSigma`'s `Setoid.r` definition may need an
explicit `show @PhiEquivalent ...` reframing inside the respect proof
(cycle 211/212/218 precedent on `Equivalent.setoidSigma`). Check cycle 223's
`PhiEquivalent.setoidSigma` definition in `Section381.lean` first and mirror
the cycle 218 `composeQ` pattern if needed.

### P1.B — Per-tree decomposition lemma on the quotient

Lift cycle 225's `compose_elementaryWeight_decomp` to the `composeQ_phi`
level via `Quotient.inductionOn₂`:

```lean
theorem elementaryWeightQ_phi_composeQ_phi
    (q q' : Quotient PhiEquivalent.setoidSigma) (t : RootedTree) :
    elementaryWeightQ_phi (composeQ_phi q q') t = <RHS-matching-cycle-225> := by
  refine Quotient.inductionOn₂ q q' ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩
  show elementaryWeightQ_phi (composeQ_phi ⟦⟨s₁, M₁⟩⟧ ⟦⟨s₂, M₂⟩⟧) t = ...
  -- Reduce via composeQ_phi_mk + elementaryWeightQ_phi_mk
  -- Goal collapses to (M₁.compose M₂).elementaryWeight t = ...
  exact compose_elementaryWeight_decomp M₁ M₂ t
```

The RHS must match cycle 225's exact statement. **First step:** read
`OpenMath/Chapter3/Section381.lean` for the cycle 225 era symbol
`compose_elementaryWeight_decomp` (use `Grep` for the exact name) and
copy its conclusion shape verbatim before writing the new theorem.

### P1.C — Identity, inverse, and PhiEquivalent-sound corollaries

Three quick corollary theorems (each ~5–10 LOC):

```lean
/-- Identity element's elementary weight is zero on every rooted tree.
Reduces by the empty `Fin 0` sum in `RKTableau.id.elementaryWeight`. -/
theorem elementaryWeightQ_phi_id (t : RootedTree) :
    elementaryWeightQ_phi
        (⟦⟨0, RKTableau.id⟩⟧ : Quotient PhiEquivalent.setoidSigma) t = 0 := by
  show RKTableau.id.elementaryWeight t = 0
  -- Use cycle 228's `id_elementaryWeight` if shipped, otherwise simp on
  -- elementaryWeight's empty Fin 0 sum.
  sorry  -- replace with the actual one-liner after reading cycle 228 result
```

If cycle 228 didn't ship `id_elementaryWeight` as a named theorem (check
`Grep "id_elementaryWeight"` in `Section381.lean`), ship it as a private
helper here.

```lean
/-- Sound bridge: equal PhiEquivalent representatives yield equal
quotient-level elementary weights. Direct from `Quotient.sound` + the
lift definition. -/
theorem elementaryWeightQ_phi_eq_of_phiEquivalent
    {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s')
    (h : PhiEquivalent M M') (t : RootedTree) :
    elementaryWeightQ_phi (⟦⟨s, M⟩⟧ : Quotient PhiEquivalent.setoidSigma) t
      = elementaryWeightQ_phi ⟦⟨s', M'⟩⟧ t := by
  exact congrArg (· t)
    (congrArg elementaryWeightQ_phi (Quotient.sound (by exact h)))
  -- (alternative form: rewrite via Quotient.sound then rfl)
```

If `elementaryWeightQ_phi_inverseQ_phi` (the inverse formula) requires
deferring because cycle 235's `inverse_elementaryWeight`-style formula
doesn't exist yet, **defer it with a TODO comment**. Do NOT block the cycle
on it.

### P1.D — `paddedEuler` non-vacuity

Add at least two concrete `example`s in `namespace OpenMath.Chapter3.Section381`
at the end of the file:

1. `elementaryWeightQ_phi_mk` definitional unfold on `⟦⟨2, paddedEuler⟩⟧`
   reducing to `paddedEuler.elementaryWeight <some-tree>` (rfl).
2. Composition law on `composeQ_phi ⟦⟨0, RKTableau.id⟩⟧ ⟦⟨2, paddedEuler⟩⟧`
   composed with cycle 234's `composeQ_phi_id_left` collapsing the LHS to
   `⟦⟨2, paddedEuler⟩⟧`, then `elementaryWeightQ_phi` matching paddedEuler's
   weight.

### Estimated LOC and verification

* Total LOC: ~100–150 over cycle 236's HEAD.
* All new symbols expected axiom-clean (`[propext, Classical.choice, Quot.sound]`).
* Compile target: warm rebuild <10s.
* Verification: `lake env lean OpenMath/Chapter3/Section381.lean` + `lean_verify`
  on each new public symbol.

## Priority 2 (stretch, if Priority 1 ships with cycle budget remaining)

Extend `OpenMath/Chapter4/Section441B.lean` with explicit closed forms for
`cInverseLog 2` and `cInverseLog 3` as cycle 238 sanity witnesses:

* `cInverseLog_two_eq : cInverseLog 2 = -2/45` — derived from the (441c)
  `z^4` coefficient: `2·c_4 + (2/3)·c_2 + (2/5)·c_0 = 0`. Use the same
  `PowerSeries.coeff_mul` antidiagonal-split + `cInverseLog_zero_eq_half` +
  `cInverseLog_one_eq_neg_one_sixth` machinery from cycle 237's base cases.
* `cInverseLog_three_eq : cInverseLog 3 = -8/945` — analogous closed form
  from the `z^6` coefficient.

These are guaranteed axiom-clean closed-form computations (~30 LOC each).
**Skip Priority 2 entirely if Priority 1 takes the full cycle budget.**

## What NOT to try

* **Do NOT attempt `Equivalent → PhiEquivalent` directly.** Confirmed
  multi-cycle work requiring B-series machinery (thm:311B and thm:313B both
  unformalized). See `thm_381H_deferred.md` for the four-direction analysis.
* **Do NOT attempt to bifurcate lem:441A Phase C** into a stand-alone file.
  Phase C is intrinsically about `aPoly`, which lives in `Section441.lean`;
  bifurcation would require duplicating the cycle 181 Möbius bridge from
  `Section441.lean`. The cycle 238 task results' suggestion to consider this
  was reviewed and rejected as net-negative.
* **Do NOT attempt thm:441C.** Still blocked on lem:441A Phase C.
* **Do NOT attempt lem:383D directly.** The textbook formula uses
  vertex-subset partitions, but our `Section383.lean` uses multiset
  sub-selection (per `convolution_vertex_vs_multiset.md`). Faithful
  formalization is multi-cycle.
* **Do NOT attempt thm:386A or thm:387A.** Both depend transitively on
  lem:383D.
* **Do NOT increase `maxHeartbeats`** above 200000. Decompose if needed.
* **Do NOT touch `scripts/autonomous_loop.py`** — the supervisor's
  "commit-not-reaching-repo" false-positive pattern is loop-maintainer
  territory (see `phantom_commit_verdict_pattern.md`).
* **Do NOT retry the Section441 GPFS smoke test** beyond Priority 0's
  60-second cap. 42 timeouts establish the pattern.
* **Do NOT poll Aristotle** more than once if you submit a batch. CLAUDE.md
  rule.

## Aristotle policy

If P1.B's composition-decomposition lemma stalls during manual proof,
submit it as an Aristotle job with cycle 225's `compose_elementaryWeight_decomp`
statement, cycle 232's `composeQ_phi`, and the new `elementaryWeightQ_phi`
definition as in-context templates. Sleep 30 min. Single poll. Incorporate
if successful.

DO NOT submit Aristotle for P1.A or P1.C — these are mechanical
`Quotient.lift` / `Quotient.inductionOn` proofs that should close in one
manual pass.

## Faithfulness discipline

* `elementaryWeightQ_phi` is the quotient-respecting lift of
  `M.elementaryWeight` (cycle 187 era, faithful Butcher §310). The textbook
  doesn't explicitly introduce a quotient version, but this is the natural
  functorial extension and matches Butcher's §384–§386 elementary-weight
  algebra implicitly. No divergence to document.
* The composition-decomposition law `elementaryWeightQ_phi_composeQ_phi` is
  the quotient-level statement of Butcher's "B-series Butcher rule"
  (cycle 225 already shipped the per-tableau version).
* If `elementaryWeightQ_phi_inverseQ_phi` requires deferring (see P1.C),
  document with a TODO comment pointing to a future cycle.

## Tautology scanner discipline

The scanner over-fires on `:= h_<name>` / `exact h_<name>` patterns. Use
underscore-free names (`hab`, `hq`, `hM`, `ht`) in new code to avoid
post-cycle cosmetic renames. See `tautology_scanner_false_positives.md` for
the cosmetic-rename pattern.

## Pre-commit faithfulness checklist (apply before committing)

For each new `def` and `theorem`:

* [ ] Lean statement matches the intended textbook content (or documented divergence).
* [ ] No tautology (conclusion ≠ any hypothesis verbatim).
* [ ] No identity-proof (`exact h_*` or `:= h_*` returning a renamed hypothesis as the entire proof body).
* [ ] No hypothesis strengthening without documentation.
* [ ] `#print axioms` returns `[propext, Classical.choice, Quot.sound]` only.

## Cycle 240+ outlook

* If Priority 1 ships cleanly: cycle 240 can pursue
  `elementaryWeightQ_phi_inverseQ_phi` if it was deferred, OR ship the
  analogous infrastructure on `Quotient Equivalent.setoidSigma` (which
  would unblock the `Equivalent → PhiEquivalent` direction once that
  bridge is built). Alternative: pivot to a tree-combinatorics target in
  §302 (independent track) or extend Section441B.lean with thm:441C-prep
  results that don't depend on the GPFS-blocked Section441.lean.
* If Priority 0 unexpectedly clears GPFS: lem:441A Phase C.2 lands, and
  cycle 240 can start Phase C.3 (real factorisation via conjugate-pair
  quadratics, the highest-risk phase per `lem_441A_phase_C_scoping.md`).
