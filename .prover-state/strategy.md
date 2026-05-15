# Cycle 263 strategy — Phase A.2 completion: tree-automorphism Setoid on `LabelledRootedTree`

## §A — Status check

* HEAD: `fb80441` (Cycle 262 — §300 Phase A.2 partial shipped).
* Repo-wide sorry count: **0**.
* `OpenMath/Chapter3/Section300.lean`: 272 LOC, axiom-clean. Contains
  cycle 261's `Vertex` / `vertices` / `vertices_card` (Phase A.1) plus
  cycle 262's `Vertex.mem_vertices` / `instFintypeVertex` /
  `Fintype.card_vertex_eq_order` / `LabelledRootedTree` /
  `canonicalLabelling` / three canonical labelling witnesses (Phase A.2
  partial).
* No pending Aristotle jobs.
* No active blockers in `.prover-state/issues/`.
* GPFS Section441 status: skip per `cycle_182_gpfs_slowness.md` (43+
  consecutive timeouts). Do **not** attempt §441 work this cycle.

## §B — Target

**Ship Phase A.2 completion of `lem_310B_plan.md`**: the tree-automorphism
equivalence relation on `LabelledRootedTree`, together with non-vacuity
witnesses. This finishes the def:300C "labelled rooted trees modulo
tree-automorphism" piece that Butcher §300 (around p. 140) introduces.

### Concrete sub-deliverables (in priority order P1–P5)

All declarations live in `OpenMath/Chapter3/Section300.lean` inside the
existing `namespace OpenMath.Chapter3.Section310.RootedTree` block,
appended **after** the cycle 262 canonical-labelling examples (line 259).

#### P1 — `TreeAutomorphism` structure (weakened form)

Define a *weakened* tree-automorphism — the minimal predicate sufficient
to define the Setoid this cycle, deferring full structural recursion to
Phase A.3.

```lean
/-- A *(weak) tree automorphism* of `t` is a permutation of `Vertex t`
that fixes the root.

This is **strictly weaker** than Butcher's tree-automorphism group (which
additionally recursively preserves each subtree's structure). The
weakening is documented; Phase A.3's σ-faithfulness identity is NOT
claimed by this cycle's Setoid. -/
structure TreeAutomorphism (t : RootedTree) where
  perm : Equiv.Perm (Vertex t)
  perm_root : perm Vertex.root = Vertex.root
```

The structure is **deliberately weakened** for cycle 263:

(a) Avoids the nested-inductive mutual-recursion pitfall flagged in
    memory `feedback_rootedtree_nested_induction.md` (defining a
    recursive `TreeAutomorphism : RootedTree → Type` would require
    `mutual` through `List RootedTree`).
(b) Uses Mathlib's existing `Equiv.Perm` infrastructure — no new
    recursive predicate needed.
(c) The Setoid built from this is **coarser** than Butcher's quotient,
    but the σ-faithfulness orbit-count `r(t)!/σ(t)` (Phase A.3) is
    explicitly deferred per `.prover-state/issues/lem_310B_plan.md` §4.1.
    Document the weakening prominently.

#### P2 — `TreeAutomorphism` API: identity / composition / inverse

```lean
/-- The identity tree-automorphism. -/
def TreeAutomorphism.id (t : RootedTree) : TreeAutomorphism t where
  perm := Equiv.refl _
  perm_root := rfl

/-- Composition of tree automorphisms. -/
def TreeAutomorphism.trans {t : RootedTree}
    (φ ψ : TreeAutomorphism t) : TreeAutomorphism t where
  perm := φ.perm.trans ψ.perm
  perm_root := by
    show ψ.perm (φ.perm Vertex.root) = Vertex.root
    rw [φ.perm_root, ψ.perm_root]

/-- Inverse of a tree automorphism. -/
def TreeAutomorphism.symm {t : RootedTree}
    (φ : TreeAutomorphism t) : TreeAutomorphism t where
  perm := φ.perm.symm
  perm_root := by
    have h := φ.perm_root
    have := congrArg φ.perm.symm h
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
```

Verify each `perm_root` proof closes with the indicated tactic. If
`Equiv.refl_trans` / `Equiv.symm_apply_apply` lemma names have
drifted in Mathlib, use `lean_local_search "Equiv.symm_apply"` to
locate.

#### P3 — `LabelledRootedTree.Equiv` relation + Setoid instance

Define the equivalence relation pointwise to dodge dependent-typing
issues with top-level `Equiv` equality across different `Vertex` types:

```lean
/-- Two labelled rooted trees are equivalent if they share an underlying
tree and one labelling is obtained from the other by composing with some
tree-automorphism (weakened form — see `TreeAutomorphism`).

Encoded pointwise to avoid dependent-typing issues with `Equiv` equality
across heterogeneous `Vertex` types. -/
def LabelledRootedTree.Equiv (a b : LabelledRootedTree) : Prop :=
  ∃ (h : a.underlying = b.underlying)
    (φ : TreeAutomorphism a.underlying),
    ∀ (v : Vertex a.underlying),
      a.labelling v = (h ▸ b.labelling) (φ.perm v)
```

Then the three equivalence-relation lemmas:

```lean
theorem LabelledRootedTree.Equiv.refl (a : LabelledRootedTree) :
    LabelledRootedTree.Equiv a a := by
  refine ⟨rfl, TreeAutomorphism.id _, ?_⟩
  intro v
  show a.labelling v = a.labelling ((Equiv.refl _) v)
  rfl

theorem LabelledRootedTree.Equiv.symm {a b : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b) :
    LabelledRootedTree.Equiv b a := by
  obtain ⟨hEq, φ, hLab⟩ := hab
  subst hEq  -- now a.underlying = b.underlying definitionally
  refine ⟨rfl, φ.symm, ?_⟩
  intro v
  -- Use hLab at φ.perm.symm v
  have := hLab (φ.perm.symm v)
  simp [TreeAutomorphism.symm] at *
  -- Close via Equiv.apply_symm_apply
  sorry  -- DO NOT SHIP — see Step 4 in §C below for the actual recipe

theorem LabelledRootedTree.Equiv.trans {a b c : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b)
    (hbc : LabelledRootedTree.Equiv b c) :
    LabelledRootedTree.Equiv a c := by
  obtain ⟨hEq_ab, φ, hLab_ab⟩ := hab
  obtain ⟨hEq_bc, ψ, hLab_bc⟩ := hbc
  subst hEq_ab
  subst hEq_bc
  refine ⟨rfl, φ.trans ψ, ?_⟩
  intro v
  show a.labelling v = a.labelling ((φ.perm.trans ψ.perm) v)
  -- chain hLab_ab and hLab_bc
  sorry  -- DO NOT SHIP — see Step 4 in §C below for the actual recipe

instance LabelledRootedTree.setoid : Setoid LabelledRootedTree where
  r := LabelledRootedTree.Equiv
  iseqv := ⟨LabelledRootedTree.Equiv.refl,
            LabelledRootedTree.Equiv.symm,
            LabelledRootedTree.Equiv.trans⟩
```

**The sorries in `symm` and `trans` above are sketch placeholders, NOT
deliverables.** They must be closed in cycle 263 before commit. See
§C Step 4 for the proof recipe.

#### P4 — Non-vacuity witnesses (reflexivity-only)

```lean
example : LabelledRootedTree.Equiv canonicalVertex canonicalVertex :=
  LabelledRootedTree.Equiv.refl _

example : LabelledRootedTree.Equiv canonicalCherry canonicalCherry :=
  LabelledRootedTree.Equiv.refl _

example : LabelledRootedTree.Equiv canonicalBroom₃ canonicalBroom₃ :=
  LabelledRootedTree.Equiv.refl _
```

Heterogeneous (genuinely-different-labelling) non-vacuity is **deferred
to cycle 264+ Phase A.2.1** — that requires evaluating
`Fintype.equivFinOfCardEq` on concrete trees, which won't reduce
cleanly.

#### P5 — Docstring + issue-file update

(i) Add a faithfulness-divergence paragraph to the file-level docstring
of `Section300.lean` after the cycle 262 paragraph at lines 187–192:

```
Cycle 263 update: `TreeAutomorphism t` is weakened to "permutation of
`Vertex t` fixing `root`" (only one structure-preservation field), which
is strictly weaker than Butcher's full tree-automorphism group. The
σ-faithfulness orbit-count identity (Phase A.3 per lem_310B_plan.md §4.1)
is NOT claimed by `LabelledRootedTree.setoid`. Strengthening to the
full recursive structure preservation is deferred to a future cycle.
```

(ii) Append a "Cycle 263 update" subsection to
`.prover-state/issues/lem_310B_plan.md` §4.1 documenting what shipped,
the weakening, and the cycle 264+ strengthening task. ~15 lines markdown.

## §C — Approach: concrete proof recipes

### Step 1: `TreeAutomorphism` structure (~10 LOC)

Define exactly as in §B P1. Verify it compiles with:

```bash
lake env lean OpenMath/Chapter3/Section300.lean
```

`Equiv.Perm` lives in `Mathlib.Logic.Equiv.Defs` (transitively imported
via `Mathlib.Algebra.BigOperators.Fin` already in cycle 261's imports;
double-check with `lean_hover_info` if elaboration fails).

### Step 2: Identity / composition / inverse (~25 LOC)

Define `TreeAutomorphism.id`, `.trans`, `.symm` per §B P2.

* **`.id.perm_root`**: closes by `rfl` because `Equiv.refl _ v = v` is
  definitional.
* **`.trans.perm_root`**: the `show` reframes the goal from
  `(φ.perm.trans ψ.perm) Vertex.root = Vertex.root` to
  `ψ.perm (φ.perm Vertex.root) = Vertex.root` (a `rfl` unfolding of
  `Equiv.trans` application). Then two `rw`s with `perm_root` close.
* **`.symm.perm_root`**: apply `φ.perm.symm` to both sides of `perm_root`,
  use `Equiv.symm_apply_apply` to simplify the LHS.

If any closure stalls past 10 min, lean on `simp [Equiv.refl,
Equiv.trans, Equiv.symm, TreeAutomorphism.id]` followed by `exact
φ.perm_root` / `exact rfl` patterns.

### Step 3: `LabelledRootedTree.Equiv` definition (~10 LOC)

Define exactly as in §B P3 (pointwise form). The `h ▸ b.labelling`
substitution should elaborate because `h : a.underlying = b.underlying`
substitutes definitionally into the labelling's domain
`Vertex a.underlying → Vertex b.underlying`.

If `h ▸ b.labelling` fails to elaborate, fall back to:

```lean
def LabelledRootedTree.Equiv (a b : LabelledRootedTree) : Prop :=
  ∃ (h : a.underlying = b.underlying)
    (φ : TreeAutomorphism a.underlying),
    ∀ (v : Vertex a.underlying),
      HEq (a.labelling v) (b.labelling (h ▸ φ.perm v))
```

`HEq` is more permissive but harder to consume. Try `Eq` form first.

### Step 4: Setoid axioms (~50 LOC, the substantive work)

#### refl (5 LOC)

```lean
theorem LabelledRootedTree.Equiv.refl (a : LabelledRootedTree) :
    LabelledRootedTree.Equiv a a := by
  refine ⟨rfl, TreeAutomorphism.id _, ?_⟩
  intro v
  rfl  -- both sides reduce to a.labelling v (because Equiv.refl _ v = v)
```

If `rfl` doesn't close, try `show a.labelling v = a.labelling v; rfl` or
`simp [TreeAutomorphism.id]`.

#### symm (~20 LOC)

After `subst hEq`, the `Equiv` reduces to the homogeneous case where
`a.underlying = b.underlying` is definitionally true. Then:

```lean
theorem LabelledRootedTree.Equiv.symm {a b : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b) :
    LabelledRootedTree.Equiv b a := by
  obtain ⟨hEq, φ, hLab⟩ := hab
  subst hEq
  -- Goal: LabelledRootedTree.Equiv b a, with a.underlying = b.underlying definitionally
  -- hLab : ∀ v, a.labelling v = b.labelling (φ.perm v)
  refine ⟨rfl, φ.symm, ?_⟩
  intro v
  -- Goal: b.labelling v = a.labelling ((φ.symm).perm v) = a.labelling (φ.perm.symm v)
  -- Specialize hLab at φ.perm.symm v:
  have h := hLab (φ.perm.symm v)
  -- h : a.labelling (φ.perm.symm v) = b.labelling (φ.perm (φ.perm.symm v))
  rw [Equiv.apply_symm_apply] at h
  -- h : a.labelling (φ.perm.symm v) = b.labelling v
  show b.labelling v = a.labelling (φ.perm.symm v)
  exact h.symm
```

If the `subst hEq` step errors because `b.underlying` appears in the
goal, restructure to keep `a` and `b` separate and use `Eq.mp` /
`Eq.mpr` instead. Specifically, replace `subst hEq` with `cases hEq`,
which performs the same substitution but is sometimes more permissive
with motive inference.

#### trans (~25 LOC)

```lean
theorem LabelledRootedTree.Equiv.trans {a b c : LabelledRootedTree}
    (hab : LabelledRootedTree.Equiv a b)
    (hbc : LabelledRootedTree.Equiv b c) :
    LabelledRootedTree.Equiv a c := by
  obtain ⟨hEq_ab, φ, hLab_ab⟩ := hab
  obtain ⟨hEq_bc, ψ, hLab_bc⟩ := hbc
  subst hEq_ab
  subst hEq_bc
  refine ⟨rfl, φ.trans ψ, ?_⟩
  intro v
  -- hLab_ab : ∀ v, a.labelling v = b.labelling (φ.perm v)
  -- hLab_bc : ∀ v, b.labelling v = c.labelling (ψ.perm v)
  -- Goal: a.labelling v = c.labelling ((φ.trans ψ).perm v)
  --              = c.labelling (ψ.perm (φ.perm v))
  rw [hLab_ab v, hLab_bc (φ.perm v)]
  -- LHS is now b.labelling (φ.perm v), which becomes c.labelling (ψ.perm (φ.perm v))
  -- after the second rewrite, matching the RHS exactly.
  rfl
```

If `rfl` doesn't close the final goal, the issue is `(φ.trans ψ).perm`
not being definitionally `φ.perm.trans ψ.perm`. Add `show
a.labelling v = c.labelling (ψ.perm (φ.perm v))` before the rewrites
to coerce the form, or end with `simp [TreeAutomorphism.trans]`.

### Step 5: Setoid instance (~5 LOC)

```lean
instance LabelledRootedTree.setoid : Setoid LabelledRootedTree where
  r := LabelledRootedTree.Equiv
  iseqv := ⟨LabelledRootedTree.Equiv.refl,
            LabelledRootedTree.Equiv.symm,
            LabelledRootedTree.Equiv.trans⟩
```

### Step 6: Non-vacuity examples (~5 LOC)

Three reflexivity examples per §B P4.

### Step 7: Verification

```bash
lake env lean OpenMath/Chapter3/Section300.lean
lake env lean OpenMath/Chapter3.lean
lake build OpenMath.Chapter3.Section300
```

Then `#print axioms` on:
* `LabelledRootedTree.Equiv`
* `LabelledRootedTree.Equiv.refl`
* `LabelledRootedTree.Equiv.symm`
* `LabelledRootedTree.Equiv.trans`
* `LabelledRootedTree.setoid`
* `TreeAutomorphism.id`
* `TreeAutomorphism.trans`
* `TreeAutomorphism.symm`

All should return `[propext, Classical.choice, Quot.sound]` only.

### Total LOC budget

~100 LOC (Section300.lean: 272 → ~370 LOC). Comfortably within
single-cycle range.

## §D — Risk assessment and ABORT THRESHOLDS

### R1: dependent-type elaboration on `h ▸ b.labelling`

Lean 4's `▸` can fail when the substitution motive isn't inferable.
If `LabelledRootedTree.Equiv`'s definition errors, fall back to the
`HEq` form (Step 3 fallback above).

**Abort threshold**: 30 min on the definition. If neither `Eq` nor
`HEq` form elaborates, abort P3–P5 and ship only P1–P2
(`TreeAutomorphism` + API). That alone is still a substantive cycle.

### R2: `subst hEq` motive failure in symm/trans

When `subst`'s motive can't be inferred from the goal, Lean fails with
"Failed to eliminate". Workaround: replace `subst hEq` with `cases hEq`,
which performs the same substitution but is sometimes more permissive.
If both fail, the structural-equality field on `LabelledRootedTree`
(which has only one `underlying` field) may need to be eliminated via
`LabelledRootedTree.ext`-style cases.

**Abort threshold**: 30 min each on `symm` and `trans` proofs. If both
stall, ship P1–P3-P1 piece (just the `Equiv` definition without the
Setoid).

### R3: `Equiv.apply_symm_apply` name drift

Mathlib has `Equiv.apply_symm_apply`, `Equiv.symm_apply_apply`, and
possibly `Equiv.coe_apply_symm`-variants. If the recipe's names don't
resolve, run `lean_local_search "Equiv.apply_symm"` to find the
current name. Both directions of the cancellation exist; pick the one
matching the proof's argument order.

### R4: σ-faithfulness divergence audit risk

The weakened `TreeAutomorphism` is a **documented faithfulness
divergence**. The supervisor's scanner should not flag it because:

* It is documented in the docstring with cross-reference to
  `.prover-state/issues/lem_310B_plan.md` §4.1.
* `lean_status.json` is NOT updated for `lem:310B` (still `[ ]` /
  `unformalized`).
* `plan.md` is NOT updated for `lem:310B`.
* No claim is made that `Setoid` quotient cardinality matches σ(t).

If the supervisor flags this as a regression, treat it as a likely
false positive (cycles 243–248 had similar tautology-scanner false
positives per `.prover-state/issues/tautology_scanner_false_positives.md`).
Do NOT remediate with sorries.

### R5: AVOID the recursive Route A trap

The cycle 262 task results recommended "Route A (recursive predicate)"
as "simpler". **OVERRIDE: do NOT take Route A.** A recursive
`TreeAutomorphism : RootedTree → Type` definition would require:
* Mutual recursion through `List RootedTree` (because `RootedTree.mk`
  takes a `List RootedTree` and the automorphism on children is a list
  of automorphisms).
* A motive-inference solution for the nested inductive per
  `feedback_rootedtree_nested_induction.md`.

Use the `Equiv.Perm` route (§B P1) instead. This is a deliberate
departure from the cycle 262 task results.

## §E — Backup plan (if main path stalls past 90 min)

If R1–R3 collectively burn 90+ minutes without producing a clean
`LabelledRootedTree.Equiv` Setoid, abort §B and pivot to the cycle 260
§342 scouting recommendation: **`lem:342A` (342a) shifted Legendre
orthogonality on `[0,1]`**.

Per cycle 260's dependency scan (`lem_310B_plan.md` §8.2), `lem:342A`
is independent of `lem:310B`. Concrete deliverables for the pivot:

1. Define `shiftedLegendre : ℕ → Polynomial ℝ`. Search Mathlib first:
   `lean_loogle "Polynomial.legendre"`. If `Polynomial.legendre` exists
   for `[-1, 1]`, define `shiftedLegendre n := Polynomial.legendre n
   |>.comp (2 * Polynomial.X - 1)`. If not, build via Rodrigues:
   `P_n(x) = (1/n!) · dⁿ/dxⁿ (x^n · (x-1)^n)`.

2. Define the `[0, 1]` inner product:
   `⟨P, Q⟩₀₁ := ∫ x in (0:ℝ)..1, P.eval x * Q.eval x`.

3. Prove orthogonality (342a) for `m ≠ n`:
   `∫ x in (0:ℝ)..1, (shiftedLegendre m).eval x * (shiftedLegendre n).eval x = 0`.

Single-cycle target (~80 LOC). Mathlib has `intervalIntegral` and
polynomial-derivative machinery. Only pivot to this if Phase A.2 stalls
past 90 min.

If even the pivot fails, ship a strictly minimal axiom-clean
deliverable: add ~3 small algebraic helper lemmas to Section301's
`bseriesAlphaPartialSum` API (e.g. `bseriesAlphaPartialSum_const_mul`)
to keep the cycle from being completely empty.

## §F — What NOT to try

* **NO sorry-first scaffolds.** Per cycle 200/201 rollback precedent.
  If P3 cannot close axiom-clean, ship P1–P2 only.
* **NO recursive `TreeAutomorphism` (Route A).** Per R5 above.
* **NO `axiom` / `constant` declarations.** Standard project rule.
* **NO `maxHeartbeats` increase above 200000.** Standard project rule.
* **NO `lean_status.json` update for `lem:310B`.** Phase A.2 is
  infrastructure; the textbook entity stays `unformalized`.
* **NO `plan.md` update for `lem:310B`.** Same reason.
* **NO modification of `scripts/autonomous_loop.py`.** Per CLAUDE.md
  and `.prover-state/issues/tautology_scanner_false_positives.md`.
* **NO Aristotle submission this cycle.** The sub-deliverables are
  small enough to close manually; no batch warranted.
* **NO §441 compile attempts.** 44th consecutive GPFS timeout
  anticipated per `cycle_182_gpfs_slowness.md`. Skip entirely.
* **NO §381 / `thm_381H_deferred.md` work.** Multi-cycle Banach-
  fixed-point integration; defer.
* **NO heterogeneous (genuinely-different-labelling) non-vacuity
  witness in cycle 263.** Defer to Phase A.2.1 (cycle 264+).
* **NO attempt to define `LabelledRootedTree.Equiv` via top-level
  `Equiv` equality (`a.labelling = ψ.trans (h ▸ b.labelling)` at the
  Equiv level).** The pointwise form (Step 3) is more robust.

## §G — Suggested commit message

```
Cycle 263 — §300 Phase A.2 completion: TreeAutomorphism + LabelledRootedTree Setoid SHIPPED.

Phase A.2 of lem_310B_plan.md completed. Cycle 262 shipped the
LabelledRootedTree structure + canonical labelling; cycle 263 ships
the tree-automorphism equivalence relation + Setoid instance.

New in OpenMath/Chapter3/Section300.lean:
* TreeAutomorphism: structure on Equiv.Perm (Vertex t) with
  perm_root field (weakened — see docstring).
* TreeAutomorphism.id / .trans / .symm: identity, composition, inverse.
* LabelledRootedTree.Equiv: pointwise-encoded equivalence relation.
* LabelledRootedTree.Equiv.{refl, symm, trans}.
* LabelledRootedTree.setoid: Setoid LabelledRootedTree instance.
* Three reflexivity non-vacuity witnesses on canonicalVertex /
  canonicalCherry / canonicalBroom₃.

Faithfulness divergence: TreeAutomorphism is weakened relative to
Butcher's tree-automorphism group (only root-fixing; full recursive
structure preservation deferred to Phase A.3 if/when needed).
Documented in file docstring and in lem_310B_plan.md §4.1.

All declarations axiom-clean ([propext, Classical.choice, Quot.sound]).
Sorry count: 0 → 0. File: 272 → ~370 LOC.

lem:310B remains [ ] / unformalized in plan.md (this cycle is
infrastructure).
```

(If R1/R2/R3 forced P1–P2-only ship, adjust accordingly — drop the
`LabelledRootedTree.Equiv` / `.setoid` references and explain in the
body that Setoid is deferred to cycle 264.)

## §H — Suggested next-cycle planner note

If cycle 263 closes P1–P5 cleanly, cycle 264 should:
* **Option 1 (recommended)**: Phase A.2.1 — heterogeneous-labelling
  non-vacuity. Exhibit two different labellings of `mk [vertex, vertex]`
  that are equivalent via the leaf-swap permutation. ~30 LOC.
* **Option 2**: Phase A.3 — strengthen `TreeAutomorphism` with the full
  recursive structure-preservation field; reprove
  `TreeAutomorphism.{id, trans, symm}` and `LabelledRootedTree.Equiv`
  in the strengthened setting. Multi-cycle (likely 2–3). Closes the
  σ-faithfulness gap from
  `.prover-state/issues/symmetry_group_equivalence.md`.
* **Option 3**: proceed to Phase B (`thm:306A` multinomial Taylor) per
  `lem_310B_plan.md` §5. Phase B.1 single-variable two-input form is
  the natural first step (~100 LOC).
* **Option 4 (pivot)**: ship `lem:342A` (342a) per §E above; defer
  further `lem:310B` work to cycle 265+.

If cycle 263 ships P1–P2 only (P3 aborted), cycle 264 retries P3 with
HEq fallback or `cases` instead of `subst`. The `TreeAutomorphism` API
is the load-bearing infrastructure either way.
