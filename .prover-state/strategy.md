# Cycle 249 Strategy

## TL;DR

Cycle 248 SHIPPED cleanly (`Section311.lean` axiom-clean, sorry count 0,
`lem_311A_order_one` plus B-series infrastructure). The cycle-248 supervisor
score of `+2` indicates a clean ship; the "stuck on" field is empty in this
prompt for a reason — there is nothing to remediate.

**Cycle 249 target**: ship `RootedTree.theta_eq_one` in
`OpenMath/Chapter3/Section310.lean` — a foundation lemma for the eventual
`lem:310B` (Elementary Differential Weight Formula). This is the cycle-248
consultant's **Option 1** recommendation: a clean, low-risk, ~40 LOC
single-cycle deliverable that builds the next layer of the §310/§311/§312
cascade.

**Sorry budget**: 0 → 0. No new sorries; no `axiom` declarations; no
`maxHeartbeats` bumps.

**Aristotle**: no submission this cycle. The proof is short enough that
manual closure is faster than the 30-minute Aristotle cadence.

---

## §A — Aristotle results to incorporate

**None.** No pending Aristotle jobs.

---

## §B — The target

### B.1 — Mathematical content

Define a recursive weight function `theta : RootedTree → ℝ` and prove it
is identically 1:

```lean
mutual
  def theta : RootedTree → ℝ
    | mk children => thetaProd children
  def thetaProd : List RootedTree → ℝ
    | [] => 1
    | t :: ts => theta t * thetaProd ts
end

theorem thetaProd_eq_map_prod (children : List RootedTree) :
    thetaProd children = (children.map theta).prod := by
  induction children with
  | nil => rfl
  | cons t ts ih => simp [thetaProd, ih]

theorem theta_eq_one : ∀ t : RootedTree, theta t = 1 := by
  intro t
  induction t with
  | mk children ih =>
    rw [theta, thetaProd_eq_map_prod]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, hceq⟩ := hx
    rw [← hceq]
    exact ih c hc
```

### B.2 — Why this is foundation, NOT `lem:310B`

Butcher's `lem:310B` (Elementary Differential Weight Formula, §310) is a
**non-trivial** sum identity relating elementary differentials at a smooth
function to a sum over labelled trees. It requires:
1. An elementary weight function `α : RootedTree → ℝ` (not yet defined).
2. A multi-tree-sum formula involving `α(t)` × `σ(t)` × `F(t)(y)`.

`RootedTree.theta` is the trivial **identically-1 elementary weight of
the exact-solution operator `E`** (Butcher §312, prerequisite for
`def:312A`). The recursive form `θ(mk children) = ∏ θ(cᵢ)` matches the
tree-product structure of the exact-solution group, and the closure
`θ ≡ 1` is the canonical scaffold the future `α(t)`-machinery will
compose with.

**This is NOT a textbook entity.** `lean_status.json` row for `lem:310B`
stays at `unformalized`. `plan.md` row stays at `[ ]`. No entity-status
update this cycle.

### B.3 — File location

**Insert in `OpenMath/Chapter3/Section310.lean`** (NOT a new file, NOT
`Section311.lean`). Place inside `namespace RootedTree` (lines 86–120),
after the existing `vertex` / `cherry` / `broom₃` examples (around line 99).

The cycle-017 `density_eq` proof at
`OpenMath/Chapter3/Section301.lean:123–155` is the canonical template.
Read it before writing — the mutual recursion + list-helper +
`_eq_map_prod` bridge + induction pattern transfers verbatim.

---

## §C — Concrete tactic recipe

### Step 1 — Read the template (5 min)

```bash
Read OpenMath/Chapter3/Section301.lean lines 123–155
```

Note the exact shape:
* `mutual` block with `density` (per-tree) and `densityProd` (list helper).
* `densityProd_eq_map_prod` bridge collapsing the recursive helper to
  `List.prod`.
* `density_eq` reformulation in `List.prod` form (uses `show` to expose
  the inner recursion before `rw`).

For `theta`, we DROP the `density_eq` step because `theta` is constantly 1
— we go straight to `theta_eq_one`.

### Step 2 — Write `theta` + `thetaProd` (10 min)

Insert into `OpenMath/Chapter3/Section310.lean` immediately before
`end RootedTree` (around line 120):

```lean
/- ### `θ(t)` — exact-solution operator weight

Recursive scaffold for the §312 elementary-weight machinery. By
construction `θ(t) = 1` for every rooted tree; the recursive form
`θ(mk children) = ∏ θ(cᵢ)` matches the tree-product structure of the
exact-solution group `E`.

This is **NOT** the textbook `lem:310B` (Elementary Differential Weight
Formula), which requires a separate `α : RootedTree → ℝ` definition and
a non-trivial sum identity. `theta` is the trivial-weight scaffold that
the future `α(t)`-machinery will compose with. -/

mutual
  /-- The (trivial) exact-solution operator weight `θ(t)`.

  Defined recursively as `θ(τ) = 1` and `θ([t₁, …, t_m]) = ∏ᵢ θ(tᵢ)`.
  See `theta_eq_one` for the closure `∀ t, θ(t) = 1`. -/
  def theta : RootedTree → ℝ
    | mk children => thetaProd children
  /-- Running product of `theta` over a list of subtrees. -/
  def thetaProd : List RootedTree → ℝ
    | [] => 1
    | t :: ts => theta t * thetaProd ts
end
```

### Step 3 — Bridge lemma `thetaProd_eq_map_prod` (5 min)

```lean
/-- `thetaProd cs` collapses to the standard `(cs.map theta).prod`. -/
theorem thetaProd_eq_map_prod (children : List RootedTree) :
    thetaProd children = (children.map theta).prod := by
  induction children with
  | nil => rfl
  | cons t ts ih => simp [thetaProd, ih]
```

Verbatim from cycle 017's `densityProd_eq_map_prod` (Section301.lean:142).

### Step 4 — Closure `theta_eq_one` (15 min)

```lean
/-- The exact-solution operator weight is identically 1. -/
theorem theta_eq_one : ∀ t : RootedTree, theta t = 1 := by
  intro t
  induction t with
  | mk children ih =>
    rw [theta, thetaProd_eq_map_prod]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, hceq⟩ := hx
    rw [← hceq]
    exact ih c hc
```

**Critical**: the induction principle for `RootedTree` produces, in the
`mk children` case, a hypothesis `ih : ∀ c ∈ children, theta c = 1`.
Confirm by reading cycle 017's `density_eq` (Section301.lean:150) — same
pattern.

If `List.prod_eq_one` fires with a different signature than expected, see
Backup B.1 below.

### Step 5 — Non-vacuity witnesses (5 min)

After `theta_eq_one`, add three `example` lines exercising the closure:

```lean
example : theta vertex = 1 := theta_eq_one _
example : theta cherry = 1 := theta_eq_one _
example : theta broom₃ = 1 := theta_eq_one _
```

These should close by direct citation.

### Step 6 — Verification (5 min)

```bash
lake env lean OpenMath/Chapter3/Section310.lean
lake env lean OpenMath/Chapter3.lean
```

Both should exit 0 in <30 s. Then axiom-check via `lean_verify` or
`#print axioms` on `theta_eq_one` and `thetaProd_eq_map_prod`. Expected:
`[propext, Classical.choice, Quot.sound]` only.

### Step 7 — Tautology-scanner check

```bash
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section310.lean
```

Expected: no hits. The recipe above uses `exact ih c hc` and `apply
List.prod_eq_one`, neither matches the regex (no `h_` prefix; not bare
`id`).

### Step 8 — Task results + commit (15 min)

Write `.prover-state/task_results/cycle_249.md` with:
* Worked on: `RootedTree.theta_eq_one` (lem:310B foundation)
* Approach: mutual recursion + list-helper + `List.prod_eq_one` induction
  (verbatim port of cycle 017's `density_eq` template)
* Result: SUCCESS, axiom-clean, ~40 LOC delta
* **Faithfulness check**: explicitly note that this is NOT the textbook
  `lem:310B`. The proof produces `θ ≡ 1` recursively; `lem:310B`'s
  textbook content (the non-trivial sum identity with `α(t)` weights)
  remains `unformalized`. No `lean_status.json` or `plan.md` row changes.

Commit message:

```
Cycle 249 — §310 theta_eq_one (lem:310B foundation) SHIPPED.

Recursive RootedTree → ℝ weight function `theta`, the trivial
exact-solution operator weight. Headline `theta_eq_one` closes via
induction on RootedTree using cycle-017's density_eq template.
Foundation for the future lem:310B α(t)-machinery; not the textbook
lemma itself (lean_status unchanged).

* theta, thetaProd (mutual recursion)
* thetaProd_eq_map_prod (list-helper → List.prod bridge)
* theta_eq_one (closure via List.prod_eq_one + RootedTree induction)
* 3 non-vacuity witnesses (vertex, cherry, broom₃)

Axiom-clean ([propext, Classical.choice, Quot.sound]).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
```

---

## §D — What NOT to try

1. **Do NOT name the deliverable `lem_310B`.** The textbook `lem:310B`
   is a stronger statement (non-trivial sum identity with `α(t)` weights
   over labelled trees). Use `theta_eq_one` or `exactSolutionWeight_eq_one`.
   `lean_status.json` for `lem:310B` stays `unformalized`.

2. **Do NOT put this in `Section311.lean` or a new file.** `theta` is a
   combinatorial weight on `RootedTree`, conceptually paired with
   `density`/`symmetry` from `Section301.lean` and the `elementaryDiff`
   from `Section310.lean`. The right home is `Section310.lean` inside
   `namespace RootedTree`.

3. **Do NOT attempt `lem_311A_order_two` (Option 2 from cycle-248
   consultant).** It requires:
   - An `iteratedFDeriv ℝ 1 f y₀ ↔ fderiv ℝ f y₀` bridge (Mathlib
     coercion bookkeeping, high risk).
   - A chain-rule helper for `iteratedDeriv 2 yex x₀ = fderiv f y₀ (f y₀)`
     (re-usable but adds scope).
   - `taylor_isLittleO (n := 3)` instead of `(n := 2)` (changes residual
     shape).
   - Likely strengthening `ContDiff ℝ 2 yex` to `ContDiff ℝ 3 yex`.
   This is **2-cycle risk**; defer to cycle 250+.

4. **Do NOT attempt the full textbook `lem:311A`** (combinatorial
   labelling over `T_S^*`). Requires `def:300C` labelled-tree quotients;
   multi-cycle.

5. **Do NOT attempt `lem:310B` directly.** Requires `α : RootedTree → ℝ`
   + the multi-tree-sum formula; multi-cycle.

6. **Do NOT attempt the `Equivalent → PEquivalent` or
   `PhiEquivalent → PEquivalent` thm:381H bridges** (deferred per
   `.prover-state/issues/thm_381H_deferred.md`).

7. **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
   43+ consecutive GPFS-blocked timeouts since cycle 182. Skip per
   `.prover-state/issues/cycle_182_gpfs_slowness.md`.

8. **Do NOT raise `maxHeartbeats` above 200000.** If the
   `RootedTree.induction` step stalls, look for a name-resolution issue
   (e.g. `List.prod_eq_one` not in scope) rather than reaching for
   heartbeat bumps. The proof is ~10 LOC and should compile in <1 s.

9. **Do NOT introduce `axiom`/`constant` declarations.**

10. **Do NOT introduce sorries.** Cycles 149 / 200 / 201 all rolled back
    sorry-first scaffolds; cycle 249's deliverable must be axiom-clean or
    skipped entirely.

11. **Do NOT edit `scripts/autonomous_loop.py`** or the prompt-builder.
    Tautology-scanner false positives are loop-maintainer territory per
    `.prover-state/issues/tautology_scanner_false_positives.md`.

12. **Do NOT attempt the 4-stage refactor of `Section319.lean`** (Option
    3 from the consultant). It's a backup-only deliverable to use if
    Option 1 stalls — which it shouldn't, given the verbatim cycle-017
    template. Reserve for a future "refactor" cycle.

---

## §E — Backup paths (if Step 4 stalls)

### Backup B.1 — `List.prod_eq_one` signature drift

If `apply List.prod_eq_one` fails (signature mismatch), try the alternate
direct list-induction:

```lean
theorem theta_eq_one : ∀ t : RootedTree, theta t = 1 := by
  intro t
  induction t with
  | mk children ih =>
    rw [theta, thetaProd_eq_map_prod]
    -- Direct list-induction fallback
    clear ih  -- placeholder; preserve ih and pass it through
    -- Better: inline a helper proving (children.map theta).prod = 1
    -- under the hypothesis (∀ c ∈ children, theta c = 1).
    sorry  -- DO NOT SHIP; this branch is fallback only
```

Better fallback: prove a small helper first:

```lean
private theorem prod_eq_one_of_forall_eq_one (l : List ℝ)
    (h : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons]
    rw [h x (List.mem_cons_self x xs), one_mul]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
```

Then close `theta_eq_one` via `apply prod_eq_one_of_forall_eq_one`.

Verify which form fires by `lean_loogle "List.prod = 1"` BEFORE committing
to either path. If Mathlib already has it under a different name (e.g.
`List.prod_eq_one_iff_forall`), use that directly.

### Backup B.2 — `RootedTree.induction` motive issue

If the `induction t with | mk children ih =>` pattern produces a
non-standard motive, fall back to explicit `RootedTree.recOn`:

```lean
theorem theta_eq_one : ∀ t : RootedTree, theta t = 1 := by
  intro t
  refine RootedTree.recOn t (motive := fun t => theta t = 1) ?_
  intro children ih
  -- continue as in main recipe
  rw [theta, thetaProd_eq_map_prod]
  ...
```

This should NOT be needed — cycle 017's `density_eq` proves the
auto-generated induction principle works correctly for this exact shape.

### Backup B.3 — Section319 helper extraction (if Option 1 completely fails)

Only if Option 1 stalls after both backup B.1 and B.2 fail (which would
be surprising):

Extract the three private helpers from `Section319.lean`
(`geometric_sum_one_plus_pos`, `geometric_sum_one_plus_zero`,
`pow_one_add_le_exp`) into a fresh `OpenMath/Helpers/GeometricExp.lean`
module and re-import. Zero new mathematical content, but a clean
refactor. ~120 LOC moved + 3 imports updated.

Do **not** pursue this proactively — it's a fallback only.

---

## §F — Decision tree

```
START
  │
  ├─→ Step 1: Read cycle 017 density_eq template (5 min)
  │      │
  │      ▼
  ├─→ Step 2-4: Write theta + thetaProd + thetaProd_eq_map_prod + theta_eq_one (30 min)
  │      │
  │      ├── Step 4 stalls on List.prod_eq_one? ──→ Backup B.1 (private helper)
  │      │
  │      ├── Step 4 stalls on RootedTree induction? ──→ Backup B.2 (RootedTree.recOn)
  │      │
  │      ├── Both backups fail (unexpected)? ──→ Backup B.3 (Section319 refactor)
  │      │
  │      ▼
  ├─→ Step 5: Add 3 non-vacuity examples (5 min)
  │      │
  │      ▼
  ├─→ Step 6-7: Verify (lake env lean, #print axioms, scanner) (10 min)
  │      │
  │      ▼
  └─→ Step 8: Write cycle_249.md + commit (15 min)

Total: ~70 min for primary path.
```

---

## §G — Success criteria

A successful cycle 249 ships:
1. `theta`, `thetaProd` (mutual recursion).
2. `thetaProd_eq_map_prod` (bridge).
3. `theta_eq_one` (closure).
4. 3 non-vacuity witnesses.
5. All axiom-clean (`[propext, Classical.choice, Quot.sound]`).
6. Sorry count: 0 → 0.
7. ~40 LOC delta in `OpenMath/Chapter3/Section310.lean`.
8. No `lean_status.json` or `plan.md` row changes.
9. No new files.
10. `cycle_249.md` task results documenting the deliverables and the
    faithfulness divergence (this is NOT textbook `lem:310B`).

Cycle 248 was a clean ship. Cycle 249 should be too.
