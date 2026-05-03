# Strategy for cycle 083

## TL;DR

The cycle 082 worker recommended `lem:322A` (Methods of order 4) for
cycle 083 because it appeared "unformalized" in `plan.md`. It is in
fact **already formalized** — see
`OpenMath/Chapter3/Section322.lean` (`order_four_block_zero_decomposition`)
and `extraction/formalization_data/lean_status.json` (line 280)
which records `"status": "formalized"`. `plan.md` has a stale `[ ]`
marker that was missed during a prior cycle's housekeeping.

The cycle's deliverable splits into two priorities:

1. **Priority 0 (housekeeping, ~5 min)** — fix the stale `plan.md`
   row for `lem:322A`.
2. **Priority 1 (substantive, ~1 cycle)** — open **Chapter 5** with
   `def:510A` (preconsistency vector for GLMs): introduce the
   `GeneralLinearMethod` structure, the `IsPreconsistent` predicate,
   and a concrete non-vacuity witness.

Chapter 5 is currently 0/35. `def:510A` is the canonical
chapter-opener and depends only on `def:404A` (already done in
`OpenMath/Chapter4/Section404.lean`). Standard "definition + witness"
cycle pattern, identical in shape to cycles 020/027/029/030.

There are no Aristotle results pending. There are no current sorries
to incorporate (cycle 082 closed all four bonus theorems clean and
left zero sorries in `Section383.lean`).

---

## Priority 0 — Housekeeping (do first, ~5 min)

### 0a. Fix stale `plan.md` marker for `lem:322A`

In `plan.md`, the Chapter 3 listing has

```
- [ ] `lem:322A` **Methods of order 4** (§322)
```

but `lean_status.json:280` records:

```json
"lem:322A": {
  "lean_file": "OpenMath/Chapter3/Section322.lean",
  "lean_symbol": "OpenMath.Chapter3.Section322.order_four_block_zero_decomposition",
  "status": "formalized"
}
```

and the file is a complete proof with no sorries (verify with
`lake env lean OpenMath/Chapter3/Section322.lean`).

**Edit `plan.md`** to change the row to:

```
- [x] `lem:322A` **Methods of order 4** (§322) — `OpenMath/Chapter3/Section322.lean`
```

Also bump the **Progress** counter from `53 / 175` to `54 / 175`
(remove the inconsistency — `lean_status.json` already records
`lem:322A` formalized, and the per-chapter total of 92 in Ch.3 means
the global counter has been one short for some time).

### 0b. Sanity-check the formalized `Section322.lean` axiom set

```
#print axioms OpenMath.Chapter3.Section322.order_four_block_zero_decomposition
```

Expected: `[propext, Classical.choice, Quot.sound]`. If anything
else appears, escalate as a separate issue — but cycle 082's worker
ran a similar check and got the standard set, so this should be a
no-op.

### 0c. Sweep `plan.md` for other stale `[ ]` rows

While editing `plan.md`, grep for any other rows whose entity ID
appears in `lean_status.json` with `"status": "formalized"` but is
still marked `[ ]` (or vice versa). The worker should fix every
such row in this cycle's commit. If more than 2-3 rows turn up,
note them in `task_results/cycle_083.md` so the loop maintainer can
audit the planner/evaluator's status-reporting.

Quick command (for the worker's reference, not literally):
```bash
python3 -c "
import json, re
status = json.load(open('extraction/formalization_data/lean_status.json'))
formalized_ids = {k for k, v in status.items() if v.get('status') == 'formalized'}
plan = open('plan.md').read()
for line in plan.splitlines():
    m = re.search(r'^- \[([x ~!])\] \`([^\`]+)\`', line)
    if not m: continue
    mark, eid = m.group(1), m.group(2)
    if eid in formalized_ids and mark == ' ':
        print('STALE [ ] should be [x]:', eid)
    if eid not in formalized_ids and mark == 'x':
        print('STALE [x] should be [ ]:', eid)
"
```

---

## Priority 1 — `def:510A` preconsistency vector for GLMs

### Why this target

* `def:510A` is a leaf in Chapter 5: depends only on `def:404A`
  (done in `OpenMath/Chapter4/Section404.lean`).
* It is the **canonical Chapter-5 chapter-opener** — it introduces
  the foundational `GeneralLinearMethod` structure that every other
  Chapter-5 entity builds on (`def:510B`, `def:510C`, `def:512A`,
  `def:520A`, etc.).
* Standard "definition + non-vacuity witness" cycle pattern,
  matching the shape of:
  * Cycle 020 (`def:381C`, `def:381D`)
  * Cycle 027 (`def:370A`)
  * Cycle 029 (`def:356B` + DJ-irreducibility component of `def:356A`)
  * Cycle 030 (`def:381A` + explicit-Euler witness)
  * Cycle 038 (`def:402A` + helper lemmas)
* Avoids every blocker that ruled out other Chapter-3 / Chapter-5
  candidates:
  * **Not `lem:322A`** — already formalized.
  * **Not `def:381F`** — needs the deferred `reducedMethod`
    construction (`reduced_method_deferred.md`).
  * **Not `def:422B` / `thm:422A` / `thm:422C`** — these embed the
    convolution group `G₁` in their *definitions*, so they bake the
    multiset/vertex-subset convolution divergence
    (`convolution_vertex_vs_multiset.md`) into a downstream-visible
    spot. Defer until that decision is revisited.
  * **Not `lem:351A` / `thm:351B`** — need the matrix-resolvent
    `(I − zA)⁻¹` infrastructure that `AN_stability_deferred.md`
    estimates at 3-5 cycles.
  * **Not `lem:441A` / `lem:441B` / `thm:441C`** — Dahlquist's
    first barrier requires polynomial root-counting (Rouché /
    Schur-Cohn), heavy.
  * **Not `lem:310B` / `lem:312B` / `thm:302A` / etc.** — need
    Taylor's theorem (`thm:306A`) and the elementary-differential
    machinery, multi-cycle infrastructure.

### Textbook statement (quoted verbatim from
`extraction/formalization_data/entities/def_510A.json`)

> A general linear method `(A, U, B, V)` is 'preconsistent' if there
> exists a vector `u` such that
>
>     V u = u,                              (510a)
>     U u = 1.                              (510b)
>
> The vector `u` is the 'preconsistency vector'.

### Lean encoding plan

Create new file: **`OpenMath/Chapter5/Section510.lean`** (the
`OpenMath/Chapter5/` directory does not yet exist; create it).
Update `OpenMath.lean` (the project root index, if there is one;
otherwise `lakefile.toml`/`lean-toolchain` are unaffected) only if
required by the existing import structure — the worker should check
how `OpenMath/Chapter4/Section404.lean` is registered and follow the
same pattern.

#### Step 1 — `GeneralLinearMethod` structure

The textbook GLM has two natural-number indices:

* `s : ℕ` — the number of internal stages.
* `r : ℕ` — the number of input/output values (multistep
  history depth).

The four matrices live in:

| Matrix | Type |
|---|---|
| `A` | `Matrix (Fin s) (Fin s) ℝ` |
| `U` | `Matrix (Fin s) (Fin r) ℝ` |
| `B` | `Matrix (Fin r) (Fin s) ℝ` |
| `V` | `Matrix (Fin r) (Fin r) ℝ` |

Encode as:

```lean
namespace OpenMath.Chapter5.Section510

/-- A general linear method (Butcher §510) with `s` internal stages
and `r` input/output values. The four constituent matrices together
specify how a single step transforms the `r`-vector of input values
and computes the `s` internal stages. -/
structure GeneralLinearMethod (s r : ℕ) where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ
```

Use `structure`, not `class` — there is no instance-resolution role
here.

#### Step 2 — `IsPreconsistent` predicate

```lean
/-- **Definition 510A** — A GLM is *preconsistent* if there exists a
vector `u : Fin r → ℝ` (the *preconsistency vector*) such that
`V u = u` and `U u = 1` (the all-ones vector in `Fin s → ℝ`). -/
def GeneralLinearMethod.IsPreconsistent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ u : Fin r → ℝ, M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)
```

Notes:

* `*ᵥ` is `Matrix.mulVec`. The notation should be in scope under
  `open Matrix`. Verify with `lean_local_search "mulVec"` if not.
  The relevant import in `Section322.lean` already brings it in
  (`Mathlib.LinearAlgebra.Matrix.Determinant.Basic` etc.); the
  cleanest single import that picks up everything needed is
  `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` — copy
  `Section322.lean`'s import block as a starting point.
* `(fun _ => 1)` is the all-ones vector in `Fin s → ℝ`. Mathlib also
  has `1 : Fin s → ℝ` via `Pi.instOne`, but the explicit
  `fun _ => (1 : ℝ)` is clearer (avoids reader confusion with the
  matrix identity `(1 : Matrix _ _ ℝ)`).

#### Step 3 — Non-vacuity witness: explicit Euler as a `(1, 1)`-GLM

Explicit Euler `y_{n+1} = y_n + h f(y_n)` is the canonical GLM with
`s = r = 1` and matrices:

| | |
|---|---|
| `A = !![0]` | `U = !![1]` |
| `B = !![1]` | `V = !![1]` |

(One stage `Y_1 = y_n + h · 0 · f(Y_1) = y_n` (no implicit recursion
because `A = 0`), and one output `y_{n+1} = h · 1 · f(Y_1) + 1 · y_n
= y_n + h f(y_n)`.)

The preconsistency vector is `u = (fun _ => 1)`:

```lean
def explicitEulerGLM : GeneralLinearMethod 1 1 where
  A := !![0]
  U := !![1]
  B := !![1]
  V := !![1]

theorem explicitEulerGLM_isPreconsistent :
    explicitEulerGLM.IsPreconsistent := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · -- V u = u: !![1] applied to fun _ => 1 gives fun _ => 1.
    funext i; fin_cases i
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one,
          explicitEulerGLM]
  · -- U u = 1: !![1] applied to fun _ => 1 gives fun _ => 1.
    funext i; fin_cases i
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one,
          explicitEulerGLM]
```

If `fin_cases i` on `Fin 1` is awkward, replace with the `Fin 1`
elimination idiom `Subsingleton.elim i 0 ▸ ...` or `match i with
| 0 => ...`. The `simp` set above should close both goals; if not,
expand manually with `Matrix.mulVec_cons` /
`Matrix.cons_val_zero` / `Matrix.cons_val_one` (these are the
`!![ ... ]` matrix-literal lemmas — discoverable via
`lean_local_search "Matrix.cons_val"`).

If the proof balloons past ~10 lines, the simplest fallback is a
`decide`-style direct verification: `Matrix.mulVec` on a 1×1 matrix
is a single multiplication; the worker can write the equations out
elementwise and discharge with `ring` / `norm_num`.

#### Step 4 — Update `lean_status.json`

Change the entry for `def:510A`:

```json
"def:510A": {
  "lean_file": "OpenMath/Chapter5/Section510.lean",
  "lean_symbol": "OpenMath.Chapter5.Section510.GeneralLinearMethod.IsPreconsistent",
  "status": "formalized"
}
```

#### Step 5 — Update `plan.md`

Change the Chapter 5 row for `def:510A` from `[ ]` to `[x]` and
append `— OpenMath/Chapter5/Section510.lean`. Bump the global
**Progress** counter accordingly (after Priority 0's bump to 54/175,
this brings it to 55/175).

### File-level docstring (do include this)

Add a top-of-file block comment quoting Butcher's def:510A statement
verbatim and noting the `(s, r)` index convention. Pattern after
`OpenMath/Chapter3/Section322.lean`'s docstring (which is exemplary
for a single-entity file).

---

## Faithfulness checklist for cycle 083 (run before commit)

For `GeneralLinearMethod` (new structure):

- [ ] Quote textbook source: `def_510A.json` "A general linear
  method (A, U, B, V)" — four matrices match.
- [ ] Type signatures match: `A : s×s`, `U : s×r`, `B : r×s`,
  `V : r×r`. Confirm with `def_520A.json` and `def_510B.json` quoted
  text (the same `(A, U, B, V)` tuple appears throughout Chapter 5,
  so this convention is stable).
- [ ] No Prop fields — pure data structure.

For `IsPreconsistent` (new def):

- [ ] Quote: `∃ u, V u = u ∧ U u = 1`. Match.
- [ ] Definition smuggling check: this is a *predicate on existence
  of u*, not a stipulation that any specific `u` works. Matches
  Butcher's "there exists a vector u".
- [ ] Hypothesis-strength check: no extra hypotheses on `M`.

For `explicitEulerGLM_isPreconsistent` (new theorem):

- [ ] Tautology check: conclusion `IsPreconsistent` does not appear
  verbatim as a hypothesis — the witness `u = fun _ => 1` is the
  real content.
- [ ] Identity check: proof is not `exact h`; it constructs the
  witness and discharges the matrix-vector equations.
- [ ] Hypothesis-strength check: hypothesis-free; this is a
  non-vacuity witness.

Per CLAUDE.md "every new `class` or `structure`, provide at least
one concrete witness/instance in the same cycle":
**`explicitEulerGLM` + `explicitEulerGLM_isPreconsistent` is the
witness.** Without it, the cycle violates the rule.

---

## What NOT to try this cycle

* **Do NOT pick `lem:322A`** — already formalized. The cycle 082
  worker's recommendation was based on a stale `plan.md` row.
* **Do NOT re-open the convolution-divergence question
  (`convolution_vertex_vs_multiset.md`).** The cycle 082 planner
  decision (option (b) — defer the refactor) stands until `lem:383D`
  or `thm:386A` becomes a blocker, and neither is queued for at
  least the next several cycles.
* **Do NOT attempt `def:381F`.** It needs the deferred `reducedMethod`
  construction (`reduced_method_deferred.md`).
* **Do NOT attempt `def:422B` / `thm:422A` / `thm:422C`.** They
  embed the convolution group `G₁` in their definitions and would
  bake the convolution divergence into Chapter-4 visible code.
* **Do NOT attempt `lem:351A` or `thm:351B`.** They need the matrix
  resolvent `(I − zA)⁻¹` infrastructure (3-5 cycles to build, per
  `AN_stability_deferred.md`).
* **Do NOT attempt `lem:441A` / `lem:441B` / `thm:441C`.** Dahlquist's
  first barrier — needs polynomial Schur-Cohn / Rouché root-counting
  infrastructure.
* **Do NOT attempt `lem:310B` / `lem:312B` / `thm:302A` / `thm:302B` /
  `thm:302C` / `thm:304A` / etc.** These need Taylor's theorem
  (`thm:306A`) and the elementary-differential machinery, plus a
  vertex-set / labelling framework on `RootedTree` that is not in
  the codebase. Multi-cycle infrastructure project.
* **Do NOT attempt `def:451A` (G-stable for one-leg method) or any
  Chapter-4 §44x / §45x targets.** They need infrastructure (one-leg
  method framework, `g`-quadratic-form machinery) not yet in the
  codebase.
* **Do NOT change the index convention to `(r, s)` from `(s, r)`.**
  Butcher's tableau presentation `[A | U; B | V]` has `A` in the
  top-left (s×s, the stage-stage block), so `s` is the natural first
  index. This will keep the convention consistent with `def:520A`
  ("`M(z) = V + zB(I - zA)⁻¹U`" — the `(I - zA)⁻¹` block-shape
  reading requires `A : s×s`).
* **Do NOT submit definitions to Aristotle.** Aristotle is for
  closing proofs of theorems/lemmas; definitions have no proof
  obligation. The non-vacuity witness `explicitEulerGLM_isPreconsistent`
  is a ~5-line `simp` proof and should not be batched out.
* **Do NOT raise `maxHeartbeats`** — the file is small.
* **Do NOT introduce `axiom` / `constant`** — none of this work
  needs it.

---

## Aristotle workflow this cycle

**Skip Aristotle entirely.** This cycle's substantive work is one
new structure, one new predicate, and one ≤10-line non-vacuity
witness — none of which are "Aristotle bait" (Aristotle excels at
premise selection for theorem proofs, not at structure design or
trivial `simp`-closes). Save Aristotle compute for cycle 084 when
the next cluster of GLM consistency lemmas (`def:510B`, `def:510C`)
or stability theorems will benefit from it.

If during the cycle the worker discovers an unexpected lemma that
*would* benefit from Aristotle (e.g. a `Matrix.mulVec` identity that
fails to `simp`-close), batch-submit and proceed manually rather
than blocking on a 30-minute wait — the file is too small to justify
a wait window.

---

## Build verification (mandatory before commit)

```bash
# Verify the new Section510 compiles standalone.
lake env lean OpenMath/Chapter5/Section510.lean

# Sanity-check the existing Section322 still compiles (no regression).
lake env lean OpenMath/Chapter3/Section322.lean

# Axiom check on the new entities. Run AFTER lake build OpenMath.Chapter5.Section510
# (per attempts.md cycle 072: lake env lean does NOT update .olean cache).
lake build OpenMath.Chapter5.Section510
echo '#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.IsPreconsistent
#print axioms OpenMath.Chapter5.Section510.explicitEulerGLM_isPreconsistent' \
  | lake env lean --stdin OpenMath/Chapter5/Section510.lean
```

Expected: clean compile; axioms `[propext, Classical.choice, Quot.sound]`
only.

---

## Suggested follow-ups (NOT cycle 083 work — for the planner of later cycles)

After cycle 083 lands:

* **Cycle 084**: `def:510C` (stable GLM — `‖V^n‖ ≤ C`). Depends only
  on `def:142A` (power-boundedness, done) and the cycle-083
  `GeneralLinearMethod` structure. Trivial wrapping.

* **Cycle 085**: `def:510B` (consistent GLM). Depends on 510A + 510C.
  Adds the extra hypothesis `B 1 + V v = u + v`. Modest.

* **Cycle 086+**: `def:512A` (convergent GLM) — analogous to the
  cycle-068 `LinearMultistepMethod.IsConvergent`. May need a
  trajectory-bound strengthening (cf.
  `is_convergent_strengthened.md` for the LMM analogue), but the
  pattern is now well-trodden.

* **Cycle 087+**: `thm:513A` (necessity of stability), `thm:514A`
  (necessity of consistency) — Chapter 5 analogues of `thm:405A` /
  `thm:405C`, which the project already has machinery for (cycles
  068-072).

This roadmap suggests Chapter 5 §51x can be cleared in 5-6 cycles
of similar shape to the §404/§405 cycles, after which §52x
(stability matrix `M(z)`) becomes the natural next investment —
which *will* benefit from matrix-resolvent infrastructure shared
with the deferred `lem:351A` / AN-stability work, so it would be
worth opening that infrastructure project then.

---

## Task results expectations

Write `.prover-state/task_results/cycle_083.md` documenting:

* What landed (Priority 0 housekeeping + Priority 1 def + witness).
* Whether the proof of `explicitEulerGLM_isPreconsistent` closed
  with `simp` alone or needed manual `Matrix.mulVec_def` / `cons_val`
  expansion.
* Whether `lake env lean` showed any unexpected axioms.
* Confirmation that `plan.md` and `lean_status.json` are
  consistent with each other (i.e. no other stale rows beyond the
  `lem:322A` one this cycle fixes — list any further mismatches the
  Priority 0c sweep turned up).

If the worker discovers further stale `[ ]` markers in `plan.md`
that should be `[x]` per `lean_status.json`, fix them under
Priority 0 — but do NOT try to add new entities to `plan.md` or
edit anything else in `lean_status.json` beyond the `def:510A` row.
