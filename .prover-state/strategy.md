# Cycle 132 Strategy

## TL;DR

Primary target: **register `thm:142D` (i ⇔ ii) as a partial formalization** by
adding a textbook-numbered alias for the existing
`OpenMath.Chapter1.Section142.convergent_iff_minpoly_roots_lt_one`
(cycle 005), updating `lean_status.json` and `plan.md`, and documenting
the deferred (iii)/(iv) Jordan/Schur clauses. Progress 68 → 69 / 175.

Stretch goal (only if primary is in the bag): **substantive r=2 IRK-stability
witness** that genuinely exercises the cycle 131 `IsIRKStable` predicate
(the cycle 131 witness is vacuous on the row-0 clauses for `r = 1`,
see §C below).

## Why this target

### Context audit — what's actually tractable

I examined every "natural next" candidate suggested by the cycle 131
worker and the upcoming entries in `plan.md`:

| Candidate | Status |
|---|---|
| Substantive `implicitMidpointGLM_isIRKStable` | Vacuous for `r = 1` regardless of `X`, see §C |
| `def:530A` non-degenerate | Needs `StartingMethod` + generalized RK infra (heavy) |
| `thm:535A` underlying one-step method (GLM) | Requires `thm:422A`, rooted-tree machinery; transitive blocker |
| `thm:541A` DIMSIM types | Transitive deps include `def:310A`, `thm:301A`, `thm:532A` etc. — none formalized |
| `thm:551B` Single non-zero eigenvalue | Requires §550 doubly companion matrix infra |
| `thm:521B` Maximum stability order | Contour integrals + partial fractions |
| `thm:431A` Schur criterion | Rouché's theorem, complex polynomial root counting (medium-heavy) |
| `def:451A` G-stable | One-leg method infra not built; matrix `M` from (451e) underspecified in extracted text |
| `thm:142C / E / F` | (iii)/(iv) clauses or perturbation-via-Schur blocked on Jordan/Schur per `jordan_canonical_form_missing.md` |

The §142 entries are partially recoverable: `thm:142D` (i ⇔ ii) is
already proven in `Section142.lean` lines 311–337 from cycle 005 —
the `convergent_iff_minpoly_roots_lt_one` packaging. This makes it
the **cleanest single-cycle entity bump available**: the proof is
already in the codebase, only the entity registration is missing.

### Why this beats freelancing

Per CLAUDE.md "Follow the strategy. Do not cherry-pick easy goals".
This target is NOT cherry-picking — it is recovering an already-proven
theorem that was filed under an internal name and never registered as
its textbook ID. The `convergent_iff_minpoly_roots_lt_one` docstring
explicitly says "Butcher §142, Theorem 142D — clauses (i) ⇔ (ii)";
the entity record `thm:142D` just hasn't been credited.

This is the same pattern used for `def:356A` (DJ-irreducibility
component formalized, AN-stability deferred) and `def:381E`
(IsIrreducible formalized, reducedMethod construction deferred).

## Primary deliverable — `thm:142D` (i ⇔ ii) partial

### Step 1 — Add textbook-named alias

Edit `OpenMath/Chapter1/Section142.lean` after the existing
`convergent_iff_minpoly_roots_lt_one` (currently ends ~line 337) to
add a thin alias that carries the textbook ID as the Lean symbol:

```lean
/-- Butcher §142, Theorem 142D — partial formalization (clauses
(i) ⇔ (ii) only).

Statement: A square complex matrix `A` is convergent (`A^n → 0`) if
and only if every root of its minimal polynomial lies in the open
unit disc.

The full 4-way TFAE in Butcher's textbook also includes:
* (iii) Jordan canonical form has all diagonal elements in the open
  unit disc.
* (iv) ∃ non-singular `S` with `‖S⁻¹AS‖_∞ < 1`.

Both (iii) and (iv) are deferred — they require a Jordan canonical
form / rescaled Schur decomposition, which is not yet in Mathlib.
See `.prover-state/issues/jordan_canonical_form_missing.md`. -/
theorem thm_142D
    (A : Matrix m m ℂ) :
    Convergent A ↔ ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1 :=
  convergent_iff_minpoly_roots_lt_one A
```

Place inside the existing `namespace OpenMath.Chapter1.Section142`
section block (you'll see `end ConvergenceCharacterizations` and
`end OpenMath.Chapter1.Section142` near the bottom — insert *before*
both `end`s, in the same `ConvergenceCharacterizations` section that
holds `convergent_iff_minpoly_roots_lt_one`).

Naming follows the established convention from cycle 131
(`def:551A` → `IsIRKStable`, etc.) — the textbook number embedded
in the symbol so future lookups can grep by number.

### Step 2 — Update `lean_status.json`

Locate the row for `thm:142D` in
`extraction/formalization_data/lean_status.json` and update. First
check the schema by examining an existing `partial` row (e.g.
`def:356A` or `def:381E`) so you match the existing field
conventions. Then update:

* `lean_file` → `OpenMath/Chapter1/Section142.lean`
* `lean_symbol` → `OpenMath.Chapter1.Section142.thm_142D`
* `formalization_status` → `partial`
* `notes` (or whatever the schema field is): "Clauses (i) ⇔ (ii)
  only via Gelfand bridge (cycle 005). Clauses (iii) Jordan
  canonical form and (iv) Schur similarity are deferred — Mathlib
  lacks Jordan/Schur. See
  `.prover-state/issues/jordan_canonical_form_missing.md`."

### Step 3 — Update `plan.md`

Change the §142 Chapter 1 row for `thm:142D` from `[ ]` to `[~]` with
a status note:

```markdown
- [~] `thm:142D` **Convergence Equivalence for Matrix Powers** (§142) — `OpenMath/Chapter1/Section142.lean::thm_142D` (cycle 132, partial: i ⇔ ii via Gelfand; iii/iv blocked on Jordan canonical form per `jordan_canonical_form_missing.md`)
```

Update the "Progress" header at the top of `plan.md` from 68 / 175
to 69 / 175 (or 68.5 / 175 depending on convention — match how
prior partials like `def:356A` were counted).

### Step 4 — Verify axiom-clean

```bash
lake env lean OpenMath/Chapter1/Section142.lean
```

Then via `lean_verify` MCP or by adding a temporary scratch:

```
#print axioms OpenMath.Chapter1.Section142.thm_142D
```

Expected: `[propext, Classical.choice, Quot.sound]` only. Should
trivially follow since `thm_142D` is a one-line alias of
`convergent_iff_minpoly_roots_lt_one`, which already passes
axiom-clean checks.

### Step 5 — Faithfulness check

Quote the textbook statement of `thm:142D` from
`extraction/formalization_data/entities/thm_142D.json` in
`task_results/cycle_132.md`'s faithfulness section. Note explicitly
that:

* The Lean statement captures clauses (i) ⇔ (ii) only.
* Clauses (iii)/(iv) are deferred with a documented blocker
  (`jordan_canonical_form_missing.md`).
* This is the same partial-formalization pattern used for `def:356A`
  (DJ-irreducibility component, AN-stability deferred) and
  `def:381E` (IsIrreducible only, reducedMethod deferred).

Do **NOT** package (iii)/(iv) as `True ↔ True` placeholders or
encode them as `sorry`'d Iff clauses — that is the explicit
anti-pattern flagged in the cycle 005 strategy. A partial Iff with
two clauses is the right shape; (iii)/(iv) are not present at all,
not stubbed.

## Stretch goal — substantive r=2 IRK-stability witness

**Only attempt if Steps 1–5 are committed AND > 30 minutes of cycle
remain.** If not, defer to cycle 133.

### Why the cycle 131 worker's "implicit-midpoint" suggestion is wrong

The cycle 131 task results suggest a "substantive
`implicitMidpointGLM_isIRKStable`" witness, claiming:

> s = 1, so the row-0 clause is non-vacuous: we'd need
> `(B·A − 0) 0 j = 0` which fails

This analysis is **incorrect**. Reading the predicate at
`OpenMath/Chapter5/Section520.lean:586–596`:

```lean
def GeneralLinearMethod.IsIRKStable {s r : ℕ} [NeZero r]
    (M : GeneralLinearMethod s r) : Prop :=
  (∀ i : Fin r, M.V i 0 = if i = 0 then 1 else 0) ∧
  ∃ X : Matrix (Fin r) (Fin r) ℝ,
    (∀ (i : Fin r) (j : Fin s), i ≠ 0 →
      (M.B * M.A - X * M.B) i j = 0) ∧
    (∀ i j : Fin r, i ≠ 0 →
      (M.B * M.U - X * M.V + M.V * X) i j = 0)
```

The row-constraint clauses iterate over `i : Fin r`, NOT `Fin s`.
For implicit-midpoint with `r = 1`, no `i ≠ 0` exists in `Fin 1`, so
both row-0 clauses are vacuously true regardless of `X`. The
substantive witness for implicit-midpoint reduces to the trivial
`X := 0` witness, which is what cycle 131 already shipped for
explicit Euler. Implicit-midpoint adds nothing.

### What a genuine substantive witness needs

A non-vacuous IRK-stability witness requires `r ≥ 2`. Sketch:

```lean
def GeneralLinearMethod.dummyR2 : GeneralLinearMethod 1 2 :=
  { A := !![0]
    U := !![1, 0]
    B := !![1; 0]    -- shape Fin 2 × Fin 1
    V := !![1, 1; 0, 0] }
```

(Verify the field types/shapes match `Section510.lean`'s
`GeneralLinearMethod` structure before constructing — `B` and `V`
shapes are `Fin r × Fin s` and `Fin r × Fin r` respectively.)

For this `dummyR2`, the IRK-stability witness needs `X : Matrix
(Fin 2) (Fin 2) ℝ` such that:

* V's first column = `e₀` clause: `V 0 0 = 1` (true: V[0][0] = 1),
  `V 1 0 = 0` (true: V[1][0] = 0). ✓
* `(B*A - X*B) i j = 0` for `i = 1, j = 0` (one index pair).
* `(B*U - X*V + V*X) i j = 0` for `i = 1, j ∈ {0, 1}` (two pairs).

Pick `X = !![0, 1; 0, 0]` (or another candidate from staring at the
textbook form) and verify the three constraints unfold cleanly via
`fin_cases i; fin_cases j; simp [dummyR2, Matrix.mul_apply, Fin.sum_univ_succ]`.
The X choice may need iteration — start with `X := 0` to see what
fails, then patch.

### Stretch budget

~80 LOC max (definition + witness theorem + axiom-clean check). If
the X-algebra doesn't close cleanly within ~45 min of attempt time,
**stop and revert** the stretch work; ship the primary deliverable
alone. Do not let the stretch goal delay the primary commit.

If you do land the stretch goal: bump entity count further (still
68/175 since IRK-stability is a property of `def:551A`, not a new
entity — but document the strengthening in
`task_results/cycle_132.md` and update `def:551A`'s row in
`lean_status.json` to note the substantive witness).

## What NOT to try

1. **Do not attempt `thm:142D` (iii) or (iv)** — both require Jordan
   canonical form / rescaled Schur infrastructure. Per
   `jordan_canonical_form_missing.md`, this is multi-cycle Mathlib
   work and explicitly out of scope.

2. **Do not encode (iii)/(iv) as `True ↔ True` placeholders or
   sorry'd Iff clauses.** That is the cycle 005 anti-pattern. The
   faithful approach is partial formalization with an explicit
   deferral note — (iii)/(iv) are absent from the Lean statement,
   not stubbed.

3. **Do not pursue the cycle 131 worker's `implicitMidpointGLM_isIRKStable`
   suggestion as written.** As shown in §"Stretch goal" above, it's
   vacuous for `r = 1`. Skip implicit-midpoint entirely; if you go
   for substantive, do `r = 2`.

4. **Do not pivot to `def:530A` / `thm:535A` / `thm:541A` /
   `def:451A`.** These all need substantial new infrastructure
   (starting methods, generalized RK, rooted-tree elementary
   differentials, one-leg methods, equation 451e expansion) — cannot
   be closed in one cycle.

5. **Do not attempt `thm:431A` Schur criterion.** Although Rouché's
   theorem is in Mathlib, the polynomial-root-counting plumbing is
   medium-effort and not aligned with the §142 cycle target.
   Defer to a future cycle dedicated to §43.

6. **Do not raise `maxHeartbeats`.** Per CLAUDE.md.

7. **Do not introduce `axiom` or `constant`.** Per CLAUDE.md.

8. **Do not edit `scripts/autonomous_loop.py`** or rebuild the
   tautology scanner. Loop maintainer's territory; see
   `tautology_scanner_false_positives.md`.

9. **Do not reattempt the cycle 005 (i) ⇒ (ii) Gelfand bridge** — it's
   already in the codebase as `convergent_imp_minpoly_roots_lt_one`
   (line 161) and `minpoly_roots_lt_one_imp_convergent` (line 311).
   Reuse via the alias.

10. **Do not delete or rename `convergent_iff_minpoly_roots_lt_one`**
    when adding `thm_142D`. Keep both — `thm_142D` is an alias, not a
    replacement. Existing callers (if any) continue to use the
    `convergent_iff_*` name.

## Pre-commit checklist

Before committing:

- [ ] `lake env lean OpenMath/Chapter1/Section142.lean` exits 0.
- [ ] `#print axioms OpenMath.Chapter1.Section142.thm_142D` shows
      `[propext, Classical.choice, Quot.sound]` only.
- [ ] `lean_status.json` row for `thm:142D` shows
      `formalization_status: "partial"` with correct
      `lean_file` / `lean_symbol`.
- [ ] `plan.md` row for `thm:142D` reads `[~]` with the deferral
      note.
- [ ] `plan.md` progress header reflects the new count.
- [ ] No new sorry's introduced anywhere.
- [ ] No regression in any existing axiom-clean theorem.
- [ ] Faithfulness check section in `cycle_132.md` quotes the
      textbook statement and explicitly notes the (iii)/(iv) deferral
      with a pointer to `jordan_canonical_form_missing.md`.
- [ ] If stretch goal landed: `dummyR2.IsIRKStable` (or chosen name)
      verified axiom-clean; `def:551A` row noted as having
      substantive witness; `task_results` documents both pieces.

## Cycle results format

Write `.prover-state/task_results/cycle_132.md` per the CLAUDE.md
template. The "Faithfulness check" section is non-optional given
this is a partial formalization — explicitly flag the divergence
(deferred clauses (iii)/(iv)).

## Suggested next-cycle direction (for cycle 133 planner)

After cycle 132, the natural follow-ups are:

1. **Substantive r=2 IRK-stability witness** if not done as stretch
   in cycle 132.

2. **`thm:551B` Single Non Zero Eigenvalue Stability** — uses the
   cycle 131 `IsIRKStable` predicate; closes a downstream consumer.
   Requires deciding on §550 doubly companion matrix infra (small,
   ~50 LOC) — could be bundled into cycle 133.

3. **`thm:431A` Schur criterion** — Mathlib has Rouché's theorem;
   medium-effort, unblocks §43 stability work in Chapter 4.

The §142 (iii)/(iv) and the heavy §53/§54 infrastructure entries
should remain deferred until they become genuinely blocking.
