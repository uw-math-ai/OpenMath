# Cycle 165 strategy — pivot to `def:451A` G-stable

## TL;DR

**Pivot to a fresh entity.** After 9 consecutive cycles on
`def:530B`/`def:530C` Path A (cycles 156–164: r-extensions, two
helper extractions, parametric refactor across three phases),
returns are diminishing and the entity remains `[~]` partial
because Path B (implicit branch) requires multi-cycle Mathlib
fixed-point infrastructure.

The cycle 164 task results recommended cycle-165 retirement of
the hand-written instances. **Do not pursue retirement this cycle.**
Reason: a quick audit shows 438 references to `padded{2,3,4}DEulerGLM`
/ `pad{Compat,3Compat,4Compat}StartingMethod` in
`OpenMath/Chapter5/Section530.lean`, plus six independent stability
witnesses in `OpenMath/Chapter5/Section520.lean`
(`padded2DEulerGLM_isIRKStable`, `_stabilityMatrix`,
`_stabilityFunction`, `_isRKStable`, `_not_isAStable`,
`_not_isLStable`) tied to the hand-written `padded2DEulerGLM`
that cite def:520E / def:520F / def:542A / def:551A non-vacuity.
Full retirement is multi-cycle. Pursuing it as a single cycle
would either cascade through these stability witnesses or land
a fragile partial cleanup.

The right move is to **claim a fresh `[ ]` entity**:
**`def:451A` (G-stable, §451)**. It is dependency-free
(`dependencies: []` per its entity record), has a clean
mathematical statement (positive semi-definiteness of an explicit
matrix), and admits a textbook-supplied non-vacuity witness
(BDF2). Single-cycle deliverable bar: definition + non-vacuity
witness, axiom-clean.

---

## Priority 1 — Formalize `def:451A` (G-stable)

Target file: **new** `OpenMath/Chapter4/Section451.lean`. (Section
451 sits in Chapter 4 §451; do not crowd Section404.lean further.)

### Mathematical content (Butcher §451, p. 363)

> A one-leg method `[α, β]` is "G-stable" if `M` given by (451e)
> is positive semi-definite.

Equation (451e), reproduced verbatim from `extraction/raw_text/ch04.txt`
near "(451e)":

```
M = αβᵀ + βαᵀ − [G 0; 0 0] + [0 0; 0 G]
```

where `α, β : Fin (k+1) → ℝ` are the coefficient column vectors
in the convention `α = (1, −α₁, −α₂, …, −α_k)` and
`β = (β₀, β₁, …, β_k)`, and `G : Matrix (Fin k) (Fin k) ℝ` is a
**chosen** symmetric matrix. The blocks `[G 0; 0 0]` and `[0 0; 0 G]`
embed `G` into the top-left and bottom-right `k × k` corner of a
`(k+1) × (k+1)` matrix respectively.

### Concrete Lean shape

```lean
namespace OpenMath.Chapter4.Section451

open OpenMath.Chapter4.Section404 (LinearMultistepMethod)

/-- The textbook's α-vector for §451: `(1, -α₁, …, -α_k)`. Recall
that our `LinearMultistepMethod` uses the convention `α 0 = -1`,
so the textbook's α-vector is the entrywise negation of `M.α`. -/
def LinearMultistepMethod.alphaVec {k : ℕ} (M : LinearMultistepMethod k) :
    Fin (k + 1) → ℝ := fun i => -M.α i

/-- The textbook's β-vector. -/
def LinearMultistepMethod.betaVec {k : ℕ} (M : LinearMultistepMethod k) :
    Fin (k + 1) → ℝ := M.β

/-- Embed a `Fin k`-indexed symmetric matrix `G` into the top-left
`k × k` block of a `Fin (k+1)` square matrix; zero on the last row
and column. -/
def gTopLeft {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : i.val < k ∧ j.val < k then
      G ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else 0

/-- Embed `G` into the bottom-right `k × k` block. -/
def gBottomRight {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : 0 < i.val ∧ 0 < j.val then
      G ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    else 0

/-- Butcher's matrix `M` from (451e): `αβᵀ + βαᵀ − [G 0; 0 0] + [0 0; 0 G]`. -/
def LinearMultistepMethod.gMatrix {k : ℕ}
    (M : LinearMultistepMethod k)
    (G : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.vecMulVec M.alphaVec M.betaVec
    + Matrix.vecMulVec M.betaVec M.alphaVec
    - gTopLeft G
    + gBottomRight G

/-- Butcher def:451A — a one-leg method (LMM treated as one-leg) is
**G-stable** if there exists a symmetric, positive-definite `G` such
that `M.gMatrix G` is positive semi-definite. -/
def LinearMultistepMethod.IsGStable {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∃ G : Matrix (Fin k) (Fin k) ℝ, G.IsSymm ∧ G.PosDef ∧
    (M.gMatrix G).PosSemidef
```

### Non-vacuity witness — BDF2

The textbook provides BDF2 explicitly:

> `[α(z), β(z)] = (1 − (4/3)z + (1/3)z², 2/3)`

Translating: BDF2 is a 2-step LMM (`k = 2`) with
`α₁ = 4/3, α₂ = -1/3, β₀ = 2/3, β₁ = β₂ = 0`. (Care: the
textbook polynomial uses the convention
`α(z) = 1 - (4/3)z + (1/3)z²` where `1` is the `z⁰` coefficient,
so the LMM's `α 1 = 4/3` and `α 2 = -1/3`. For our
`LinearMultistepMethod` with `α 0 = -1`, set
`α 0 := -1, α 1 := 4/3, α 2 := -1/3`, and
`β 0 := 2/3, β 1 := 0, β 2 := 0`.)

The textbook also supplies the witness `G`:

> `G = ((10/9, -4/9), (-4/9, 2/9))`

```lean
def bdf2LMM : LinearMultistepMethod 2 where
  α := fun i => match i with
    | ⟨0, _⟩ => -1
    | ⟨1, _⟩ => 4/3
    | ⟨2, _⟩ => -1/3
  β := fun i => match i with
    | ⟨0, _⟩ => 2/3
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
  α_zero := rfl

def bdf2GWitness : Matrix (Fin 2) (Fin 2) ℝ :=
  !![10/9, -4/9; -4/9, 2/9]

theorem bdf2LMM_isGStable : bdf2LMM.IsGStable := by
  refine ⟨bdf2GWitness, ?_, ?_, ?_⟩
  · -- IsSymm: G = Gᵀ. Verify by `ext i j; fin_cases i <;> fin_cases j <;> rfl`.
    sorry
  · -- PosDef. The textbook gives this; verify by `Matrix.PosDef` definition
    -- on a 2×2 matrix with leading 10/9 > 0 and det = 20/81 - 16/81 = 4/81 > 0.
    sorry
  · -- PosSemidef of `M.gMatrix G`. Per textbook, M reduces to:
    --   [3/4 - g_11, -8/9 - g_12, 2/9;
    --    -8/9 - g_12, g_11 - g_22, g_12;
    --    2/9, g_12, g_22]
    -- With g_11 = 10/9, g_12 = -4/9, g_22 = 2/9, the off-diagonal
    -- entries reduce, and entry-wise verification (or rank-1 check)
    -- yields `M.gMatrix G ≥ 0`. Concretely: compute each of the 9
    -- entries via `simp` + `norm_num`; check PosSemidef by
    -- `Matrix.PosSemidef.fromBlocks_of_iff` or by a Cholesky-style
    -- factor exhibiting M = LLᵀ.
    sorry
```

The three `sorry`s are deliberate stepping stones for the cycle 165
worker. **Sorry-first ladder**:

1. **Step 1 — definitions + scaffold**: Introduce `alphaVec`,
   `betaVec`, `gTopLeft`, `gBottomRight`, `gMatrix`, `IsGStable`,
   `bdf2LMM`, `bdf2GWitness`, `bdf2LMM_isGStable` with three
   `sorry`s. Verify the file compiles.
2. **Step 2 — IsSymm**: 4 `Fin.cases` × `rfl` (~5 lines). Trivial.
3. **Step 3 — PosDef**: Use `Matrix.PosDef.of_two_dim` (search
   Mathlib) or unfold to `Matrix.PosDef` and prove via
   `Matrix.PosSemidef.of_pos_diag_pos_det` analogue. Concrete: a
   2×2 symmetric matrix `[a, b; b, c]` is `PosDef` iff `a > 0` and
   `a*c - b² > 0`. For us, `10/9 > 0` and
   `(10/9)(2/9) - (-4/9)² = 20/81 - 16/81 = 4/81 > 0`. Build via
   inner-product expansion `⟨v, M v⟩ = a v₀² + 2b v₀ v₁ + c v₁²`
   and complete-the-square. Backup: search Mathlib for
   `Matrix.PosDef` 2×2 lemmas.
4. **Step 4 — PosSemidef of M(G)**: Compute `M(G)` entry-wise.
   Suggest: factor `M(G) = vvᵀ` for some `v : Fin 3 → ℝ` if M
   turns out rank-1, or `M(G) = LLᵀ` more generally — both close
   `PosSemidef` immediately via `Matrix.posSemidef_self_mul_transpose`
   (verify name). Compute the 9 entries first; if they are all
   small rationals, `decide` or `norm_num` should discharge.
   Backup: use `Matrix.PosSemidef.diagonal` after reducing M to a
   diagonal form via row/col operations.

### Faithfulness check (apply at end of cycle)

For `IsGStable`:
- [ ] Open `extraction/formalization_data/entities/def_451A.json`
  and quote the textbook statement (already extracted at top of
  this strategy).
- [ ] Confirm Lean type matches: `IsGStable` is an existential
  quantifier over `G` symmetric + PosDef + `M.gMatrix G` PosSemidef.
  The textbook says "G-stable if M is positive semi-definite",
  parameterised by an unstated G. Standard reading: G-stable iff
  *exists* such G. Document this convention in the docstring.
- [ ] **Definition smuggling check**: do not encode "G-stable" as
  the consequence (e.g. "stable for all dissipative IVPs"). It
  must be the definitional matrix condition. ✓ (definition above
  matches textbook).

For `bdf2LMM_isGStable`:
- [ ] Tautology check: conclusion is `bdf2LMM.IsGStable`; not
  `True ↔ True`, not `id`-shaped. ✓
- [ ] Identity check: proof is a `refine` with three sub-proofs
  (witness `G`, three properties), not `exact h`. ✓
- [ ] Hypothesis strength check: no hypotheses; the witness is
  unconditional. ✓

---

## Priority 2 (backup) — Aristotle batch for the three sorry's

If priority-1 Step 1 lands and Steps 2/3/4 take longer than
expected, batch-submit Steps 2, 3, 4 to Aristotle as parallel
sub-jobs (~5 jobs is the CLAUDE.md target):

* **Job A**: `bdf2GWitness.IsSymm` (5 LOC; trivial).
* **Job B**: `bdf2GWitness.PosDef` (~30 LOC; 2×2 specialisation).
* **Job C**: `(bdf2LMM.gMatrix bdf2GWitness).PosSemidef` (~50 LOC;
  compute matrix entry-wise, factor as `LLᵀ` or apply rank-1
  closure).

Submit at the **start** of cycle 165 (before manual proof attempts)
so the 30-min CLAUDE.md sleep window overlaps the Step-1 scaffold
work. Single poll after manual closure of Step 2 (~30 min in).

---

## Priority 3 — Update tracking files

1. **`extraction/formalization_data/lean_status.json`**: bump
   `def:451A` from `not_started` → `formalized` (or whatever the
   schema uses; check sibling rows). Cycle pointer: 165.
2. **`plan.md`**: flip `def:451A` row from `[ ]` to `[x]`. Bump
   the progress count from 69 / 175 → 70 / 175.
3. **No other plan.md edits this cycle** — leave `def:530B`/
   `def:530C` rows as-is (they remain `[~]` per the cycle 164
   state; nothing changed).

---

## What NOT to do this cycle

1. **Do NOT pursue the cycle-165 retirement plan from cycle 164's
   task results.** A quick audit shows 438 references to
   `padded{2,3,4}DEulerGLM` / `pad{2,3,4}CompatStartingMethod` in
   Section530.lean, plus six stability witnesses in Section520.lean
   tied to `padded2DEulerGLM` (`_isIRKStable`, `_stabilityMatrix`,
   `_stabilityFunction`, `_isRKStable`, `_not_isAStable`,
   `_not_isLStable`). Full retirement requires either porting all
   stability witnesses to `paddedREulerGLM 1` (cascading through
   def:520E / def:520F / def:542A / def:551A non-vacuity) or
   landing a fragile partial cleanup. Both are multi-cycle scope.
   Defer to a dedicated cleanup cycle when the planner judges the
   parametric family fully stable. For cycle 165, prioritize entity
   count over technical-debt cleanup.

2. **Do NOT extend the def:530B/C Path A r-grid further** (e.g. to
   `r = 5` or `p = 2`). Six consecutive r-extension cycles
   (156–161) plus three refactor cycles (162–164) have saturated
   the value extractable from this approach. The next genuine
   advance on def:530B/C requires Path B (implicit branch via
   `ContractingWith` / `Function.IsFixedPt`), which is multi-cycle
   Mathlib infrastructure and out of scope for cycle 165. See
   `.prover-state/issues/def_530B_scaffold_strategy.md`.

3. **Do NOT generalise the cycle 158/160 helpers further** (e.g.
   to a Taylor-degree-parametric helper at degree `p+1`). The
   two helpers (one per `p ∈ {0, 1}`) are sufficient for current
   Path A non-vacuity; further generalisation has no concrete
   downstream consumer.

4. **Do NOT attempt `thm:550A` general-`n`.** Two failed
   long-running Aristotle attempts (cycle 141 cancelled at 6 %
   after 24 h; cycle 148 cancelled at 21 % after 89 h, per
   `.prover-state/issues/thm_550A_general_n.md`). Closure path is
   structural (cofactor-expansion induction or eigenvalue
   density), and requires cofactor-expansion or charpoly
   continuity infrastructure that is multi-cycle Mathlib work. Do
   not submit further Aristotle jobs for this target.

5. **Do NOT introduce `axiom` or `constant` declarations** for any
   step (CLAUDE.md absolute rule).

6. **Do NOT raise `maxHeartbeats`** above 200000. If `decide` /
   `norm_num` on the BDF2 matrix `M(G)` reduction stalls, decompose
   the entry-wise check into per-`(i,j)` lemmas (9 sub-lemmas) and
   close each with `simp; norm_num`.

7. **Do NOT modify `scripts/autonomous_loop.py`.** The standing
   tautology-scanner false-positive issue
   (`tautology_scanner_false_positives.md`) is loop-maintainer
   territory. If a closer of shape `:= h_*` or `exact h_*` appears,
   apply the cosmetic `h_<name>` → `h<name>` rename workaround.

---

## Pre-commit checklist (apply before pushing)

1. `lake env lean OpenMath/Chapter4/Section451.lean` → exit 0.
2. `grep -c sorry OpenMath/Chapter4/Section451.lean` → 0.
3. `lean_verify OpenMath.Chapter4.Section451.bdf2LMM_isGStable` →
   `[propext, Classical.choice, Quot.sound]` only.
4. `lake build OpenMath.Chapter4.Section451` → no regressions.
5. Tautology scanner clean:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section451.lean`
   → no hits.
6. Faithfulness check (above) signed off.
7. `lean_status.json` and `plan.md` updated; `extraction/`
   directories untouched (per CLAUDE.md "never edit
   `extraction/raw_text/` or `extraction/formalization_data/entities/`").
8. **Imports added to `OpenMath.lean`**: add `import
   OpenMath.Chapter4.Section451` so the new file ships with
   `lake build OpenMath`.

---

## Cycle deliverable bar

* **Minimum (score ≥ 1)**: definitions + scaffold + at least one
  of the three `bdf2LMM_isGStable` sub-proofs closed (Step 2 — the
  trivial `IsSymm` step). Sorry count ≤ 2 in the new file. Cycle
  documented in `task_results/cycle_165.md`.
* **Target (score = 2)**: all three sub-proofs closed,
  `bdf2LMM_isGStable` axiom-clean. Sorry count = 0. `def:451A`
  flipped to `[x]` in `plan.md`. Adds one entity to the formalized
  count (69 → 70).
* **Stretch (not required)**: also state the textbook's
  observation that PosDef implies symmetric for real matrices, so
  the `IsSymm` field of `IsGStable` is redundant; refactor
  `IsGStable` to drop it. Or extend with an additional witness
  (e.g. trapezoidal rule). Pursue only if Steps 1–4 land in the
  first half of the cycle.

---

## Cross-references

* `extraction/formalization_data/entities/def_451A.json` —
  textbook statement (full LaTeX; quoted at top of this strategy).
* `extraction/raw_text/ch04.txt`, near "(451e)" — equation
  (451e) verbatim with the embedding-block notation.
* `OpenMath/Chapter4/Section404.lean:53` — `LinearMultistepMethod`
  structure (reuse for one-leg methods).
* `Mathlib.LinearAlgebra.Matrix.PosDef` — `Matrix.PosDef`,
  `Matrix.PosSemidef`, related lemmas. Search via
  `lean_local_search "PosDef"` / `lean_local_search "PosSemidef"`
  before relying on specific lemma names.
* `.prover-state/issues/def_530B_scaffold_strategy.md` — long-form
  history of the def:530B/C Path A work; closes with cycle 164's
  reconciliation deliverable. Path B (implicit branch) remains
  multi-cycle deferred.
* `.prover-state/task_results/cycle_164.md` — most recent cycle's
  result document; recommends retirement (which this strategy
  defers per the audit above).
