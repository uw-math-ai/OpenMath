# Cycle 165 Results

## Worked on

`def:451A` — Butcher §451 G-stability for one-leg / linear multistep
methods. New file `OpenMath/Chapter4/Section451.lean` containing:

* §451 vector/matrix infrastructure (extending `Section404`'s
  `LinearMultistepMethod` namespace):
  * `LinearMultistepMethod.alphaVec` — textbook §451 α-vector
    `(1, -α₁, …, -α_k)` realised as the entrywise negation
    `i ↦ -M.α i` (since our LMM convention has `M.α 0 = -1`).
  * `LinearMultistepMethod.betaVec` — textbook β-vector, identical to
    `M.β`.
  * `gTopLeft`, `gBottomRight` — the two block-embeddings of a
    `Fin k × Fin k` matrix into a `Fin (k+1) × Fin (k+1)` matrix
    (top-left and bottom-right respectively).
  * `LinearMultistepMethod.gMatrix M G` — Butcher (451e):
    `α βᵀ + β αᵀ - [G 0; 0 0] + [0 0; 0 G]`.
  * `LinearMultistepMethod.IsGStable` — Definition 451A: existence of
    a symmetric positive-definite `G` such that `M.gMatrix G` is
    PSD.
* Non-vacuity (textbook worked example, p. 363):
  * `bdf2LMM` — BDF2 as a 2-step LMM with
    `α 0 = -1, α 1 = 4/3, α 2 = -1/3`, `β 0 = 2/3, β 1 = β 2 = 0`.
  * `bdf2GWitness` — the textbook witness
    `G = !![10/9, -4/9; -4/9, 2/9]`.
  * `bdf2RankOneVec` — the rank-1 generator `(1, -2, 1) : Fin 3 → ℝ`.
  * `bdf2GWitness_isSymm`, `bdf2GWitness_posDef`,
    `bdf2_gMatrix_eq_smul_vecMulVec`, `bdf2_gMatrix_posSemidef`,
    `bdf2LMM_isGStable` — all closed, axiom-clean.
* `OpenMath/Chapter4.lean` updated to import the new file.

## Approach

Followed the cycle-165 strategy verbatim: pivot to a fresh `[ ]`
entity rather than chase the cycle-164 def:530B/C retirement (which
the strategy correctly identifies as a multi-cycle cleanup).

**Sorry-first scaffold**: opened a fresh `Section451.lean` with the
five definitions plus three named sub-lemmas
(`bdf2GWitness_isSymm`, `bdf2GWitness_posDef`,
`bdf2_gMatrix_eq_smul_vecMulVec`) and the orchestrating
`bdf2LMM_isGStable`. After the first compile pass, two structural
issues surfaced and were fixed before any proof work:

1. The first pass declared the §451 helpers in the
   `Section451.LinearMultistepMethod` namespace, which Lean
   rejected since the structure lives in `Section404`. Solution:
   bracket the §451 helpers between `namespace
   OpenMath.Chapter4.Section404 ... end` so dot-notation
   `M.alphaVec`, `M.gMatrix`, etc. resolves correctly.
2. `bdf2LMM` and `bdf2GWitness` needed `noncomputable` because
   `Real.instDivInvMonoid` is noncomputable.

After those fixes the file compiled with two real sorries
(`bdf2GWitness_posDef` and `bdf2_gMatrix_eq_smul_vecMulVec`); the
`isSymm` step was a 2-line `ext + fin_cases + rfl` and the
`posSemidef` step reduced to scaling
`Matrix.posSemidef_vecMulVec_self_star` by `2/9`.

**Aristotle**: submitted the file with a prompt sketching both
proofs as a backup. Then immediately attacked both sorries
manually via `lean_multi_attempt` and `lean_run_code`.

**Closing the matrix equality**: `ext i j; fin_cases i <;>
fin_cases j <;> simp [<defs>, Matrix.vecMulVec_apply, …] <;>
norm_num` closed all nine entries in one tactic.

**Closing PosDef**: routed through
`Matrix.posDef_iff_dotProduct_mulVec` (so we work with
`Fin 2 → ℝ` rather than `Fin 2 →₀ ℝ`). The Hermitian field is a
2-line `ext + fin_cases + simp`. The quadratic-form positivity
required two steps:

1. Compute the dot product as
   `(10/9) (x 0)² - (8/9) (x 0) (x 1) + (2/9) (x 1)²` via
   `simp [bdf2GWitness, dotProduct, Fin.sum_univ_two,
   Matrix.mulVec]` followed by `ring`.
2. Case-split on `x 0 ≠ 0 ∨ x 1 ≠ 0` (forced by the assumption
   `x ≠ 0`) and discharge each branch with
   `nlinarith [sq_nonneg (5*(x 0) - 2*(x 1)), sq_nonneg (x 1),
   sq_nonneg (x 0), mul_self_pos.mpr <branch hyp>]`.

   The hint `sq_nonneg (5 x 0 - 2 x 1)` is the algebraic
   identity `45 · ((10/9) a² - (8/9) ab + (2/9) b²) =
   2(5a - 2b)² + 2 b²` — which exhibits the quadratic form as a
   non-negative combination of two squares, with the `5a - 2b`
   completion arising from the (2/5)-scaled diagonal entry.

The Aristotle job was no longer needed; cancellation returned 404
("Project cannot be canceled"), so it was left to run unattended
(no further interaction).

## Result

**SUCCESS — full target.**

* Sorry count in `OpenMath/Chapter4/Section451.lean`: **0**.
* `lean_verify OpenMath.Chapter4.Section451.bdf2LMM_isGStable` →
  `[propext, Classical.choice, Quot.sound]` only — axiom-clean.
* `lake build OpenMath.Chapter4.Section451` succeeds (8030 jobs).
* `def:451A` flipped from `[ ]` → `[x]` in `plan.md`; progress
  count `69 / 175` → `70 / 175`.
* `lean_status.json` updated: `def:451A` → `formalized`,
  symbol `OpenMath.Chapter4.Section404.LinearMultistepMethod.IsGStable`.
* `OpenMath.lean` indirectly imports the new file via
  `OpenMath/Chapter4.lean`.

## Faithfulness check

### `LinearMultistepMethod.alphaVec`, `betaVec`, `gTopLeft`, `gBottomRight`, `gMatrix`

These are §451 *infrastructure* (the textbook's α-vector, β-vector,
and embedding-block notation). They are not stand-alone named
mathematical objects in Butcher's text; they are the inline
notation used to set up equation (451e). Their faithfulness is
chained into `IsGStable`'s.

### `LinearMultistepMethod.IsGStable` (entity `def:451A`)

* Textbook (`entities/def_451A.json`):
  > A one-leg method `[α, β]` is `G-stable' if `M` given by (451e)
  > is positive semi-definite.
  with (451e):
  > `M = αβᵀ + βαᵀ − [G 0; 0 0] + [0 0; 0 G]`.
* Lean: `∃ G, G.IsSymm ∧ G.PosDef ∧ (M.gMatrix G).PosSemidef`.
* Captures: **same content**, with the explicit existential reading
  of the unstated quantifier on `G`. Faithfulness considerations:
  * The textbook's "if M is positive semi-definite" is parameterised
    by an unstated `G`; the standard reading is `∃ G`. The same
    page exhibits a *specific* `G` for BDF2, confirming the
    existence reading.
  * `IsSymm` is included alongside `PosDef`. For real matrices,
    `PosDef` already implies `IsHermitian = IsSymm`, so this is
    *strictly equivalent* to the slimmer `∃ G, G.PosDef ∧ …`. The
    textbook's display
    `G = (g_11 g_12 / g_12 g_22)` shows `G` written symmetrically
    by parameterisation, so keeping the explicit symmetry hypothesis
    matches the textbook one-to-one. (Stretch refactor — drop
    `IsSymm` — is deferred; cosmetic only.)
* Definition smuggling: the predicate is the Lean equivalent of
  the *matrix* PSD condition, not a downstream consequence (e.g.
  "stable for all dissipative IVPs"). ✓

### `bdf2LMM`

* Textbook: BDF2 = `[α(z), β(z)] = (1 - (4/3)z + (1/3)z², 2/3)`.
* Lean: `α 0 = -1, α 1 = 4/3, α 2 = -1/3`, `β 0 = 2/3,
  β 1 = β 2 = 0`. Captures: **same content**, accounting for our
  LMM convention `α 0 = -1` (so the textbook polynomial coefficients
  `(1, -4/3, 1/3)` become `α-vector = (1, -4/3, 1/3) = -M.α`).

### `bdf2GWitness`

* Textbook: `G = ((10/9, -4/9), (-4/9, 2/9))`. Lean: literal
  `!![10/9, -4/9; -4/9, 2/9]`. Captures: **same content**.

### `bdf2RankOneVec`

* This is *not* a textbook-named entity; it is a helper vector
  `(1, -2, 1)` used internally to exhibit `M(G)` as a rank-1 PSD
  matrix `(2/9) · u · uᵀ`. The doc-string flags this. Adding it
  via `extensions/helper_entities.json` is unnecessary because it
  has no downstream consumers outside this file.

### Theorems

* `bdf2GWitness_isSymm`, `bdf2GWitness_posDef`,
  `bdf2_gMatrix_eq_smul_vecMulVec`, `bdf2_gMatrix_posSemidef`,
  `bdf2LMM_isGStable`:
  * Tautology check: none of the conclusions appear verbatim as a
    hypothesis. ✓
  * Identity check: the proofs are non-trivial (`refine` / `rw` /
    `nlinarith` / explicit witness construction). None is `exact h`,
    `:= h_*`, or `:= id`. ✓
  * Hypothesis strength check: all four sub-lemmas are
    hypothesis-free; the BDF2 witness is unconditional. ✓
  * Tautology scanner clean (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$
    |:=\s*id\s*$' OpenMath/Chapter4/Section451.lean` → no hits). ✓

## Dead ends

* **First simp attempt without unfolding `vecHead`/`vecTail`**: the
  stock `simp [Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two,
  ...]` simplified the dot product into `vecHead x * (vecHead x *
  (10/9) + ...)` form rather than `(x 0) * ((x 0) * (10/9) + ...)`,
  which `nlinarith` could not pattern-match because the squares
  hint mentioned `x 0`/`x 1`, not `vecHead x`. The fix was a
  `have key : ... = ... := by simp [...]; ring` step that
  rewrites the dot product into an explicit polynomial in
  `x 0, x 1` *before* `nlinarith`.

* **`Matrix.dotProduct` constant**: the constant is
  `_root_.dotProduct` (no `Matrix.` prefix), exposed via
  `open Matrix`. First attempt with `simp [Matrix.dotProduct, ...]`
  failed with `Unknown constant`; resolved by switching to
  `simp [dotProduct, ...]` after `open Matrix`.

* **`*ᵥ` notation parse error**: with only
  `open OpenMath.Chapter4.Section404 (LinearMultistepMethod)` the
  `*ᵥ` infix operator was rejected with an obscure
  `Mathlib.Tactic.subscriptTerm` elaboration error. Adding
  `open Matrix` to the §451 namespace fixed it.

## Discovery

* **Cross-namespace dot-notation pattern**: when adding helpers to
  a structure declared in a sister `Section`, declaring them under
  `namespace OpenMath.Chapter4.Section404 ... end` (rather than
  inside the new `Section451` namespace) is the cleanest way to
  preserve `M.alphaVec` / `M.gMatrix` dot-notation. This pattern is
  reusable for future inter-section infrastructure additions
  (e.g. spectral helpers on `LinearMultistepMethod`).

* **`Matrix.posSemidef_vecMulVec_self_star` for real PSD rank-1**:
  the cleanest way to prove a small explicit rank-1 PSD matrix
  is to factor as `(scale) • Matrix.vecMulVec u u` (with `scale ≥
  0`), then use `Matrix.PosSemidef.smul` and the cited lemma. The
  matrix-equality side is dispatched by `ext + fin_cases <;> simp;
  norm_num` in seconds. This pattern will recur whenever we
  exhibit a small explicit PSD witness (e.g. for further G-stable
  LMM examples or for thm:454A).

* **`Matrix.posDef_iff_dotProduct_mulVec` over Finsupp form**: the
  `Matrix.PosDef` definition uses `Finsupp` quantification, but the
  `_iff_dotProduct_mulVec` companion converts to the standard
  `Fin n → R` form. Always route 2×2 PD proofs through the iff.

* **Cycle 164 retirement deferral was correct**: a quick check
  before pivoting confirmed the strategy's audit (438 references,
  six stability witnesses in Section520.lean) — the multi-cycle
  cleanup would have produced a fragile partial commit. Single-
  entity-per-cycle progress on a fresh `[ ]` entity was the right
  call.

## Suggested next approach

The natural next move is to **claim more entities in Chapter 4**
that, like `def:451A`, are dependency-free or near-trivial-
dependency. Candidates from `plan.md`:

* `thm:454A` ("A G-stable LMM is A-stable") — the *next*
  textbook entity after `def:451A`, depends directly on it.
  Proof in Butcher §454 is two paragraphs, structural (compute
  `W* M W` and apply (451e) PSD). Would also produce the first
  `IsGStable`-consumer, validating the definition is doing the
  right work. Recommended priority for cycle 166.

* `def:402A` is already done; `def:422B` ("underlying one-step
  method") and `def:442A` ("principal sheet") are dependency-light
  and cheap.

* For def:530B/C retirement: if/when the planner judges the
  parametric family fully stable, the cycle 164 task results
  document remains accurate as a cleanup playbook. No urgency.

* **Stretch goal not pursued this cycle**: the textbook's
  observation that "PosDef ⇒ IsSymm" makes the `IsSymm` field of
  `IsGStable` redundant. Refactoring to drop it would be cosmetic
  and would slightly simplify downstream consumers (e.g. thm:454A);
  defer to whoever needs it.

* **Note on Aristotle**: the cycle-165 batch submission to
  Aristotle was orphaned (couldn't be cancelled before manual
  closure). Future cycles should consider waiting ~30 s after
  submission to confirm the project entered a non-cancellable
  state, or just deferring submission until the manual attempt
  has been timeboxed.
