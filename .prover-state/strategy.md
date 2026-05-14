# Cycle 241 Strategy

## Snapshot

- Sorry count across the repo: **0**.
- Cycle 240 shipped §441 closed-form witnesses `cInverseLog 2 = -2/45`
  and `cInverseLog 3 = -22/945` + negativity corollaries + cross-checks
  against cycle 238's general `cInverseLog_neg`, all axiom-clean.
- No pending Aristotle results.
- §441 GPFS smoke test on `Section441.lean` has timed out **44
  consecutive cycles** (loop-maintainer territory; do NOT retry).

Since the repo is sorry-free and no theorem is mid-restructuring, the
cycle 241 deliverable must be a **fresh theorem from plan.md**. Cycle
240's "Suggested next approach" recommended **Option B (§302
tree-combinatorics)** — but on closer inspection, every §302 entity
(`thm:302A`, `thm:302B`, `thm:302C`, `thm:304A`) needs new
combinatorial infrastructure (`α(t)`, `β(t)`, `θ_k = #rooted trees of
order k`) that does not yet exist. Building it faithfully without
slipping into definition smuggling is a 2–3 cycle project per entity.

**Pivot**: target **`thm:523A` (Non-linear stability, §523)** instead.
Its statement is a pure algebraic identity (no PSD assumption needed
for the identity itself — that hypothesis is only consumed by the
corollary `thm:523B`), all infrastructure already exists in §510/§512,
and the proof reduces to `linear_combination` / `ring` after expanding
quadratic forms. Single-cycle ship rate is high; new file
`OpenMath/Chapter5/Section523.lean`.

## Priorities (in order)

### Priority 0 — Skip the GPFS smoke test
Do **NOT** attempt `time timeout 60 lake env lean
OpenMath/Chapter4/Section441.lean`. 44 consecutive timeouts since
cycle 182. The pathology is documented in
`.prover-state/issues/cycle_182_gpfs_slowness.md` and remains
loop-maintainer territory. Append a one-line entry to that file's
"GPFS timeout log" only if you happen to run it for some other
reason; do not run it just to update the log.

### Priority 1 — Ship `thm:523A` in `OpenMath/Chapter5/Section523.lean`

**Textbook statement (Butcher §523, verbatim from
`extraction/formalization_data/entities/thm_523A.json`)**:

> Let `Y` denote the vector of stage values, `F` the vector of
> stage derivatives and `y^{[n−1]}`, `y^{[n]}` the input and output
> from a single step of a GLM `(A, U, B, V)`. Assume `M` is a PSD
> `(s+r) × (s+r)` matrix where
>
>     M = [[D A + Aᵀ D − Bᵀ G B,    D U − Bᵀ G V],
>          [Uᵀ D − Vᵀ G B,           G − Vᵀ G V  ]]
>
> with `G` PSD `r × r` and `D` PSD diagonal `s × s`. Then
>
>     ‖y^{[n]}‖²_G = ‖y^{[n−1]}‖²_G + 2⟨h·F, Y⟩_D − ‖h·F ⊕ y^{[n−1]}‖²_M.

**Key faithfulness observation**: the **identity** above does NOT
require `M`, `G`, or `D` to be PSD. The PSD hypotheses only enter
for the corollary `thm:523B` (`PSD M ⇒ ‖y[n]‖² ≤ ‖y[n−1]‖²`). State
`thm:523A` as an **unconditional algebraic identity** parameterised by
the matrices `D`, `G`, the GLM, and an arbitrary stage vector `Y`,
`F`, `y_prev`, `y_next` satisfying the two step equations:

```
Y i      = h · ∑_j A_{ij} F j + ∑_j U_{ij} y_prev j
y_next i = h · ∑_j B_{ij} F j + ∑_j V_{ij} y_prev j
```

This is the same shape as `IsGLMSolution`'s per-step witness
(`OpenMath/Chapter5/Section512.lean:91-98`). Do NOT thread
`IsGLMSolution` into the signature — its existential structure and
its tie to a specific `f` are both irrelevant to the algebraic
identity. Take `Y`, `F`, `y_prev`, `y_next` as free vectors with the
step equations as explicit hypotheses (`hStage`, `hOut`).

**Concrete target shape — adapt syntax to whatever Mathlib API makes
the proof close cleanly**:

```lean
namespace OpenMath.Chapter5.Section510

open Matrix BigOperators

variable {s r : ℕ}

/-- The (523b) block matrix `M(D, G, A, U, B, V)`. -/
noncomputable def GeneralLinearMethod.algebraicStabilityMatrix
    (M : GeneralLinearMethod s r) (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin s ⊕ Fin r) (Fin s ⊕ Fin r) ℝ :=
  Matrix.fromBlocks
    (D * M.A + M.A.transpose * D - M.B.transpose * G * M.B)
    (D * M.U - M.B.transpose * G * M.V)
    (M.U.transpose * D - M.V.transpose * G * M.B)
    (G - M.V.transpose * G * M.V)

/-- **Theorem 523A** (Butcher §523, p. 422) — Non-linear stability
identity ... [docstring] -/
theorem GeneralLinearMethod.algebraicStability_identity
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, M.A i j * F j) + ∑ j, M.U i j * y_prev j)
    (hOut   : ∀ i, y_next i = h * (∑ j, M.B i j * F j) + ∑ j, M.V i j * y_prev j) :
    y_next ⬝ᵥ (G *ᵥ y_next)
      = y_prev ⬝ᵥ (G *ᵥ y_prev)
        + 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y))
        - (Sum.elim (fun i => h * F i) y_prev)
            ⬝ᵥ (M.algebraicStabilityMatrix D G *ᵥ Sum.elim (fun i => h * F i) y_prev) := by
  sorry  -- close after sorry-first scaffold
```

Use whichever Mathlib quadratic-form convention closes faster
(`x ⬝ᵥ (A *ᵥ x)` vs `(x ᵥ* A) ⬝ᵥ x` — both encode `xᵀ A x`, pick one
and be consistent). Cycle 169's `Section454.lean` and cycle 033's
`Section357.lean` are the closest precedents.

**Proof sketch**:

1. Substitute `hOut` into `y_next ⬝ᵥ (G *ᵥ y_next)`. Expand
   `(h B F + V y_prev)ᵀ G (h B F + V y_prev)` into four bilinear
   terms:
   `h² Fᵀ Bᵀ G B F + h Fᵀ Bᵀ G V y_prev + h y_prevᵀ Vᵀ G B F + y_prevᵀ Vᵀ G V y_prev`.
2. Substitute `hStage` into `2 · ⟨hF, Y⟩_D = 2 · (hF)ᵀ D Y`. Expand
   `2 (hF)ᵀ D (h A F + U y_prev)` to
   `2 h² Fᵀ D A F + 2 h Fᵀ D U y_prev`.
3. Expand `(hF ⊕ y_prev)ᵀ M (hF ⊕ y_prev)` against the `fromBlocks`
   definition. The top-left block contributes
   `h² Fᵀ (DA + AᵀD − BᵀGB) F`, the top-right `h Fᵀ (DU − BᵀGV) y_prev`,
   the bottom-left `h y_prevᵀ (UᵀD − VᵀGB) F`, the bottom-right
   `y_prevᵀ (G − VᵀGV) y_prev`.
4. RHS − LHS rearrangement: every `BᵀGB`/`VᵀGV`/`BᵀGV`/`VᵀGB` term
   from step 3 cancels against the corresponding term from step 1,
   leaving `+ y_prevᵀ G y_prev` (the `G` from `(G − VᵀGV)`) and
   `+ 2 h² Fᵀ DA F + 2 h Fᵀ DU y_prev` (steps 2's expansion), against
   `−h²·(Fᵀ DA F + Fᵀ AᵀD F) − h (Fᵀ DU y_prev + y_prevᵀ UᵀD F)`
   from step 3's block contributions. The `Fᵀ DA F = Fᵀ AᵀD F`
   symmetry (real scalars, transpose-invariant under
   `dotProduct_comm`) and the analogous `Fᵀ DU y_prev = y_prevᵀ UᵀD F`
   collapse the doubled terms.
5. After collecting, residue is `y_prevᵀ G y_prev = ‖y_prev‖²_G`.
   `ring` (or `linear_combination` with explicit substitutions from
   `hStage`/`hOut` as hypotheses) closes.

**Risks** (pre-flagged so the worker doesn't get blocked):

- **R1 — `Sum.elim` / `fromBlocks` quadratic form unfolding**: the
  `(Sum.elim a b) ⬝ᵥ ((fromBlocks A B C D) *ᵥ Sum.elim a b)` shape
  may not unfold cleanly by `simp [Matrix.fromBlocks, Sum.elim]`
  alone. Fall back to a helper lemma
  `Matrix.fromBlocks_quadForm_apply` (or whatever Mathlib calls it —
  search via `lean_loogle "fromBlocks ⬝ᵥ"` / `"fromBlocks *ᵥ"`). If
  missing, build a private helper that unfolds the M-norm into
  four block quadratic forms by direct `Sum.elim_inl` / `Sum.elim_inr`
  case-splits. Cycle 169's `Section454.lean`
  (`gTopLeft_quadForm_eq` / `gBottomRight_quadForm_eq`) is the
  decomposition precedent.
- **R2 — cross-term sign collapse**: the pair `Fᵀ Bᵀ G V y_prev`
  and `y_prevᵀ Vᵀ G B F` are equal (both encode the same real
  scalar). Use `Matrix.dotProduct_comm` or
  `Matrix.dotProduct_mulVec` plus transpose-of-product
  (`Matrix.transpose_mul`) to bridge. The cycle 169 `Section454.lean`
  `mul_re_of_real_complex` / `star_beta_alpha_re_eq_star_alpha_beta_re`
  pattern is the analog for complex-valued cycle 167–169 work.
- **R3 — diagonal `D` vs full `D`**: the textbook says `D` is
  diagonal and PSD, but the **identity** holds for **any** matrix
  `D : Matrix (Fin s) (Fin s) ℝ` whose symmetric part appears in the
  cross-term `Fᵀ DA F + Fᵀ AᵀD F = 2 Fᵀ (D's sym part) A F` (more
  precisely the proof goes through whenever `Fᵀ DA F = Fᵀ AᵀD F`,
  which holds for **symmetric** `D` — including all PSD diagonals
  and more). Two faithful framings:
  - (a) **Strict generalisation**: take `D` symmetric and document
    the diagonal weakening in the docstring. Strict generalisation
    of Butcher's theorem (every PSD diagonal is symmetric).
  - (b) **Even stricter**: take `D` arbitrary and use real-scalar
    commutativity `Fᵀ DA F = Fᵀ (DA)ᵀ F = Fᵀ AᵀDᵀ F = Fᵀ AᵀD F` only
    if `D = Dᵀ`. Without `D` symmetric, this collapses fails.
  
  **Recommendation**: go with (a) — take `D` as `Matrix.IsSymm D` or
  `Matrix.diagonal d` (the latter only if Mathlib gives you the
  `dᵀ = d` collapse for free). The diagonal-only restriction is
  perhaps the cleanest single-cycle option since `Matrix.diagonal`
  is automatically symmetric and the proof has fewer cases.
- **R4 — `linear_combination` over matrix-valued sums**: may or may
  not fire. Fallback: bring everything into `Finset.sum` form with
  `simp [Matrix.mulVec, Matrix.vecMul, dotProduct, ...]`, distribute
  sums via `Finset.sum_add_distrib` / `Finset.mul_sum`, and close
  with `ring` per-summand via `Finset.sum_congr rfl`. Pattern from
  cycles 124, 167, 169.
- **R5 — `IsGLMSolution` vs free `Y, F` hypothesis form**: do NOT
  state `thm:523A` directly against `IsGLMSolution` — that
  predicate is existential in `Y` and tied to a specific `f`. The
  algebraic identity is per-`Y`-and-`F`, with no existential and no
  `f`. Decoupling them is the right call. Document the
  `IsGLMSolution`-vs-`hStage/hOut` framing choice in the docstring.

**Non-vacuity witness (Priority 1.B)**: After the main identity
lands, ship a corollary at a concrete GLM. The cleanest:

```lean
/-- Non-vacuity witness at `explicitEulerGLM`. -/
example (D : Matrix (Fin 1) (Fin 1) ℝ) (G : Matrix (Fin 1) (Fin 1) ℝ)
    (h : ℝ) (F Y : Fin 1 → ℝ) (y_prev y_next : Fin 1 → ℝ)
    (hStage : ∀ i, Y i = h * (∑ j, explicitEulerGLM.A i j * F j) +
                          ∑ j, explicitEulerGLM.U i j * y_prev j)
    (hOut : ∀ i, y_next i = h * (∑ j, explicitEulerGLM.B i j * F j) +
                            ∑ j, explicitEulerGLM.V i j * y_prev j) :
    y_next ⬝ᵥ (G *ᵥ y_next) = y_prev ⬝ᵥ (G *ᵥ y_prev) + ... :=
  explicitEulerGLM.algebraicStability_identity D G h F Y y_prev y_next hStage hOut
```

This `example` confirms the theorem ELABORATES at a concrete `(s, r)
= (1, 1)` GLM and that the type unifies with `explicitEulerGLM`. It
does NOT require manually evaluating the identity at concrete `D, G`
— that's a separate (harder) check that the algebraic identity
*reduces correctly* at concrete instances, optional stretch goal.

A second `example` checking `trivialZeroGLM` at `D = 0, G = 0`,
`F = 0, Y = 0, y_prev = 0, y_next = 0` would be the most degenerate
witness (both sides `0 = 0`) — skip unless time permits.

**Headline conclusion**: cycle 241 ships the algebraic identity
`thm:523A`. The textbook also states the inequality form
`‖y_next‖²_G ≤ ‖y_prev‖²_G + 2⟨hF, Y⟩_D` (which follows from PSD `M`
⇒ M-norm term ≥ 0); that's `thm:523B`, ship in cycle 242 or later
as a one-line `linarith` corollary.

### Priority 2 — Update `lean_status.json` and `plan.md`

After Priority 1 lands:
- Bump `extraction/formalization_data/lean_status.json` row for
  `thm:523A`: `unformalized` → `formalized`, set `lean_symbol` to
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_identity`
  (or whatever final name is chosen), set `last_cycle` to 241.
- Update `plan.md` Chapter 5 §523 row: `[ ] thm:523A` → `[x] thm:523A`,
  noting the file path `OpenMath/Chapter5/Section523.lean`.
- Update Chapter5 progress count in `plan.md` header: `70 / 175` →
  `71 / 175`.

### Priority 3 (stretch only — do NOT push if Priority 1 takes the full cycle)

Open `thm:523B` as a one-line corollary IF `Matrix.PosSemidef` gives
a usable `xᵀ M x ≥ 0` lemma:

```lean
theorem GeneralLinearMethod.algebraicStability_inequality
    (M : GeneralLinearMethod s r)
    (D : Matrix (Fin s) (Fin s) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ)
    (hM : (M.algebraicStabilityMatrix D G).PosSemidef)
    (h : ℝ) (F Y : Fin s → ℝ) (y_prev y_next : Fin r → ℝ)
    (hStage : ...) (hOut : ...) :
    y_next ⬝ᵥ (G *ᵥ y_next) ≤
      y_prev ⬝ᵥ (G *ᵥ y_prev) + 2 * ((fun i => h * F i) ⬝ᵥ (D *ᵥ Y)) := by
  have hid := M.algebraicStability_identity D G h F Y y_prev y_next hStage hOut
  have hM_nn := hM.dotProduct_nonneg (Sum.elim (fun i => h * F i) y_prev)
  linarith
```

Verify the Mathlib hook name via `lean_local_search
"Matrix.PosSemidef.dotProduct"` or
`lean_loogle "Matrix.PosSemidef _ → 0 ≤ _ ⬝ᵥ _"`. If the hook does
not exist with the right shape, defer `thm:523B` to a future cycle
rather than building the hook from scratch.

## Explicit anti-priorities — DO NOT do these

### Do NOT touch the GPFS-blocked §441 path
Cycles 182–240 have all skipped this. The 44-cycle pattern is
established. The cycle 182 draft + cycle 184 namespace fix (preserved
at `.prover-state/cycle_182_draft_section441.lean`) remain ready to
land once GPFS recovers — but recovery is loop-maintainer territory,
not worker territory.

### Do NOT pivot to §302 tree-combinatorics this cycle
Cycle 240 recommended §302 in its "Suggested next approach", but
**every §302 entity requires undefined combinatorial primitives**
(`α(t)`, `β(t)`, `θ_k`, plus their combinatorial-counting provenance).
Building those faithfully without slipping into definition smuggling
(see CLAUDE.md "Definition smuggling check") is a 2–3 cycle project
per entity. `thm:523A` ships in one cycle with no new infrastructure.

If a planner *really* wants to open §302 in a future cycle, the
recommended scoping is:
1. Cycle X: define `RootedTree.numberings` (= α) and a
   `RootedTree.labelings` (= β) as combinatorial recursions matching
   the textbook (NOT as closed forms), with non-vacuity at concrete
   trees (`vertex`, `τ²`, `tau3Bushy`).
2. Cycle X+1: prove `thm:302A` formulas (302a)/(302b) as **theorems**
   about the cycle-X definitions, using existing `RootedTree.order` /
   `symmetry` / `density` from §301.
3. Cycle X+2: open `thm:302C` (`A_n = (n−1)!`, `B_n = n^(n−1)` —
   Cayley) as a more ambitious follow-up.

This is **not** cycle 241's scope.

### Do NOT touch §383 abstract-quotient infrastructure
Cycle 239 just shipped `elementaryWeightQ_phi` and five non-vacuity
witnesses. The §383 line should settle for at least one more cycle
before the next abstract-quotient deliverable. See cycle 240 task
results' deferral.

### Do NOT touch §380 `thm:381G` / `thm:381H`
Still blocked on the `Equivalent → PhiEquivalent` direction (one of
three unresolved iff directions for `thm:381H`, see
`.prover-state/issues/thm_381H_deferred.md`). Multi-cycle B-series
work.

### Do NOT attempt §550 general-`n` infrastructure
Cycle 151 cancelled the Aristotle general-`n` job for `thm:550A`
at 21%; the deferral remains in force. Seven concrete-`n` stepping
stones (n = 1..7) are the empirical evidence base; further stepping
stones (`n = 8`) provide marginal value.

### Do NOT introduce `axiom` or raise `maxHeartbeats`
Standing CLAUDE.md constraint. `thm:523A`'s proof is pure algebra —
if it doesn't fit within 200000 heartbeats, decompose into named
per-block-quadratic-form helpers (cycle 167/169 precedent for the
§454 `gTopLeft_quadForm_eq` / `gBottomRight_quadForm_eq` pattern).

### Do NOT use `lean_inspect` or other deprecated tools
Use `lean_local_search` for known Mathlib symbol lookups, `lean_loogle`
for type-pattern queries, `lean_multi_attempt` for tactic
exploration, and `lean_verify` for axiom-cleanliness checks.

## Workflow

1. **Read** `extraction/formalization_data/entities/thm_523A.json` for
   the textbook statement.
2. **Read** `OpenMath/Chapter5/Section510.lean:63-200` (GLM structure
   + `IsStable`/`IsConsistent`/`explicitEulerGLM`) and
   `OpenMath/Chapter5/Section512.lean:91-99` (`IsGLMSolution` step
   shape) — confirm the step equations available.
3. **Create** `OpenMath/Chapter5/Section523.lean` with
   `import OpenMath.Chapter5.Section510` (NOT `Section512` — the
   free-`Y`-`F` form is cleaner per R5).
4. **Sorry-first scaffold**:
   - `algebraicStabilityMatrix` definition (no sorry — straight
     `Matrix.fromBlocks`).
   - `algebraicStability_identity` theorem stated, body `sorry`.
   - Run `lake env lean OpenMath/Chapter5/Section523.lean` — confirm
     compile passes with one sorry. **Do NOT proceed until this
     compiles cleanly.**
5. **Close the body of `algebraicStability_identity`**:
   - First attempt: substitute `hStage` and `hOut` into both sides
     via `rw [show ... from funext fun i => hOut i]` or `simp_rw`,
     then `simp [GeneralLinearMethod.algebraicStabilityMatrix,
      Matrix.fromBlocks_mulVec, Matrix.dotProduct_add,
      Matrix.add_dotProduct, Matrix.mulVec_add, Sum.elim_inl,
      Sum.elim_inr, dotProduct, Matrix.mulVec, Finset.mul_sum,
      Finset.sum_mul, ...] at *; ring`.
   - If that exceeds heartbeats: decompose into four named per-block
     quadratic-form helpers (`block_TL`, `block_TR`, `block_BL`,
     `block_BR` corresponding to the four `fromBlocks` components),
     prove each as a separate `private lemma` by `simp + ring`,
     then combine in the main theorem.
   - Aristotle as last-resort fallback: if both manual paths stall,
     submit the scaffolded file to Aristotle as a single job. Pool
     is empty; do not poll twice in cycle 241.
6. **Verify axiom-clean** via `lean_verify
   OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_identity`.
   Expected: `[propext, Classical.choice, Quot.sound]`.
7. **Write cycle-241 task results** documenting (a) what shipped,
   (b) faithfulness divergences (e.g. dropped diagonal-`D` /
   PSD-`M` / PSD-`G` hypotheses per R3 — these are strict
   generalisations, not weakenings of the theorem's content),
   (c) Priority 3 outcome (stretch shipped or deferred).
8. **Update** `lean_status.json` + `plan.md` per Priority 2.
9. **Commit** with message `Cycle 241 — §523 thm:523A algebraic
   stability identity SHIPPED`.

## Pre-commit faithfulness check

Per CLAUDE.md, before committing:

### For `def algebraicStabilityMatrix`
- [ ] Open `entities/thm_523A.json` and quote (523b). Confirm the
  Lean `fromBlocks` matches the textbook block layout entry-by-entry.
- [ ] Definition smuggling: does the def encode (523b)'s **structure**
  (block layout), or its **PSD property** (the hypothesis of the
  theorem)? It must encode the structure. The PSD property is a
  separate hypothesis, NOT folded into the definition.

### For `theorem algebraicStability_identity`
- [ ] Tautology check: the conclusion is a quadratic-form identity
  involving the LHS `‖y_next‖²_G` and the RHS sum-of-three-terms.
  Confirm it does NOT trivially reduce to `x = x` for arbitrary
  arguments.
- [ ] Identity check: is the proof a one-line `exact hStage` or
  similar? If yes — that's a bug, escalate. (Expected: 30–100 LOC of
  algebraic expansion.)
- [ ] Hypothesis-strength check: does the theorem use **all** of
  `hStage`, `hOut`, `D`, `G`, `A`, `U`, `B`, `V`? If any is unused
  in the proof body, the theorem is overstating its requirements.
  In particular: confirm `D` and `G` are NOT required to be PSD by
  this theorem. The PSD requirement is for `thm:523B` (the
  inequality form).
- [ ] Faithfulness divergence audit: document in the docstring that
  the textbook restricts `D` to PSD diagonal and `G` to PSD, but the
  identity itself holds for arbitrary `D` and `G` (or symmetric `D`
  per R3). This is a strict generalisation, faithful in the "the
  textbook fact is a corollary of our more general fact" sense.

### For the non-vacuity witness
- [ ] Confirm the `explicitEulerGLM` `example` typechecks — both
  sides of the identity unify with `s = r = 1` and the GLM's
  `A = 0, U = 1, B = 1, V = 1` entries.
- [ ] (Skipped if not pursued) Confirm `trivialZeroGLM` reduces
  trivially.
