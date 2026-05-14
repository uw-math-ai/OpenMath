# Cycle 241 Results

## Worked on
`thm:523A` (Butcher §523 algebraic stability identity for general linear
methods, p. 427). New file `OpenMath/Chapter5/Section523.lean` opens
§523 with `GeneralLinearMethod.algebraicStabilityMatrix` (equation
(523b) `fromBlocks` definition) and the headline theorem
`GeneralLinearMethod.algebraicStability_identity`.

## Approach

Per planner strategy: stated the textbook algebraic identity as an
**unconditional algebraic equality** parameterised by an arbitrary
matrix `D : Matrix (Fin s) (Fin s) ℝ` (subject only to `D.IsSymm`),
arbitrary `G : Matrix (Fin r) (Fin r) ℝ`, and free stage/output
vectors `(Y, F, y_prev, y_next)` related by the textbook step
equations as explicit hypotheses `hStage`, `hOut`. The PSD hypotheses
on `M`, `G` (and the diagonal restriction on `D`) are deferred to the
inequality corollary `thm:523B`.

The proof decomposes algebraically (no Aristotle needed):

1. **Step 1 (`hY`, `hyn`)** — Rewrite `Y` and `y_next` componentwise
   in matrix-vector form via `Matrix.mulVec`. The key conversion is
   `h * ∑_j A_{ij} F j = ∑_j A_{ij} * (h * F j) = (A *ᵥ (h • F)) i`,
   handled by `Finset.mul_sum` + `Finset.sum_congr` + `ring`.

2. **Step 2 (`hM_quad`)** — Expand the M-quadratic form
   `(α ⊕ y_prev) ⬝ᵥ (algebraicStabilityMatrix D G) *ᵥ (α ⊕ y_prev)`
   into 9 named bilinear-form terms via `Matrix.fromBlocks_mulVec` +
   `Sum.elim_comp_inl`/`inr` + `sumElim_dotProduct_sumElim` +
   `dotProduct_add` + `dotProduct_sub` + `Matrix.add_mulVec` +
   `Matrix.sub_mulVec` + `ring`.

3. **Step 3 (`lift` + `hLHS`)** — Define the adjoint helper
   `(M₁ *ᵥ x) ⬝ᵥ (M₂ *ᵥ y) = x ⬝ᵥ ((M₁ᵀ * M₂) *ᵥ y)` (proof:
   `dotProduct_mulVec` + `Matrix.vecMul_mulVec` + `← dotProduct_mulVec`).
   Apply it 4 times to expand `(Bα + Vu) ⬝ᵥ G *ᵥ (Bα + Vu)`,
   reassociate matrix products via `← Matrix.mul_assoc` + `ring`.

4. **Step 4 (`hCross`)** — Expand `2 * (α ⬝ᵥ D *ᵥ Y)` using `hY` and
   `Matrix.mulVec_mulVec` + `ring`.

5. **Step 5 (`hSymm1`, `hSymm2`)** — Collapse the two D-symmetric
   cross-term identities `αAᵀDα = αDAα` and `y_prev UᵀD α = α DU y_prev`
   via `Matrix.transpose_mul` + `hD` + `Matrix.mulVec_transpose` +
   `dotProduct_comm` + `← dotProduct_mulVec`. (Both rely on `Dᵀ = D`.)

6. **Step 6** — Combine via `rw` chain + `ring`.

Non-vacuity witness: an `example` at `explicitEulerGLM` (`(s, r) = (1, 1)`)
with `D = Matrix.diagonal d`, `G = Matrix.diagonal g`. Diagonal matrices
are automatically symmetric via `Matrix.isSymm_diagonal`.

No Aristotle calls this cycle (pure algebraic identity, manual closure
was tractable). No GPFS smoke test on `Section441.lean` (priority 0:
loop-maintainer territory, 44 consecutive timeouts).

## Result

**SUCCESS** — `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_identity`
verified axiom-clean: `#print axioms` returns
`[propext, Classical.choice, Quot.sound]`. The companion
`def algebraicStabilityMatrix` and the non-vacuity `example` at
`explicitEulerGLM` both elaborate. Whole-`Chapter5.lean` build succeeds.

## Faithfulness check

For each new `def` and `theorem` introduced this cycle:

### `def GeneralLinearMethod.algebraicStabilityMatrix`

- Entity ID and textbook statement (quoted from `entities/thm_523A.json`):
  > `M = ⎡⎣ DA + Aᵀ D − Bᵀ G B    D U − Bᵀ G V    ⎤⎦`
  > `    ⎣  Uᵀ D − Vᵀ G B          G − Vᵀ G V       ⎦`             (523b)
- Lean statement captures: **same content** (block-by-block).
  `Matrix.fromBlocks` constructs the `(s+r) × (s+r)` matrix indexed by
  `Fin s ⊕ Fin r`, with the four blocks
  `(D * M.A + M.A.transpose * D - M.B.transpose * G * M.B)`,
  `(D * M.U - M.B.transpose * G * M.V)`,
  `(M.U.transpose * D - M.V.transpose * G * M.B)`,
  `(G - M.V.transpose * G * M.V)` matching (523b) entry-by-entry.
- **Definition smuggling check**: the def encodes (523b)'s **block
  structure**, not its PSD property. The PSD hypothesis is a separate
  hypothesis attached to `thm:523B` (the inequality corollary), not
  folded into this definition. ✓

### `theorem GeneralLinearMethod.algebraicStability_identity`

- Entity ID and textbook statement (quoted from `entities/thm_523A.json`):
  > `\| y^{[n]} \|_G^2 = \| y^{[n-1]} \|_G^2 + 2 \langle hF, Y \rangle_D - \| hF \oplus y^{[n-1]} \|_M^2`
- Lean statement captures: **strict generalisation** along three axes,
  with the **identity content faithful**.
- Divergences (all strict generalisations of the textbook statement):
  1. **`D` symmetric, not PSD diagonal**. The identity holds whenever
     `Dᵀ = D`; this is implied by (and strictly weaker than) "PSD
     diagonal". The cross-term collapses (`αAᵀDα = αDAα`,
     `y_prev UᵀD α = α DU y_prev`) genuinely require `D` symmetric:
     without it, the identity fails. Justification: documented in file
     docstring; symmetric `D` is automatically obtained from PSD
     diagonal via `Matrix.isSymm_diagonal`, so any textbook instance
     is a special case.
  2. **`G` arbitrary (no PSD)**. The identity is a pure algebraic
     consequence of the (523b) block structure and does not consume
     a PSD hypothesis on `G`. The PSD hypothesis enters `thm:523B`'s
     inequality form only.
  3. **`M = algebraicStabilityMatrix D G` not assumed PSD**. Same
     reasoning as for `G`: the identity is purely algebraic. PSD-`M`
     is the input to `thm:523B`.
  4. **Decoupled from `IsGLMSolution`**. The textbook frames
     `(Y, F, y_prev, y_next)` as arising from a single step of the
     method (per `IsGLMSolution`'s existential closure), but the
     identity is per-fixed-`Y`-`F` and tied to no specific `f`.
     We take the step equations `hStage`, `hOut` as explicit
     hypotheses, mirroring the per-step witness inside
     `IsGLMSolution` (`OpenMath/Chapter5/Section512.lean:91-98`).
     Documented in file docstring.
- **Tautology check**: the conclusion `y_next ⬝ᵥ (G y_next) = ...`
  is a 4-term algebraic equality, none of whose terms appears
  verbatim as a hypothesis. ✓
- **Identity check**: the proof body is 6 named lemma steps + a final
  `rw` + `ring` (~60 LOC, not a one-liner). ✓
- **Hypothesis-strength check**: every hypothesis is used in the
  proof — `M` (via the blocks), `D` (via `hCross`, `hSymm1`, `hSymm2`),
  `G` (via `hLHS`), `hD : D.IsSymm` (via `hSymm1`, `hSymm2`), `h, F, Y`
  (via `hStage` → `hY`), `y_prev, y_next` (via `hOut` → `hyn`),
  `hStage` (via `hY`), `hOut` (via `hyn`). PSD hypotheses are
  **absent** (correctly, since they are not needed). ✓
- **Absent theorem check**: no `sorry`s or `theorem (...)` promises
  beyond the inequality form `thm:523B` (which is deferred to a later
  cycle per the planner's Priority 3 stretch goal).

### Non-vacuity `example` at `explicitEulerGLM`

- Confirms the theorem **elaborates** at concrete `(s, r) = (1, 1)`:
  `D = Matrix.diagonal d`, `G = Matrix.diagonal g`, with
  `Matrix.isSymm_diagonal _` discharging the `D.IsSymm` hypothesis.
  The body is a one-line invocation of the main theorem (no manual
  unfolding required).

## Dead ends

- **Initial `Matrix.dotProduct_*` namespace error**: tried
  `Matrix.dotProduct_add` etc., but those lemmas live at the top
  level (not under the `Matrix` namespace) because `dotProduct`
  itself is defined at the top level. Fixed by stripping the
  `Matrix.` prefix.
- **`Matrix.mulVec_transpose` direction confusion**: the Mathlib
  lemma is `Aᵀ *ᵥ x = x ᵥ* A` (not the reverse). Got it backwards
  initially; corrected via `vecMul_mulVec` for the adjoint helper.
- **`hY`/`hyn` final `rfl`**: the `show ... = (M.A *ᵥ α) i + (M.U *ᵥ y_prev) i`
  step + `rw [h1]` only rewrites the first summand; the residual
  `(M.U *ᵥ y_prev) i = ∑ j, M.U i j * y_prev j` closes by `rfl`
  (definitional unfolding of `Matrix.mulVec`).

## Discovery

- The **textbook's diagonal restriction on `D` is unnecessary** for
  the identity itself — `D` symmetric suffices. The diagonal
  restriction is presumably motivated by the inequality corollary
  `thm:523B` (where PSD plays a role) and/or by physical
  interpretability (`D` as a weight vector for stage values). This
  is a clean strict generalisation worth preserving.
- The **algebraic identity decouples cleanly from `IsGLMSolution`**:
  taking step equations as explicit hypotheses produces a more
  reusable statement than threading the existential. This pattern
  may be useful for other §52x theorems that are purely algebraic
  consequences of the step equations.
- The adjoint helper `(M₁ *ᵥ x) ⬝ᵥ (M₂ *ᵥ y) = x ⬝ᵥ ((M₁ᵀ * M₂) *ᵥ y)`
  closes very cleanly via `dotProduct_mulVec` + `Matrix.vecMul_mulVec`
  + `← dotProduct_mulVec`. This is a generic adjoint pattern for
  quadratic-form manipulations and should be reusable in future
  §52x / §54x theorems.
- The Sum-block quadratic form unfolding via `fromBlocks_mulVec` +
  `sumElim_dotProduct_sumElim` works cleanly without needing a
  custom helper (R1 risk in the strategy was overstated).

## Suggested next approach

1. **Ship `thm:523B` (the inequality form) next cycle** — per the
   planner's Priority 3 stretch goal. With `thm:523A` in place as
   an unconditional identity, `thm:523B` is a one-line `linarith`
   corollary once we have `Matrix.PosSemidef.dotProduct_nonneg`
   (or equivalent). The hook is `M.PosSemidef → 0 ≤ x ⬝ᵥ (M *ᵥ x)`;
   verify via `lean_loogle "Matrix.PosSemidef _ → 0 ≤ _ ⬝ᵥ _"`.
2. **§520F or §521B for breadth** — the §520 cluster has multiple
   open theorems (`thm:521B` "Maximum stability order for given
   steps") that don't require the §302 tree-combinatorics
   prerequisites.
3. **§302 if a 2-cycle commitment is acceptable** — Cycle 240's
   suggestion remains the right one but is multi-cycle work (define
   `α(t)`, `β(t)`, `θ_k` combinatorial primitives, prove (302a)/(302b)
   in cycle X+1, then `thm:302C` Cayley in cycle X+2). Single-cycle
   workers should prefer §520 / §523 follow-ups.
4. **Do NOT touch §441 GPFS-blocked path** — 44 consecutive timeouts
   since cycle 182; loop-maintainer territory.
