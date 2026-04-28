# Cycle 007 Results

## Worked on
- `thm:123A` ("Further Hamiltonian problems") — Butcher §123, p. 56:
  *the Hamiltonian `H(y(x))` is invariant along solutions of `y' = J ∇H`.*
- Formalized in 2-D as `hamiltonian_invariant`, alongside a new
  `HamiltonianTraj2D` structure and a small Fréchet-derivative helper
  `gradientCLM`, in `OpenMath/Chapter1/Section123.lean`.

## Approach

### Step 1 — entity load
- Read `extraction/formalization_data/entities/thm_123A.json`:
  > `\\begin{theorem}\\n$H(y(x))$ is invariant.\\n\\end{theorem}`
- Re-read `entities/thm_123B.json` for the Hamiltonian-system context
  (`y' = J ∇H`, `J = [[0, -I], [I, 0]]`).
- Re-read existing `OpenMath/Chapter1/Section123.lean` to anchor the
  naming convention from cycle 004's `HamiltonianVar2D` /
  `area_const`.

### Step 2 — Mathlib search round
The strategy outlined two routes for the 2-variable chain rule:
(1) the `HasFDerivAt H : ℝ × ℝ → ℝ` route via
`HasFDerivAt.comp_hasDerivAt`, or (2) keeping the chain rule as a
`d_H : ∀ x, HasDerivAt Hcomp (∇H · y') x` field on the structure.

I scaffolded with route (2) (the simpler, strategy-recommended
shape) since it required no Mathlib search to close the algebraic
step (`ring`). Aristotle was given the chance in Step 4 to upgrade
to route (1) if it proved cleaner — and it did. The final version
of the file uses route (1).

### Step 3 — sorry-first scaffold (initial route-(2) version)

The route-(2) scaffold I committed first (kept here for the cycle
record) used:

```lean
structure HamiltonianTraj2D
    (y₁ y₂ H₁ H₂ Hcomp : ℝ → ℝ) : Prop where
  d_y₁  : ∀ x, HasDerivAt y₁ (-(H₂ x)) x
  d_y₂  : ∀ x, HasDerivAt y₂ (H₁ x) x
  d_H   : ∀ x, HasDerivAt Hcomp
                (H₁ x * (-(H₂ x)) + H₂ x * (H₁ x)) x

theorem hamiltonian_invariant ... : ∀ x, HasDerivAt Hcomp 0 x := by
  intro x; have hx := h.d_H x; convert hx using 1; ring
```

The route-(2) scaffold compiled cleanly with no diagnostics on
first try. *But* the conclusion `HasDerivAt Hcomp 0 x` quantifies
over an opaque `Hcomp : ℝ → ℝ` without a structural link to the
actual Hamiltonian — semantically faithful only if the user reads
the docstring and instantiates `Hcomp x := H (y₁ x, y₂ x)`
themselves. This is faithful but indirect. Step 4 took advantage
of Aristotle to upgrade.

### Step 4 — Aristotle batch

Submitted the file once with project ID
`cf4c6f84-7a2f-4935-aa63-56db1f130beb`, prompt asking for either a
cleaner factoring (using Mathlib chain-rule lemmas) or returning
the file unchanged. Slept 30 minutes, then checked once.

**Outcome**: `COMPLETE_WITH_ERRORS` after ~11 minutes. The
"COMPLETE_WITH_ERRORS" label is a documented false-alarm pattern
in this project (see cycles 005/006); the actual file
`Section123_aristotle/Section123.lean` was clean. Diff vs my
scaffold confirmed:

1. Existing `HamiltonianVar2D`, `area`, `area_const` and their
   docstrings all preserved verbatim. ✓
2. Top-of-file `/-! ... -/` block preserved verbatim. ✓
3. Aristotle introduced a `noncomputable def gradientCLM (a b : ℝ) :
   (ℝ × ℝ) →L[ℝ] ℝ` packaging `(v₁, v₂) ↦ a·v₁ + b·v₂` as a
   continuous linear map.
4. `HamiltonianTraj2D` was restructured to take `H : ℝ × ℝ → ℝ`
   directly (not an opaque `Hcomp`) and the `d_H` chain-rule field
   was replaced by
   `hH : ∀ x, HasFDerivAt H (gradientCLM (H₁ x) (H₂ x)) (y₁ x, y₂ x)`
   — i.e. "the Fréchet derivative of `H` at the trajectory point
   has the named partials" — a *standard* Mathlib hypothesis, not
   a manually-spelled chain rule.
5. The conclusion of `hamiltonian_invariant` became
   `HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x` — *literally* the
   textbook statement "$H(y(x))$ is invariant", not an opaque
   `Hcomp` symbol.
6. The proof now (a) builds the pair derivative
   `HasDerivAt (fun t => (y₁ t, y₂ t)) (-(H₂ x), H₁ x) x` from
   `d_y₁`, `d_y₂` via `HasFDerivAtFilter.prodMk`, (b) composes
   with `hH` via `HasFDerivAt.comp_hasDerivAt`, then (c) closes
   the algebraic `gradientCLM (H₁ x) (H₂ x) (-(H₂ x), H₁ x) = 0`
   step with `simp [gradientCLM, ...]; ring`.

### Step 5 — adopting Aristotle's version

I evaluated the new factoring against the strategy's faithfulness
criteria:

- Does the structure still encode the Hamiltonian ODE `y' = J ∇H`?
  YES — `d_y₁`, `d_y₂` are unchanged (component form of the ODE);
  `hH` is the standard "H is differentiable at the trajectory
  point with named gradient" hypothesis.
- Does the theorem's conclusion still say "H ∘ y has zero
  derivative"? YES — and now it says it more directly:
  `HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x` — the actual
  composition is in the conclusion, not hidden behind an opaque
  symbol.
- Is anything load-bearing now hidden in a hypothesis it shouldn't
  be? NO — the chain rule is a *Mathlib lemma*, applied inside the
  proof, not pre-baked as a structure field.

All three checks favor the Aristotle version. Adopted by
`cp /tmp/aristotle_cf4c6f84/Section123_aristotle/Section123.lean
OpenMath/Chapter1/Section123.lean`.

### Step 6 — verification

1. `lake env lean OpenMath/Chapter1/Section123.lean` → exit 0,
   empty stdout (no warnings, no errors, no `sorry`).
2. `lake build OpenMath` →
   `Build completed successfully (2790 jobs).`
3. `lean_diagnostic_messages` (LSP) → `items: []`,
   `failed_dependencies: []`.

## Result

SUCCESS — `thm:123A` formalized in 2-D as
`OpenMath.Chapter1.Section123.hamiltonian_invariant`. The shipped
version is the Aristotle-suggested chain-rule-via-Mathlib
factoring, which is strictly more textbook-faithful than the
scaffold (the conclusion is now the literal
`HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x` rather than an opaque
`Hcomp`). Zero `sorry`, both single-file and full-project builds
green.

## Faithfulness check

### `gradientCLM` (new helper def)

- Type: `(a b : ℝ) → (ℝ × ℝ) →L[ℝ] ℝ`.
- Definition: `a • ContinuousLinearMap.fst ℝ ℝ ℝ +
                b • ContinuousLinearMap.snd ℝ ℝ ℝ`,
  i.e. `(v₁, v₂) ↦ a·v₁ + b·v₂`.
- This is *not* a named Butcher concept; it's a small reusable
  helper for "the Fréchet derivative of a scalar function on
  ℝ × ℝ with partials `(a, b)`". No Mathlib `def` was found that
  packages this exact thing without going through more abstract
  `EuclideanSpace`/`PiLp` machinery, so a one-liner local helper
  is appropriate.
- The natural Mathlib equivalence
  `gradientCLM a b = (a, b).inner_right` (or similar) could be
  proved on demand; not needed for `thm:123A`.

### `HamiltonianTraj2D` (new structure)

Field labels:
- `d_y₁` : **hypothesis** (the user models `H` and `y` and supplies
  `y₁'(x) = -∂₂H(y(x))`, which is the first component of `y' = J∇H`).
- `d_y₂` : **hypothesis** (similarly `y₂'(x) = ∂₁H(y(x))`).
- `hH`   : **hypothesis** ("`H` is Fréchet-differentiable along the
  trajectory with gradient `(H₁, H₂)`"). This is the standard
  smoothness hypothesis on `H`, not a disguised version of the
  conclusion. The chain rule that turns `hH` + `d_y₁` + `d_y₂` into
  `d/dx H(y(x))` is *Mathlib's* `HasFDerivAt.comp_hasDerivAt`,
  applied in the proof — not a structure field.

Definition-smuggling check: `HamiltonianTraj2D` encodes the ODE
`y' = J ∇H` plus the hypothesis that `H` is differentiable at
trajectory points. None of its fields state
`HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x` — so the conclusion of
`thm:123A` is NOT smuggled into the hypothesis. ✓

### `hamiltonian_invariant` (new theorem)

- Entity ID `thm:123A`, textbook statement (quoted from
  `formalization_data/entities/thm_123A.json` field
  `statement_latex`):
  > `\\begin{theorem}\\n$H(y(x))$ is invariant.\\n\\end{theorem}`
- Lean statement captures: **same content (in 2-D)**. The
  conclusion is `HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x` for
  every `x`, i.e. `d/dx H(y(x)) = 0` everywhere — the textbook's
  "invariant". (On a connected 1-D domain, zero derivative ↔
  locally constant ↔ globally constant.) The 2-D restriction
  matches cycle-004's `area_const` precedent; a `2N`-D
  generalization is deferred per the strategy's "do NOT generalize
  this cycle" rule.
- Tautology check: conclusion is
  `HasDerivAt (fun t => H (y₁ t, y₂ t)) 0 x`. None of the
  structure fields say this; `hH` says the *Fréchet* derivative
  of `H` at the *trajectory point* is `gradientCLM (H₁ x) (H₂ x)`,
  which is mathematically a different statement (it's about `H`
  alone, not about `H ∘ (y₁, y₂)`). The proof does real work to
  close the gap. ✓
- Identity check: proof has 7 lines including `convert`,
  `HasFDerivAtFilter.prodMk`, `comp_hasDerivAt`, `simp`, `ring`.
  Real algebraic and structural work. ✓
- Hypothesis-strength check: only `HasDerivAt y₁ ...`,
  `HasDerivAt y₂ ...` (i.e. real differentiability of the two
  trajectory components), plus `HasFDerivAt H ...` *only at the
  trajectory points* (not globally). No `C^∞`, no continuity beyond
  what differentiability already implies. ✓
- Absent-theorem check: no comments promise theorems that don't
  exist in the file. ✓

## Dead ends

None. The sorry-first scaffold (route (2)) closed on first try
with `convert ... ring`. Aristotle's route-(1) refactor was
adopted because it improved faithfulness, not because the
scaffold failed.

## Discovery

- **Aristotle is genuinely useful as a code-review pass even when
  the file already compiles.** I submitted with no `sorry`s and a
  prompt that explicitly accepted "return unchanged" as a valid
  outcome; Aristotle still produced a meaningful refactor that
  improved faithfulness (conclusion went from opaque `Hcomp` to
  literal `H (y₁ t, y₂ t)`). The "Aristotle-first (MANDATORY)"
  rule earns its keep here.
- Mathlib's `HasFDerivAt.comp_hasDerivAt` and
  `HasFDerivAtFilter.prodMk` are the canonical pair for "scalar
  function of a vector-valued curve" chain rules. Worth
  remembering for future Hamiltonian / variational work.
- The 2-D restriction is an honest faithfulness gap relative to
  the `2N`-D textbook statement. Future cycles that need to
  formalize `2N`-D Hamiltonian systems (e.g. for §370 symplectic
  integrators) will need to either generalize `HamiltonianTraj2D`
  to `Fin (2N)` indexing or reach for a Mathlib
  `Matrix.symplecticForm` API.
- `lake env lean <file>` produces no output (and exits 0) when a
  file is clean — that's the success signal. Cross-check via
  `lean_diagnostic_messages` from the LSP.

## Suggested next approach

- Per the planner's "Suggested follow-up for cycle 008": pivot to
  **`thm:110C`** (existence/uniqueness of solutions, §110) — the
  Banach fixed-point bridge `lem:110B` is already done in cycle
  003, so `thm:110C` is the next high-value Chapter-1 unlock.
  Doing `thm:110C` opens up `thm:111A`, `thm:112B`, and the rest
  of Chapter 1.
- Avoid `thm:142E` until a Schur upper-triangular decomposition
  lands (3–5 cycle infrastructure project — tracked in
  `.prover-state/issues/jordan_canonical_form_missing.md`).
- A `2N`-D generalization of `hamiltonian_invariant` is *not* a
  good cycle-008 target on its own; defer until a downstream
  consumer (Ch.3 §370 symplectic integrators) actually needs it.
