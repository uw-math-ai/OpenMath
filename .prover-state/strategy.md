# Cycle 087 Strategy — formalize `def:520C` (stability function + stability region + instability region)

## Pre-flight

* No Aristotle results pending. No sorry's in committed code. No open
  blockers on Chapter 5.
* Cycle 086 closed `def:520A` (`GeneralLinearMethod.stabilityMatrix`)
  in `OpenMath/Chapter5/Section520.lean`. Build is clean; axioms are
  `[propext, Classical.choice, Quot.sound]` only.
* Progress: 57 / 175 entities done.

## What to work on this cycle

**Target: `def:520C`** — the stability function `Φ(w, z) = det(wI − M(z))`,
the stability region (subset of ℂ where `sup_n ‖M(z)^n‖ < ∞`), and the
instability region (its complement).

Why this target:

* Cycle 086's task results explicitly nominate it as the next step.
* It is the immediate successor in §520's topo order: it depends only
  on `def:520A` (just landed) plus pre-existing infrastructure
  (`Matrix.det`, `PowerBounded` from `OpenMath/Chapter1/Section142.lean`).
* It unblocks `thm:520B` (next likely target — restates that
  `y^[n] = M(z) y^[n-1]` for the linear test problem), `def:520E`
  (A-stable), `def:521A` (maximal stability order), and `thm:520D`
  (instability region boundary).

## Faithfulness reading of `def:520C`

Read `extraction/formalization_data/entities/def_520C.json`. The
textbook entity bundles **three** related concepts in one record:

1. **Stability function** Φ(w, z) := det(wI − M(z)). The textbook
   notes: "Φ(w, z) may be a rational function" because `M(z)` involves
   `(I − zA)⁻¹`; "we equally refer to the numerator of this rational
   function as the stability function".
2. **Stability region** := { z ∈ ℂ : sup_{n ≥ 1} ‖M(z)^n‖ < ∞ }.
3. **Instability region** := complement of (2) in ℂ.

Encode all three as separate `def`s in this cycle. Do **not** try to
also encode "the numerator of Φ" — that requires a polynomial-vs-rational
distinction we have not built and is not used by any immediate
downstream consumer (`def:520E`, `def:521A`, `thm:520D` only need (1)
as `det(wI − M(z))` and (2) as the power-boundedness predicate).
Document this scoping explicitly in the file docstring, citing
`def:520C`'s "we equally refer to the numerator" remark — a notational
convenience, not a separate Lean definition.

### Concrete encoding

In `OpenMath/Chapter5/Section520.lean`, append to the existing
`namespace OpenMath.Chapter5.Section510` block (so dot notation
`M.stabilityFunction`, `M.stabilityRegion`, `M.instabilityRegion`
works on values of type `GeneralLinearMethod s r`):

```lean
/-- **Definition 520C** — The *stability function* of a general
linear method, `Φ(w, z) = det(wI − M(z))`.

Butcher §520, p. 419: "the 'stability function' for the method is the
polynomial Φ(w, z) given by Φ(w, z) = det(wI − M(z))".

Encoding note: in general `M(z)` involves `(I − zA)⁻¹`, so Φ is
naturally a rational function in `z`. The textbook remark "we equally
refer to the numerator of this rational function as the stability
function" is a notational convenience, not a separate definition; we
encode the literal `det(wI − M(z))` form, which is the canonical
representative on the invertibility domain. -/
noncomputable def GeneralLinearMethod.stabilityFunction
    {s r : ℕ} (M : GeneralLinearMethod s r) (w z : ℂ) : ℂ :=
  (w • (1 : Matrix (Fin r) (Fin r) ℂ) - M.stabilityMatrix z).det

/-- **Definition 520C** (continued) — The *stability region* of a
general linear method is the set of `z ∈ ℂ` for which the powers
of `M(z)` are uniformly bounded.

Butcher §520, p. 419: "the 'stability region' is the subset of the
complex plane such that if z is in this subset, then
`sup_{n=1..∞} ‖M(z)^n‖ < ∞`".

We use the existential `PowerBounded` predicate from
`OpenMath.Chapter1.Section142` (a uniform `∀ k, ‖a^k‖ ≤ C` bound,
which is equivalent to `sup_n ‖a^n‖ < ∞`). The matrix norm is the
default Mathlib `Matrix.linftyOpNormedRing` made available by
`Mathlib.Analysis.Matrix.Normed`; per the §142 docstring, the
predicate is norm-equivalence-invariant on finite-dimensional spaces
so the choice of matrix norm does not matter for membership. -/
noncomputable def GeneralLinearMethod.stabilityRegion
    {s r : ℕ} (M : GeneralLinearMethod s r) : Set ℂ :=
  { z : ℂ | ∃ C : ℝ,
      OpenMath.Chapter1.Section142.PowerBounded C (M.stabilityMatrix z) }

/-- **Definition 520C** (continued) — The *instability region* is
the complement of the stability region in `ℂ`. -/
noncomputable def GeneralLinearMethod.instabilityRegion
    {s r : ℕ} (M : GeneralLinearMethod s r) : Set ℂ :=
  (M.stabilityRegion)ᶜ
```

Two non-vacuity witnesses (mandatory per CLAUDE.md):

```lean
/-- Non-vacuity: at `z = 0`, the explicit-Euler stability function
collapses to `w − 1` (since `M(0) = V = !![1]` for explicit Euler). -/
theorem explicitEulerGLM_stabilityFunction_at_zero (w : ℂ) :
    explicitEulerGLM.stabilityFunction w 0 = w - 1 := by
  unfold GeneralLinearMethod.stabilityFunction
  rw [explicitEulerGLM_stabilityMatrix]
  -- Goal: det(w • 1 - !![1 + 0]) = w - 1
  -- Reduce to a 1×1 determinant.
  rw [Matrix.det_fin_one]
  simp

/-- Non-vacuity: `0` lies in the stability region of explicit Euler.
At `z = 0`, `M(0) = !![1]`, so every power equals `!![1]` and the
sequence is bounded by `‖!![1]‖`. -/
theorem explicitEulerGLM_zero_mem_stabilityRegion :
    (0 : ℂ) ∈ explicitEulerGLM.stabilityRegion := by
  refine ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖, ?_⟩
  intro k
  rw [explicitEulerGLM_stabilityMatrix]
  -- !![1 + 0] = (1 : Matrix (Fin 1) (Fin 1) ℂ); then 1 ^ k = 1.
  have hM : !![(1 : ℂ) + 0] = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp [Matrix.one_fin_one]
  rw [hM, one_pow]
```

If the second witness is fiddly (the `!![1+0] = 1` reduction may need
a different rewrite path), try `lean_multi_attempt` with snippets:
- `simp [Matrix.one_fin_one, show (1:ℂ) + 0 = 1 from by ring]`
- `simp [Matrix.one_fin_one]; ring_nf`
- `ext i j; fin_cases i; fin_cases j; simp; ring`

Persist with rewrites; do not change the witness statement.

## Imports / namespace housekeeping

* Section520.lean already imports
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` (transitively, via
  Section510). If `Matrix.det_fin_one` is not visible, add
  `import Mathlib.LinearAlgebra.Matrix.Determinant.Basic` directly.
* Section520.lean already imports `OpenMath.Chapter5.Section510`,
  which itself imports `OpenMath.Chapter1.Section142`. So
  `PowerBounded` is reachable via the fully-qualified
  `OpenMath.Chapter1.Section142.PowerBounded`. If you prefer the
  unqualified name, `open OpenMath.Chapter1.Section142 (PowerBounded)`
  inside the Section510 namespace block is the cleanest fix.
* Keep the existing pattern: `complexify` lives in
  `namespace OpenMath.Chapter5.Section520`; the `GeneralLinearMethod.*`
  declarations live in `namespace OpenMath.Chapter5.Section510` so dot
  notation works. **Do not** put the new definitions in the
  `Section520` namespace — that re-introduces the cycle 086 namespace
  bug (recorded in cycle 086 task results §"Dead ends").

## Aristotle plan

* Submit to Aristotle **only the second non-vacuity witness**
  (`explicitEulerGLM_zero_mem_stabilityRegion`) as a fallback if your
  first manual attempt fails. The three `def`s and the first witness
  (`explicitEulerGLM_stabilityFunction_at_zero`) should close in one
  cycle without Aristotle compute.
* If you batch-submit, follow CLAUDE.md: ~5 sub-lemmas, 30-min sleep,
  one check. Do not poll repeatedly. For this 5-deliverable cycle,
  Aristotle is likely unnecessary.

## What NOT to try

* **Do not** redefine `complexify` or change `stabilityMatrix`'s
  encoding. Cycle 086's choices are committed and stable.
* **Do not** try to express the stability function as a
  `Polynomial ℂ` (univariate in `w`) or a bivariate polynomial in
  `(w, z)`. Mathlib's `Polynomial`/`MvPolynomial` API requires
  encoding the determinant as a formal polynomial, which is real
  polynomial-algebra work and is out of scope. The textbook treats Φ
  as a function `ℂ × ℂ → ℂ` everywhere it is used in §520; encode it
  that way. The "polynomial in w" remark is descriptive (the
  determinant of `wI − M(z)` is the characteristic polynomial of
  `M(z)` evaluated at `w`, hence polynomial in `w` for fixed `z`),
  not a Lean encoding requirement.
* **Do not** define a "numerator of Φ" predicate. Out of scope; not
  needed by any immediate downstream consumer; document the omission
  in the file docstring and move on.
* **Do not** put any of the new `def`s in the `Section520` namespace.
  Cycle 086 already hit this footgun; recurring in cycle 087 wastes
  a full edit-compile cycle. Use `namespace OpenMath.Chapter5.Section510`
  for everything that takes a `GeneralLinearMethod` value.
* **Do not** raise `maxHeartbeats`. The proofs above are short.
* **Do not** introduce `axiom` or `constant`.
* **Do not** treat any "stuck on" / "commits not reaching repo" /
  "semantic sorry" framing in a future prompt as a real blocker
  without verifying against `HEAD` first. The pattern is documented
  as a recurring stale-`attempts.md` phantom in
  `consultant_advice_cycle_009.md`, `..._014.md`, `..._015.md`,
  `..._040.md`, and `tautology_scanner_false_positives.md`.
  Verification recipe: `git log -1 --format='%H %s'` and
  `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$' OpenMath/`.

## Pre-commit faithfulness checklist

For each new `def` (`stabilityFunction`, `stabilityRegion`,
`instabilityRegion`):

* Open `entities/def_520C.json` and quote the textbook fragment in the
  Lean docstring.
* Confirm the Lean type matches:
  - `stabilityFunction : ℂ → ℂ → ℂ` (textbook: Φ(w, z) ∈ ℂ).
  - `stabilityRegion : Set ℂ` (textbook: subset of the complex plane).
  - `instabilityRegion : Set ℂ` (textbook: complement of the
    stability region).
* Definition smuggling check: each definition matches the textbook
  formula literally.
  - `Φ(w, z) = det(wI − M(z))` ✓
  - "sup_n ‖M(z)^n‖ < ∞" encoded as
    "∃ C, PowerBounded C (M.stabilityMatrix z)" — these are
    **equivalent on a `SeminormedRing`** (existence of a uniform
    upper bound iff finite supremum); flag in the docstring that
    the existential form is the §142-canonical spelling we share
    with `def:510C`. This is **not** definition smuggling — it is
    a literal re-spelling of the supremum-finiteness condition.
  - Complement: literal.
* Hypothesis-strength check: all three are hypothesis-free.

For each new theorem (`explicitEulerGLM_stabilityFunction_at_zero`,
`explicitEulerGLM_zero_mem_stabilityRegion`):

* Tautology check: conclusions are concrete equalities / membership
  facts, not hypothesis re-exports. ✓
* Identity check: proofs do real reduction (compute a determinant /
  reduce a matrix power), not `exact h`-style stubs. ✓

## Housekeeping at end of cycle

1. Update `extraction/formalization_data/lean_status.json` —
   mark `def:520C` as `formalized` with
   `lean_file = "OpenMath/Chapter5/Section520.lean"` and
   `lean_symbol = "OpenMath.Chapter5.Section510.GeneralLinearMethod.stabilityFunction"`
   (the lead symbol; the region defs are siblings in the same file).
2. Update `plan.md` — mark `def:520C` `[x]` with file pointer; bump
   "Progress: 57 / 175" → "58 / 175".
3. Write `.prover-state/task_results/cycle_087.md` per CLAUDE.md
   format (Worked on / Approach / Result / Faithfulness check / Dead
   ends / Discovery / Suggested next approach).
4. Verify with `lake env lean OpenMath/Chapter5/Section520.lean`
   (single-file check is preferred per CLAUDE.md). Then
   `#print axioms` on each of the five new declarations to confirm
   `[propext, Classical.choice, Quot.sound]` only. Use
   `lake build OpenMath.Chapter5.Section520` first to refresh the
   `.olean` cache before `#print axioms`, per the cycle 072
   stale-cache discovery.
5. Commit with message
   `Cycle 087 — formalize def:520C (stability function + region + instability region)`
   and push.

## Suggested next-cycle target (cycle 088)

`thm:520B` — "for a linear differential equation, `y^[n] = M(z) y^[n-1]`
holds with `z = hq`". This is the natural §520 follow-up; the proof is
a one-step algebraic identity reducing `(500c)` (the GLM iteration on
`Y, y^[n]`) under `f(y) = qy` to the closed form. Depends on
`def:520A` (✓), `def:520C` (this cycle), and a Lean encoding of "the
GLM iteration" `(500c)` — that encoding does not yet exist and will
be the cycle 088 planner's main infrastructure decision. Out of scope
for cycle 087.
