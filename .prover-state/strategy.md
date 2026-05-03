# Cycle 089 — Formalize `def:520F` (L-stable general linear method)

## Status going in

- Cycle 088 closed `def:520E` (A-stable GLM) plus the `trivialZeroGLM`
  non-vacuity witness. `OpenMath/Chapter5/Section520.lean` builds clean.
- No pending Aristotle results, no sorry's, no infrastructure
  blockers reported by previous workers in scope.
- The cycle 088 worker explicitly recommended `def:520F` as next.
  Its only direct dependency is `def:520E`, which is now in place.

## Priority 0 — incorporate Aristotle

**None pending.** Skip.

## Priority 1 — formalize `def:520F` (L-stable GLM)

### Textbook statement (verbatim from `entities/def_520F.json`)

> A general linear method is L-stable if it is A-stable and
> ρ(M(∞)) = 0.

Here ρ denotes spectral radius and `M(∞)` is the formal value of the
rational function `M(z) = V + zB(I − zA)⁻¹U` "at infinity". In the
standard interpretation (Hairer–Wanner, Butcher), the condition
`ρ(M(∞)) = 0` is equivalent to "the spectral radius of `M(z)` tends
to 0 as `z → ∞` in `ℂ`". This is the formulation we encode, because
it sidesteps the `A`-invertibility issue that arises when trying to
define `M(∞)` as a single matrix.

### Encoding choice — use `Filter.Tendsto`, not an elementary form

Use Mathlib's `spectralRadius` (lives in
`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:53`) returning
`ℝ≥0∞`, and Mathlib's `Filter.cocompact ℂ` (the standard "going to
infinity" filter on a finite-dim normed space). This is more
idiomatic than a `∀ ε > 0, ∃ R, …` form and Mathlib has the lemmas
we need (`spectralRadius_zero`, `tendsto_const_nhds`).

### Exact Lean signature

Add the new definition and witness inside the existing
`namespace OpenMath.Chapter5.Section510` block of
`OpenMath/Chapter5/Section520.lean` (the same block that holds
`IsAStable` and `trivialZeroGLM_isAStable` — see lines 59–279 of
the current file). Place the new declarations **after**
`trivialZeroGLM_isAStable` (line 277) and **before** the closing
`end OpenMath.Chapter5.Section510` (line 279).

Imports to add at the top of the file (only if not already present):

```lean
import Mathlib.Analysis.Normed.Algebra.Spectrum
```

The `spectralRadius` and `Filter.cocompact` symbols should both
become accessible from this import plus the existing
`Mathlib.Data.Complex.Basic` import. Add other imports only if Lean
errors demand it; keep the diff minimal.

Definition:

```lean
/-- **Definition 520F** — A general linear method is *L-stable* if it
is A-stable and the spectral radius of its stability matrix `M(z)`
tends to `0` as `z → ∞` in `ℂ`.

Butcher (Definition 520F, p. 419): "A general linear method is
L-stable if it is A-stable and ρ(M(∞)) = 0."

Encoding choice: the condition `ρ(M(∞)) = 0` is interpreted as
`Filter.Tendsto (fun z => spectralRadius ℂ (M(z))) (Filter.cocompact ℂ)
(𝓝 0)`. This sidesteps the issue that `M(∞)` as a literal matrix
value is only well-defined when the `A`-block is invertible (in
which case `M(∞) = V − B·A⁻¹·U`); the spectral-radius limit
formulation captures the same mathematical content without needing
a case split on invertibility, and is the formulation universally
used in the modern stiff-ODE literature (cf. Hairer–Wanner). -/
def GeneralLinearMethod.IsLStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  M.IsAStable ∧
  Filter.Tendsto
    (fun z : ℂ => spectralRadius ℂ (M.stabilityMatrix z))
    (Filter.cocompact ℂ)
    (𝓝 0)
```

Non-vacuity witness:

```lean
/-- Non-vacuity witness for `IsLStable`: the `trivialZeroGLM` is
L-stable. Since `M(z) = !![0]` for every `z` (cycle 088
`trivialZeroGLM_stabilityMatrix`), the spectral radius is
identically `0`, and `Tendsto` of a constant sequence to its
constant value is automatic. -/
theorem trivialZeroGLM_isLStable : trivialZeroGLM.IsLStable := by
  refine ⟨trivialZeroGLM_isAStable, ?_⟩
  -- Reduce the spectral-radius function to the constant 0.
  have hfun :
      (fun z : ℂ => spectralRadius ℂ (trivialZeroGLM.stabilityMatrix z))
        = fun _ => (0 : ℝ≥0∞) := by
    funext z
    rw [trivialZeroGLM_stabilityMatrix]
    -- Show `!![(0 : ℂ)] = 0` then use `spectralRadius_zero`.
    have h0 : (!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [h0]
    exact spectralRadius_zero
  rw [hfun]
  exact tendsto_const_nhds
```

### Likely build issues and quick fixes

The strategy above should compile as written, but here are the
most likely snags and their canonical fixes:

1. **`spectralRadius_zero` name mismatch.** If Lean reports the name
   does not exist, search via
   `lean_local_search "spectralRadius_zero"` — the lemma exists in
   `Mathlib/Analysis/Normed/Algebra/Spectrum.lean:81`. The signature
   is `theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0`
   with `A` instance-inferred from context. May need to spell out
   `(spectralRadius_zero (𝕜 := ℂ) (A := Matrix (Fin 1) (Fin 1) ℂ))`
   if instance inference stalls.

2. **`spectralRadius` instance resolution.** `spectralRadius`
   requires `[NormedField 𝕜] [Ring A] [Algebra 𝕜 A]`. For
   `A = Matrix (Fin r) (Fin r) ℂ` and `𝕜 = ℂ`, all three are
   inferred from Mathlib's standard matrix-algebra instances
   (which `Mathlib.Analysis.Matrix.Normed`, transitively imported,
   provides). If instance synthesis stalls, the worker should
   `lean_hover_info` on `spectralRadius` to confirm what's missing
   and add the targeted import — but try the minimal import first.

3. **`Filter.cocompact` namespace.** The full name is
   `Filter.cocompact`. Use it explicitly. The `(𝓝 0)` notation
   requires `open scoped Topology` (commonly already in scope). If
   not, add `open scoped Topology` near the top of the namespace
   block.

4. **`(𝓝 (0 : ℝ≥0∞))` vs `(𝓝 0)`.** The `0` in `(𝓝 0)` may
   require explicit type annotation `(𝓝 (0 : ℝ≥0∞))` if Lean
   cannot infer it. Apply only if the first form fails.

5. **`!![(0 : ℂ)] = 0` rewrite.** Already done in cycle 088 at
   `trivialZeroGLM_isAStable` (lines 270–271). Same `ext + fin_cases
   + simp` works.

6. **`tendsto_const_nhds`.** Universally available; no extra
   import needed.

If any one of these fails, do **not** rewrite the encoding; instead
search Mathlib for the working name. The encoding is faithful and
should not be changed.

### Faithfulness check (mandatory pre-commit)

Per CLAUDE.md, before committing:

* **Definition smuggling check (`IsLStable`):** the Lean predicate
  encodes "A-stable AND spectral radius of `M(z)` tends to 0 as
  `z → ∞`". The textbook statement is "A-stable AND ρ(M(∞)) = 0".
  These are mathematically equivalent under the standard
  interpretation of `M(∞)` as the limit at infinity (cf. the
  encoding-choice paragraph in the docstring). Document this
  divergence explicitly in the docstring and in the cycle 089
  task results. NOT smuggling — `M(∞)` is not part of Lean
  syntax, so the limit formulation is the literal Lean expression
  of the textbook condition.

* **Non-vacuity check:** `trivialZeroGLM_isLStable` is a real
  witness; `trivialZeroGLM` exists, A-stability is proved
  (cycle 088), and the limit half is closed by reducing to a
  constant function and `tendsto_const_nhds`.

* **No new hypotheses, no extra typeclass requirements** beyond
  what `def:520E` (`IsAStable`) already requires plus the
  `spectralRadius` instances inferred from `Matrix … ℂ`.

* **No `class`/`structure` introductions, no `axiom`/`constant`,
  no heartbeat bumps.**

## Priority 2 — housekeeping

After the build is clean and axioms check out:

1. **`extraction/formalization_data/lean_status.json`**:
   bump `def:520F` from `unformalized` to `formalized`. The pattern
   is the same as cycle 088 used for `def:520E`. The existing entry
   for `def:520F` (search for `"def:520F"` in the file) will have
   `lean_file: null`, `lean_symbol: null`, `formalization_status:
   "unformalized"` — set them to
   `"OpenMath/Chapter5/Section520.lean"`,
   `"OpenMath.Chapter5.Section510.GeneralLinearMethod.IsLStable"`,
   `"formalized"` respectively.

2. **`plan.md`**: change the `def:520F` row in Chapter 5 from `[ ]`
   to `[x]` and add the trailing pointer
   `OpenMath/Chapter5/Section520.lean`. Update the
   "**Progress: 59 / 175**" header to **60 / 175**.

## Priority 3 — task results

Write `.prover-state/task_results/cycle_089.md` per CLAUDE.md
template. The faithfulness section must explicitly call out the
`M(∞)` ↔ `Filter.Tendsto … (𝓝 0)` interpretation (this is the
only non-trivial encoding choice this cycle).

## What NOT to try

1. **Do NOT define `M(∞)` as a separate matrix value.** That would
   require a case split on `A`-invertibility (the formula
   `M(∞) = V − B·A⁻¹·U` only applies when `A` is invertible) and
   would force a different — and arguably less faithful — encoding
   for the `A`-singular case. The `Tendsto`-spectralRadius form is
   the literature-standard encoding and is what we use.

2. **Do NOT introduce a `Matrix.spectralRadius` wrapper.** Use
   Mathlib's `spectralRadius ℂ (M : Matrix _ _ ℂ)` directly. The
   instance synthesis should just work.

3. **Do NOT use `Filter.atTop.comap norm` or similar bespoke
   filter constructions.** `Filter.cocompact ℂ` is the canonical
   "going to infinity" filter on a finite-dim normed space.

4. **Do NOT use `explicitEulerGLM` as the L-stability witness.**
   Explicit Euler is **not** A-stable (e.g. at `z = -3`, `M(z) =
   !![-2]` whose powers diverge), hence not L-stable. The
   `trivialZeroGLM` is the only non-vacuity witness in scope.

5. **Do NOT introduce an elementary `∀ ε > 0, ∃ R, ...` form**
   alongside the Tendsto form. Keep the encoding minimal — one
   formulation, the Tendsto one, with a docstring explaining the
   choice.

6. **Do NOT bump `maxHeartbeats`.** None of the proofs above need
   it; if `simp` or `ext + fin_cases + simp` runs slow, decompose
   manually rather than raising the limit (CLAUDE.md rule).

7. **Do NOT submit anything to Aristotle this cycle.** All proof
   obligations are short and have known shapes; manual
   verification is faster than a 30-minute Aristotle round-trip.

## Acceptance criteria

* `lake env lean OpenMath/Chapter5/Section520.lean` exits clean.
* `lake build OpenMath.Chapter5.Section520` succeeds.
* `#print axioms trivialZeroGLM_isLStable` returns
  `[propext, Classical.choice, Quot.sound]`.
* `lean_status.json` and `plan.md` updated as in Priority 2.
* `cycle_089.md` task results present.
* Single commit, single push, branch `Main/Experiments`.
