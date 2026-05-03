# Cycle 088 Strategy — formalize `def:520E` (A-stable GLM)

## Status snapshot

Cycle 087 successfully formalised `def:520C` (`stabilityFunction`,
`stabilityRegion`, `instabilityRegion`) plus two non-vacuity witnesses
in `OpenMath/Chapter5/Section520.lean`. Build clean, axioms reduced to
`[propext, Classical.choice, Quot.sound]`, score +2. Progress is
58 / 175.

There are **zero open sorry's** in the codebase and **no pending
Aristotle results** to incorporate. The cycle 087 task results
§"Suggested next approach" recommends two parallel paths:

* `thm:520B` — requires designing a non-trivial GLM-iteration encoding
  (no infrastructure for `(500c)` exists yet; multi-cycle commitment).
* `def:520E` (A-stable) — *near-trivial* follow-up to cycle 087's
  `stabilityRegion`.

**Cycle 088 picks `def:520E`.** Rationale: cycles 083–087 all scored
+2 with the "definition + ≤ 2 non-vacuity witnesses" pattern; this
target preserves that momentum and unblocks `def:520F` (L-stable),
the only direct downstream consumer of `def:520E`. `thm:520B` is
deferred to a future cycle that can dedicate the planning effort
needed for the GLM iteration encoding.

## Target

**Entity**: `def:520E` (A-stable general linear method).

**Textbook statement** (quoted verbatim from
`extraction/formalization_data/entities/def_520E.json`):

> A general linear method is 'A-stable' if `M(z)` is power-bounded
> for every `z` in the left half complex plane.

**Page reference**: Butcher 2008, p. 419.

## Encoding plan

### File: `OpenMath/Chapter5/Section520.lean`

Append at the end of the `namespace OpenMath.Chapter5.Section510`
block (the second namespace block in the file, lines 59–210), **before**
the existing `end OpenMath.Chapter5.Section510` on line 210.

### Four new declarations

#### 1. `def GeneralLinearMethod.IsAStable`

```lean
/-- **Definition 520E** — A general linear method is *A-stable* if its
stability matrix `M(z)` is power-bounded for every `z` in the (closed)
left half complex plane.

Butcher (Definition 520E, p. 419): "A general linear method is
'A-stable' if `M(z)` is power-bounded for every `z` in the left half
complex plane."

Encoding choices:

* "Power-bounded" is the existential `PowerBounded` predicate from
  `OpenMath.Chapter1.Section142` reused via membership in the
  `stabilityRegion` set defined in `def:520C`. By unfolding,
  `z ∈ M.stabilityRegion ↔ ∃ C, PowerBounded C (M.stabilityMatrix z)`,
  so this re-spelling is a literal restatement of the textbook.
* "Left half complex plane" is encoded as the closed left half-plane
  `{z : ℂ | z.re ≤ 0}`. The textbook is silent on open vs closed; the
  closed interpretation is the standard convention in stability
  theory and matches `def:350A` (Runge–Kutta A-stability) elsewhere
  in this codebase. -/
def GeneralLinearMethod.IsAStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → z ∈ M.stabilityRegion
```

#### 2. Non-vacuity helper: a trivial all-zero GLM

`explicitEulerGLM` is **not** A-stable (`z = -3` gives
`M(z) = !![1 + (-3)] = !![-2]`, whose powers blow up). We need a
distinct witness. The simplest is the all-zero `(s, r) = (1, 1)` GLM:

```lean
/-- The trivial `(s, r) = (1, 1)` GLM with all four blocks set to the
zero `1×1` matrix. This is not a Runge–Kutta or LMM in the textbook
sense — it is the simplest non-vacuity witness for A-stability:
its stability matrix `M(z) = !![0]` for every `z`, so the trivial
power bound holds uniformly. -/
def trivialZeroGLM : GeneralLinearMethod 1 1 where
  A := !![0]
  U := !![0]
  B := !![0]
  V := !![0]
```

#### 3. The stability matrix of `trivialZeroGLM` is identically `!![0]`

```lean
/-- For the all-zero `(1,1)` GLM, the stability matrix collapses to
the `1×1` zero matrix at every `z ∈ ℂ`. Mirrors the cycle 086
`explicitEulerGLM_stabilityMatrix` proof shape (which also unfolds
the resolvent factor against the `A = !![0]` block first). -/
theorem trivialZeroGLM_stabilityMatrix (z : ℂ) :
    trivialZeroGLM.stabilityMatrix z = !![0] := by
  -- (1 - z • complexify A) = 1 since A = !![0].
  have hA :
      (1 - z • complexify trivialZeroGLM.A)
        = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [trivialZeroGLM, complexify]
  unfold GeneralLinearMethod.stabilityMatrix
  rw [hA, inv_one]
  ext i j
  fin_cases i; fin_cases j
  simp [trivialZeroGLM, complexify, Matrix.mul_apply]
```

#### 4. Non-vacuity: `trivialZeroGLM` is A-stable

```lean
/-- Non-vacuity witness for `IsAStable`: the `trivialZeroGLM` is
A-stable. Since `M(z) = !![0]` for every `z`, the powers
`M(z)^0 = 1`, `M(z)^k = 0` (`k ≥ 1`) are uniformly bounded by
`‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖`. -/
theorem trivialZeroGLM_isAStable : trivialZeroGLM.IsAStable := by
  intro z _hz
  refine ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖, ?_⟩
  intro k
  rw [trivialZeroGLM_stabilityMatrix]
  -- Goal: ‖(!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) ^ k‖
  --        ≤ ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖
  -- Identify the !![0] entry-matrix with the actual zero matrix:
  have h0 : (!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [h0]
  -- Goal: ‖(0 : Matrix (Fin 1) (Fin 1) ℂ) ^ k‖ ≤ ‖(1 : …)‖
  cases k with
  | zero => simp
  | succ n =>
      rw [zero_pow (Nat.succ_ne_zero n), norm_zero]
      exact norm_nonneg _
```

(The exact spelling of `cases k with | zero | succ n` may need
minor tweaking — see "Implementation notes" below.)

## Implementation notes

### Existing infrastructure to reuse (already in the file from cycle 087)

* `OpenMath.Chapter5.Section520.complexify` (line 50) — the lift
  `Matrix m n ℝ → Matrix m n ℂ`. Note: still in the **`Section520`**
  namespace; the `Section510` namespace block in `Section520.lean`
  re-opens it via `open OpenMath.Chapter5.Section520 (complexify)`
  on line 63. **Do not redeclare.**
* `GeneralLinearMethod.stabilityMatrix` (line 92, in `Section510`).
* `GeneralLinearMethod.stabilityRegion` (line 170, in `Section510`).
* The scoped `Matrix.Norms.Operator` open (line 62 of the
  `Section510` namespace block) — already provides the
  `linftyOpSemiNormedRing` instance needed for `PowerBounded` on
  `Matrix (Fin r) (Fin r) ℂ`. **Do not re-open.**
* `OpenMath.Chapter1.Section142.PowerBounded` (already imported
  transitively via `Section510`).

### Namespace placement

All four new declarations (`IsAStable`, `trivialZeroGLM`,
`trivialZeroGLM_stabilityMatrix`, `trivialZeroGLM_isAStable`) go
**inside the existing `namespace OpenMath.Chapter5.Section510` block**
in `Section520.lean`. This matches cycle 086/087 placement and
ensures dot notation `M.IsAStable` works on values of
`GeneralLinearMethod s r`. Add them after
`explicitEulerGLM_zero_mem_stabilityRegion` (line 208) and before
`end OpenMath.Chapter5.Section510` (line 210).

### Likely build issues and quick fixes

1. **`cases k` arm syntax.** If
   `cases k with | zero => … | succ n => …` fails on motive issues,
   fall back to `induction k with | zero => … | succ n _ih => …` or
   to `rcases k with _ | n`. Test with `lean_multi_attempt` inside
   the goal.
2. **`zero_pow` argument shape.** The needed lemma is
   `zero_pow : ∀ {n : ℕ}, n ≠ 0 → (0 : α)^n = 0`. If
   `zero_pow (Nat.succ_ne_zero n)` produces a unification mismatch,
   try `zero_pow n.succ_ne_zero` or `simp [pow_succ]` (since
   `0 * x = 0`).
3. **`(!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0`.** May already
   be `simp`-closable directly via `Matrix.zero_apply` /
   `Matrix.of_isEmpty`. If `ext + fin_cases + simp` is unwieldy,
   try `Matrix.ext` (functional ext) or
   `show !![(0 : ℂ)] = (0 : Matrix _ _ ℂ); decide` is sometimes
   sufficient.

### Faithfulness checklist (must run before commit)

For `def GeneralLinearMethod.IsAStable`:

* **Quoted textbook**: "A general linear method is 'A-stable' if
  `M(z)` is power-bounded for every `z` in the left half complex
  plane." (Butcher 2008, p. 419, `entities/def_520E.json`.)
* **Lean type matches**: `∀ z : ℂ, z.re ≤ 0 → z ∈ M.stabilityRegion`
  literally re-spells the textbook quantifier. The
  `z ∈ M.stabilityRegion` membership unfolds to
  `∃ C, PowerBounded C (M.stabilityMatrix z)`, the literal
  power-boundedness condition from cycle 087's `def:520C`.
* **No definition smuggling**: A-stability is encoded as
  exactly the textbook's quantifier, not as a derived
  characterization (e.g. via `Re(eigenvalues) ≤ 0`).
* **Convention note (closed vs open half-plane)**: documented
  in the docstring; closed is the textbook convention used by
  `def:350A` (Runge–Kutta A-stability) elsewhere in the codebase.

For each new theorem:

* `trivialZeroGLM_stabilityMatrix`: tautology-free (conclusion is
  a concrete matrix equation).
* `trivialZeroGLM_isAStable`: tautology-free (conclusion is
  `M.IsAStable`, providing real witnesses `C` and `k`-uniform bound).
* No hypothesis strengthening: both theorems are hypothesis-free.

## Aristotle plan

Probably not needed. This cycle's deliverable is small and matches
the cycle 087 shape, which closed without Aristotle. **Only if** the
`cases k` proof of `trivialZeroGLM_isAStable` proves stubborn after
~20 minutes of manual tries, batch-submit just the one lemma and
sleep ≤ 30 minutes, then incorporate or fall back to `induction k`.
Do NOT submit `IsAStable` (definition-only) or
`trivialZeroGLM_stabilityMatrix` (cycle 086 has the matching
`explicitEulerGLM_stabilityMatrix` proof template; copy-adapt
directly).

## Tracking updates

After the file compiles cleanly:

1. **`extraction/formalization_data/lean_status.json`** — set
   `def:520E` row to:
   ```json
   {
     "lean_file": "OpenMath/Chapter5/Section520.lean",
     "lean_symbol": "OpenMath.Chapter5.Section510.GeneralLinearMethod.IsAStable",
     "formalization_status": "formalized"
   }
   ```
   (Match the cycle 087 row format for `def:520C`.)
2. **`plan.md`** — flip the `[ ]` next to `def:520E` to `[x]` and
   append `— OpenMath/Chapter5/Section520.lean`. Bump the progress
   counter from 58 / 175 to 59 / 175.

## Build verification (run before commit)

```bash
lake env lean OpenMath/Chapter5/Section520.lean   # single file check
lake build OpenMath.Chapter5.Section520           # populate .olean cache
```

Then verify axioms:

```bash
echo '#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.IsAStable
#print axioms OpenMath.Chapter5.Section510.trivialZeroGLM_stabilityMatrix
#print axioms OpenMath.Chapter5.Section510.trivialZeroGLM_isAStable' \
  | lake env lean --stdin OpenMath/Chapter5/Section520.lean
```

Expected for all three: `[propext, Classical.choice, Quot.sound]`.
**Note** (per cycle 072): run `lake build` *before* `#print axioms`
so the `.olean` cache is fresh; otherwise stale caches can produce
spurious `sorryAx` reports.

## What NOT to do this cycle

* Do **NOT** target `thm:520B` ("for `y' = qy`, the GLM iteration
  yields `y^[n] = M(z) y^[n-1]` with `z = hq`"). It requires a
  fresh design pass for the GLM iteration encoding (no Lean
  infrastructure for Butcher's equation `(500c)` exists yet); this
  is a multi-cycle commitment that should be opened by a planner
  cycle dedicated to the encoding decision.
* Do **NOT** also try `def:520F` (L-stable) in the same cycle.
  L-stability adds a `lim_{|z| → ∞} ‖M(z)‖ = 0` requirement on top
  of A-stability, involving a complex limit and materially more
  work. Save it for a clean follow-up cycle.
* Do **NOT** try to prove `explicitEulerGLM` is *not* A-stable.
  Negation witnesses are harder than positive witnesses and are
  not required for non-vacuity.
* Do **NOT** redeclare `complexify` or re-open
  `Matrix.Norms.Operator`. Both are already in scope inside the
  `Section510` namespace block of `Section520.lean` (lines 62–63).
* Do **NOT** raise `maxHeartbeats`. CLAUDE.md is explicit.
* Do **NOT** introduce `axiom` / `constant`.
* Do **NOT** edit `scripts/autonomous_loop.py` from the worker.
  (Standing rule from cycle 015's
  `tautology_scanner_false_positives.md`.)
* Do **NOT** treat any "stuck" / "commit not landed" / "semantic
  sorry" verdict in the prompt at face value without first running
  the verification commands above. The pattern of
  `attempts.md`-propagated phantom verdicts (cycles 008, 014, 015,
  035, 040, 071) is well-documented; verify HEAD before reacting.

## Definition of done

* `OpenMath/Chapter5/Section520.lean` compiles cleanly
  (`lake env lean` + `lake build`).
* All three new declarations have axiom set
  `[propext, Classical.choice, Quot.sound]`.
* `lean_status.json` and `plan.md` updated.
* Faithfulness checklist filled in `task_results/cycle_088.md`,
  with quoted textbook statement and matching Lean type discussion.
* Commit pushed to `origin/Main/Experiments`.
* Progress: 58 / 175 → **59 / 175**.
