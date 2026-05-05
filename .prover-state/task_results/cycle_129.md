# Cycle 129 Results

## Worked on
Strengthening cycle 128's `def:525A` deliverable by adding a
substantively non-trivial G-symplectic witness via the
implicit-midpoint method as a `(s, r) = (1, 1)` general linear
method.

New deliverables:

* `def implicitMidpointGLM` (in
  `OpenMath/Chapter5/Section510.lean`) — the canonical implicit
  midpoint method written as a 1×1 GLM with
  `A = !![1/2]`, `U = B = V = !![1]`.
* `theorem implicitMidpointGLM_isPreconsistent` —
  preconsistency witness `u = (fun _ => 1)`.
* `theorem implicitMidpointGLM_isGSymplectic` (in
  `OpenMath/Chapter5/Section525.lean`) — substantively
  non-trivial G-symplectic witness with
  `G = D = (1 : Matrix (Fin 1) (Fin 1) ℝ)`.

## Approach
Followed the planner's seven-step strategy:

1. Re-read `entities/def_525A.json`, `Section510.lean`, and
   `Section525.lean` to confirm structures and conventions.
2. Searched Mathlib for PSD/IsDiag lemmas on the identity
   matrix. Found `Matrix.PosSemidef.one` (in
   `Mathlib.LinearAlgebra.Matrix.PosDef`, requires
   `StarOrderedRing`) and `Matrix.isDiag_one` (in
   `Mathlib.LinearAlgebra.Matrix.IsDiag`).
3. Added `implicitMidpointGLM` to `Section510.lean`. Initial
   compile failed with "depends on `Real.instDivInvMonoid`
   which has no executable code" — fixed by marking
   `noncomputable`. (The `1/2` literal in the `A` block forces
   noncomputability; this matches Mathlib's expectation for
   any GLM definition with non-rational entries down the line,
   so it is a clean precedent.)
4. Added `implicitMidpointGLM_isPreconsistent` as a direct
   adaptation of `explicitEulerGLM_isPreconsistent` since the
   `U` and `V` blocks coincide.
5. Added `implicitMidpointGLM_isGSymplectic` to
   `Section525.lean` using `(G, D) = (1, 1)`. Initial compile
   failed: `Matrix.PosSemidef.one` requires `StarOrderedRing
   ℝ`, which is not provided by `LinearAlgebra.Matrix.PosDef`
   alone. Fixed by adding `import Mathlib.Data.Real.StarOrdered`
   (the canonical Mathlib home of the `StarOrderedRing ℝ`
   instance, per its module docstring).
6. Three matrix equations (525a)–(525c) discharged uniformly
   by `ext i j; fin_cases i; fin_cases j; simp
   [implicitMidpointGLM, Matrix.mul_apply (...), ...]; norm_num`
   — `simp` unfolds the 1×1 sums and `!![...]` literals, and
   `norm_num` handles the `1/2 + 1/2 = 1` arithmetic in (525c).
7. Trimmed unused `simp` lemmas after linter feedback.
8. Verified axiom-cleanness on all three new declarations:
   only `[propext, Classical.choice, Quot.sound]`.

## Result
SUCCESS — all three new declarations compile axiom-clean.
Verification:

```
$ lake env lean OpenMath/Chapter5/Section510.lean   # clean
$ lake env lean OpenMath/Chapter5/Section525.lean   # clean
$ lake build OpenMath.Chapter5.Section525           # 2786 jobs OK
$ #print axioms implicitMidpointGLM_isPreconsistent
   → [propext, Classical.choice, Quot.sound]
$ #print axioms implicitMidpointGLM_isGSymplectic
   → [propext, Classical.choice, Quot.sound]
```

The new G-symplectic witness *genuinely separates*
`implicitMidpointGLM` from `explicitEulerGLM`: the latter
(with `A = !![0]`) cannot satisfy (525c) under
`G = D = 1`, since `0 + 0 ≠ 1`. So `IsGSymplectic` is
demonstrably non-vacuous in a discriminating sense — not
merely inhabited by the trivial `G = D = 0` witness.

## Faithfulness check

For `def implicitMidpointGLM`:

- Entity ID: this is a *named GLM* (not a textbook entity in
  the formalization extraction). Implicit midpoint as a
  Runge–Kutta method appears in Butcher §234 (the textbook's
  primary discussion of the method). The transcription to GLM
  form via `r = 1` embedding is standard — see
  `Section510.lean` `explicitEulerGLM` for the parallel
  precedent already in the project.
- Lean entries: `A = !![1/2]`, `U = B = V = !![1]`. This is
  the standard GLM transcription of `c = 1/2, A = 1/2, b = 1`
  (the midpoint Runge–Kutta tableau).
- Definition smuggling check: `implicitMidpointGLM` IS the
  textbook tableau, not a characterization. We are not
  defining it via "G-symplectic with `G = 1`" — that's the
  *theorem*, not the definition. ✓

For `theorem implicitMidpointGLM_isPreconsistent`:

- Tautology check: the conclusion `IsPreconsistent` is
  existential over `u`; not a hypothesis. ✓
- Identity check: the proof is a `refine ⟨fun _ => 1, ...⟩`
  followed by two `funext / fin_cases / simp` blocks. Real
  computation, not a re-export. ✓
- Hypothesis strength: parameter-free. ✓

For `theorem implicitMidpointGLM_isGSymplectic`:

- Tautology check: the conclusion `IsGSymplectic` is
  existential over `(G, D)`; not a hypothesis. ✓
- Identity check: the proof produces a non-trivial witness
  `(G, D) = (1, 1)` and verifies the three matrix equations
  by direct `ext / fin_cases / simp` computation. Real
  algebraic content. ✓
- Hypothesis strength: parameter-free. ✓
- Discriminating-content check: as noted in the docstring,
  this witness genuinely fails for `explicitEulerGLM` (since
  (525c) would require `0 = 1`). So the theorem captures
  substantive G-symplectic structure, not vacuous
  inhabitation. ✓

## Dead ends

- Initial attempt with `G = !![1]` rather than the identity
  `1` would have required proving PSD and IsDiag for
  `!![1]` from scratch (no direct Mathlib lemma matches the
  `!![...]` literal). Switching to `G = 1` lets us use
  `Matrix.PosSemidef.one` and `Matrix.isDiag_one` directly,
  saving ~20 lines of bespoke proof.
- The `noncomputable` annotation was needed because `1/2 : ℝ`
  is not computable. This is a one-token fix and matches how
  any future GLM with real-number entries (like the (525d)
  example) will need to be declared.
- Adding `Mathlib.Data.Real.StarOrdered` to the imports of
  `Section525.lean` was necessary; without it,
  `Matrix.PosSemidef.one` fails synthesis on `StarOrderedRing
  ℝ`. This import is lightweight and standard.

## Discovery

- **`Matrix.PosSemidef.one` lives behind `StarOrderedRing`**
  — `Mathlib.LinearAlgebra.Matrix.PosDef` does not transitively
  pull in the `StarOrderedRing ℝ` instance. Future cycles
  using `Matrix.PosSemidef.one` over `ℝ` should add
  `import Mathlib.Data.Real.StarOrdered`.
- **`!![...]` notation forces `noncomputable` for `ℝ` entries
  with division** — even a constant like `1/2` triggers the
  IR check failure. Mark such `def`s `noncomputable`.
- **The 1×1 `simp` recipe**
  `ext i j; fin_cases i; fin_cases j; simp
  [<glm-name>, Matrix.mul_apply, ...]` cleanly handles all
  three (525a)–(525c) equations once `(G, D) = (1, 1)` is
  chosen. Total proof body for the G-symplectic witness was
  ~12 lines.

## Suggested next approach

- **Cycle 130 candidate**: Butcher (525d) substantive 2×2
  G-symplectic witness with `√3` arithmetic. The cycle 129
  deliverable already provides a non-trivial discriminating
  witness, so cycle 130's Butcher (525d) work is *additional
  polish* rather than load-bearing. The arithmetic is heavier
  (entries like `(3+√3)/6`, `-√3/3`, `(3+√3)/3`, etc.) but no
  longer time-critical.
- **Bonus opportunity**: add
  `implicitMidpointGLM_isStable` and
  `implicitMidpointGLM_isConsistent` mirroring the
  `explicitEulerGLM` analogues. Both should be one-line proofs
  given the identical `V` block. (Deferred from cycle 129
  because the stretch goal was lower-priority than the core
  G-symplectic witness; cycle 130 could pick these up
  alongside the 2×2 work.)
- **§550 doubly-companion-matrix infrastructure** —
  `thm:550A`, `thm:550B`, `cor:550C` cluster, multi-cycle.
- **Chapter 3 leaf cleanup** — long tail of unformalized §3
  entities (`thm:302C`, `thm:302A`, `thm:302B`, `def:381F`,
  etc.). These are independent of §5 work.
