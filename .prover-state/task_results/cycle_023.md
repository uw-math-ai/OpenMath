# Cycle 023 Results

## Worked on
`thm:343A` — *the reflection of the reflection of a Runge–Kutta method
is the original method* (Butcher §343, page 220–221).

This required:

1. Defining `RKTableau.reflection` (the textbook construction is given
   only as a tableau diagram; this cycle introduces the Lean term).
2. Stating and proving Theorem 343A as an involution claim:
   `M.reflection.reflection = M`.
3. Providing a non-trivial concrete witness — the implicit midpoint
   method (a 1-stage symmetric method).

New Lean entities added in `OpenMath/Chapter3/Section343.lean`:

* `RKTableau.reflection` (def)
* `RKTableau.reflection_A_apply`, `reflection_b_apply`,
  `reflection_c_apply` (rfl-lemmas, API)
* `RKTableau.reflection_reflection` (Theorem 343A — closes the cycle)
* `RKTableau.implicitMidpoint` (def — concrete witness)
* Two `example` lemmas demonstrating both witnesses.

## Approach
1. Loaded `extraction/formalization_data/entities/thm_343A.json` and
   re-read Butcher §343 (`extraction/raw_text/ch03.txt`, lines
   4970–5037) to confirm the tableau formulas verbatim.
2. Defined `reflection` component-wise:
   * `âᵢⱼ = bⱼ - aᵢⱼ`,
   * `b̂ⱼ = bⱼ`,
   * `ĉᵢ = (Σⱼ bⱼ) - cᵢ`.
   No silent simplification of `Σⱼ bⱼ → 1` (consistency is *not*
   assumed in def:343).
3. Proved `reflection_reflection` by destructuring `M`, then using
   `RKTableau.mk.injEq.mpr ⟨_, _, _⟩` to split into three field
   equalities. Each is closed by `funext` plus `ring` (or `rfl` for
   the trivial `b` field).
4. Added `RKTableau.implicitMidpoint` (with `noncomputable` because
   `1/2 : ℝ` uses real-number division). Proved its symmetry using
   the same `mk.injEq` pattern with `norm_num`/`simp` for the rational
   arithmetic.
5. Registered the new file in `OpenMath/Chapter3.lean` (chapter
   aggregator).
6. Verified `lake env lean OpenMath/Chapter3/Section343.lean` and
   `lake build` both succeed cleanly.
7. Updated `extraction/formalization_data/lean_status.json` and
   `plan.md` (flipped the row, bumped progress 23 → 24).

Aristotle was *not* used this cycle — per the strategy, the proof is so
short (one structure-extensionality plus three `ring` calls) that
submitting to Aristotle would be unnecessary overhead. Aristotle quota
is preserved for future non-trivial cycles (e.g. `thm:381G`'s
partition-algebra arguments or §314's elementary-differential
independence).

## Result
**SUCCESS.** `thm:343A` is fully formalized with no `sorry`, no `axiom`,
no raised `maxHeartbeats`, and a passing `lake build`. The
`reflection_reflection` theorem closes by component-wise `ring` after
field destructuring.

## Faithfulness check

### `def RKTableau.reflection` (new definition of a named concept)

* **Entity**: textbook concept "reflection" / "adjoint method" of a
  Runge–Kutta tableau. Derived in Butcher §343, page 220, last display
  (`extraction/raw_text/ch03.txt` lines 5021–5033). The textbook
  reflection tableau:
  ```
  (Σⱼ bⱼ) - cᵢ │ b₁-aᵢ₁  b₂-aᵢ₂  …  bₛ-aᵢₛ
                ─────────────────────────
                  b₁  b₂  …  bₛ
  ```
* **Lean statement captures**: same content. Verbatim component
  formulas: `A i j := M.b j - M.A i j`, `b j := M.b j`, `c i :=
  (∑ j, M.b j) - M.c i`.
* **Definition-smuggling check**: PASS. We define the reflection
  exactly as Butcher's tableau formula. No characterization
  theorem is being smuggled in via the definition.
* **Faithfulness flag note**: `ĉᵢ = (Σⱼ bⱼ) - cᵢ`, NOT `1 - cᵢ`. Under
  the consistency condition `Σⱼ bⱼ = 1` they agree, but def:343 does
  not assume consistency. We did **not** silently substitute.

### `theorem RKTableau.reflection_reflection`

* **Entity**: textbook Theorem 343A:
  > The reflection of the reflection of a Runge–Kutta method is the
  > original method.
* **Lean statement captures**: same content.
  `M.reflection.reflection = M` is the literal involution claim.
* **Tautology check**: PASS. The conclusion `M.reflection.reflection
  = M` does not appear among the (zero) hypotheses.
* **Identity check**: PASS. The proof is `obtain ⟨A, b, c⟩ := M; refine
  RKTableau.mk.injEq..mpr ⟨?_, ?_, ?_⟩; ⟨ring; rfl; ring⟩` —
  substantive `ring` calls on `b j - (b j - A i j) = A i j` and
  `(∑ j, b j) - ((∑ j, b j) - c i) = c i`. Not `exact h` or `:= id`.
* **Hypothesis-strength check**: PASS. Only `M : RKTableau s` is
  required; matches Butcher's hypothesis "given a Runge–Kutta method".
* **Absent-theorem check**: PASS. No comments promise unwritten
  auxiliary results.

### `def RKTableau.implicitMidpoint` (concrete witness)

* **Entity**: textbook implicit midpoint rule. Butcher §371 page 240
  (`extraction/raw_text/ch03.txt` lines around 8320). Tableau:
  `A = (1/2)`, `b = (1)`, `c = (1/2)`.
* **Lean statement captures**: same content.
* **Note**: cycle 023 does *not* prove `implicitMidpoint` is
  symplectic (def:370A is out of scope for this cycle and has an open
  faithfulness question — see the strategy doc). The witness exists
  only to demonstrate that `reflection` has non-trivial fixed points.
  We *do* prove `implicitMidpoint.reflection = implicitMidpoint`, which
  is a weaker but useful fact (the method is symmetric).

### Sanity sweeps (CLAUDE.md pre-commit checklist)

* `rg '\bsorry\b' OpenMath/` → no matches.
* `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/` →
  no matches.
* `lake env lean OpenMath/Chapter3/Section343.lean` → exits cleanly,
  no warnings.
* `lake build` → completes successfully (2826 jobs).

## Dead ends

* First attempt used `cases M with | mk A b c => show … = ⟨A, b, c⟩;
  refine ⟨?_, ?_, ?_⟩`. Lean rejected the `refine ⟨?_, ?_, ?_⟩` with
  "Constructor `Eq.refl` does not have explicit fields, but 3 were
  provided" — the anonymous-constructor `⟨…⟩` shorthand on an equality
  goal is interpreted as `Eq.refl` (reflexivity), not as a triple of
  field equalities.

  **Fix**: invoke `RKTableau.mk.injEq.mpr ⟨?_, ?_, ?_⟩` explicitly.
  The `mk.injEq` simp lemma rewrites a structure-equality `mk x y z =
  mk a b c` into a triple `x = a ∧ y = b ∧ z = c`, and `.mpr` accepts
  the conjunction in right-associated form `⟨_, _, _⟩`.

  **Discovery for future cycles**: when proving structure equalities
  on user-defined `RKTableau`, prefer `RKTableau.mk.injEq` over
  anonymous-constructor splitting. (Mathlib structures with `@[ext]`
  get an `ext` lemma that does the same thing more cleanly, but
  `RKTableau` is not currently `@[ext]`.)

* `simp` alone did not close the `(∑ _j : Fin 1, (1 : ℝ)) - 1/2 = 1/2`
  goal in the implicit-midpoint symmetry proof — it left
  `1 - 2⁻¹ = 2⁻¹`. Adding `norm_num` after `simp` closed it. (Either
  `simp [Fin.sum_univ_one]` plus `norm_num`, or just `simp; norm_num`,
  works.)

* The first version of `implicitMidpoint` was not marked
  `noncomputable`, which Lean rejected because `1/2 : ℝ` uses
  `Real.instDivInvMonoid`. Marked it noncomputable explicitly
  (consistent with how `RKTableau.derivativeWeight` and others in
  Section312 are also noncomputable).

## Discovery

1. **Structure-equality idiom for `RKTableau`**: the cleanest pattern
   for proving `M = N : RKTableau s` is

   ```lean
   refine RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
   · -- A field
   · -- b field
   · -- c field
   ```

   This avoids `cases` (which can produce hard-to-control field names)
   and avoids `congr` (which sometimes does not split structure
   equalities into field-level goals). If `RKTableau` is later given
   `@[ext]`, the same approach simplifies to `ext` plus three field
   subgoals.

2. **Faithful encoding of `(Σⱼ bⱼ) - cᵢ`**: the `c` field of the
   reflection involves a sum over the *original* tableau's `b`. The
   textbook formula `Σⱼ bⱼ` reduces to `1` under consistency, but we
   do not assume consistency, and consequently the involution proof
   has to use `ring` rather than `rfl` for the `c` component. Worth
   noting if/when `consistent` (`Σⱼ bⱼ = 1`) is later introduced as a
   class — additional API lemmas like `reflection_c_apply_consistent`
   may then be useful.

3. **`Matrix (Fin s) (Fin s) ℝ` extensionality**: behaves like a plain
   function `Fin s → Fin s → ℝ` for `funext` purposes; no `Matrix.ext`
   call is needed.

4. **`mk.injEq` is auto-generated for `structure`** — no `@[ext]` or
   manual lemma needed.

## Suggested next approach

The strategy doc lays out three plausible cycle-024 directions, in
rough priority order:

1. **`thm:381G`-Φ scoping** — start the partition-algebra
   infrastructure (`Ã = A`, characteristic functions span ℝ^s, closure
   under matrix-`A` multiplication via tree induction). This is
   genuine multi-cycle work; cycle 024 should *scope* it (an issue
   file with explicit sorry-decomposition) rather than start
   formalizing immediately. The Y-stages clause additionally needs
   §314 (`thm:314A`) which is `unformalized`.

2. **`def:370A` (symplectic methods)** — once the symplectic-matrix
   transpose ambiguity is resolved. Butcher's literal formula
   `M = diag(b)A + A·diag(b) - bbᵀ` gives `m_{ij} = (b_i + b_j)
   a_{ij} - b_i b_j`, but the standard symplectic condition (Hairer–
   Wanner Vol II) is `m_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j`.
   These agree only when `s = 1`. Worth fetching a second source
   before starting — possibly Hairer–Wanner directly, or asking the
   consultant subagent.

3. **§300 combinatorial entities** — e.g. `thm:302C`'s `An = (n-1)!,
   Bn = n^{n-1}` count formulas. Self-contained but requires defining
   `α(t)` and `β(t)` as labelling counts — substantial combinatorics
   work but no §314 dependency.

A useful next stretch on §343 itself would be `thm:343B` (which
asserts that `B(η)`, `C(η)`, `D(η)`, `E(η,ζ)` simplifying assumptions
are preserved/transformed under reflection). That requires the §321
simplifying-assumption framework — *not* available yet — and is a
multi-cycle effort. Defer until §321 is started.

Of the three, my own ranking is **(1) > (2) > (3)** — `thm:381G`
unblocks the most §380 follow-up content, and the partition-algebra
work is reusable for §314. But the `def:370A` transpose-resolution
work could be a useful 1-cycle scoping issue if the consultant
subagent is queryable.
