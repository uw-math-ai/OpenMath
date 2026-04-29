# Cycle 038 Results

## Worked on
- `def:402A` (convergent linear multistep method, Butcher Definition 402A,
  p. 340) — formalized as `LinearMultistepMethod.IsConvergent`.
- Helper recurrence predicate `LinearMultistepMethod.IsLMMSolution`
  (Butcher §404 recurrence; reused predicate-style for explicit and
  implicit methods).
- Sanity helper `isLMMSolution_zero_iff` (LMM with `f ≡ 0` ↔ solves
  the homogeneous recurrence (403a)).
- Sanity helper `const_sequence_isHomogeneousSolution` (constant
  sequences solve (403a) under preconsistency).
- Deferral issue for the concrete `IsConvergent` witness
  (`thm:422C`-shaped proof; gated on Picard–Lindelöf strengthening
  and discrete Grönwall infrastructure).

## Approach
Per the planner's strategy: extend the existing
`OpenMath/Chapter4/Section404.lean` (the §40 introductory file) with a
`## §402 — Convergence` section appended after the §403 content.

1. Read `extraction/formalization_data/entities/def_402A.json` to
   pin down the textbook statement, then quoted it in the
   `IsConvergent` docstring.
2. Wrote the `IsLMMSolution` predicate first — captures the §404
   recurrence with `Fin (k+1)` indexing and natural-number
   subtraction `n + k - i.val` (always non-negative for `i ≤ k`).
3. Wrote `IsConvergent` with all six universal quantifiers (f, L,
   IVP data, starting method, x, iterates) ahead of the textbook
   `Tendsto (Y_m - yex x)` conclusion. Used `LipschitzInSecond` from
   `OpenMath.Chapter1.Section110` (matching its signature
   `(Set ℝ) (ℝ≥0) (ℝ → E → F)`; we instantiate `E = F = ℝ` and pass
   `Set.univ`).
4. Hand-traced the `k = 1` Euler case to confirm the recurrence
   shape is consistent with the existing cycle-036
   `explicitEulerLMM` definition (sign convention noted in cycle 036
   is preserved unchanged).
5. Sorry-first: skeleton compiled cleanly after adding
   `import OpenMath.Chapter1.Section110` and `open scoped NNReal
   Topology`. Two early compile failures were diagnosed and fixed
   (`LipschitzInSecond` unknown without the import; `ℝ≥0` failed to
   parse without `open scoped NNReal`).
6. Helper proofs:
   - `isLMMSolution_zero_iff`: unfold both predicates, peel off
     `Fin.sum_univ_succ`, simplify with `Fin.val_zero`,
     `Nat.sub_zero`, `M.α_zero`, `Fin.val_succ`, close both
     directions with `linarith`.
   - `const_sequence_isHomogeneousSolution`: factor the constant `c`
     out of the sum via `Finset.sum_mul`, rewrite by `← hM`
     (preconsistency) and `one_mul`.
7. Aristotle batch was prepared mentally but not submitted: the
   manual proofs typecheck on the first compile attempt after
   import fixes, so the planner's "if your manual proof finishes
   first, keep it" rule applied.
8. Wrote `lmm_convergence_witness_deferred.md` documenting why the
   concrete `_ : IsConvergent` witness is deferred (`thm:422C` shape,
   needs Grönwall + Picard–Lindelöf strengthening + starting-method
   error tracking).

## Result
SUCCESS — `lake env lean OpenMath/Chapter4/Section404.lean` exits
clean (exit code 0, no diagnostics). Both helper theorems closed
without `sorry`.

## Faithfulness check

### `LinearMultistepMethod.IsLMMSolution` (helper, not a textbook concept on its own)
- Captures the §404 recurrence
  `Σ_{i=0}^{k} α_i · y_{n-i} = h · Σ_{i=0}^{k} β_i · f(x_{n-i}, y_{n-i})`
  via the index shift `n ↦ n + k`. Sums over `Fin (k+1)`, so the
  leading `α 0` and `β 0` terms are included.
- Tautology check: not applicable (predicate, not theorem).
- Hypothesis-strength check: not applicable.
- The signs are consistent with cycle-036's `explicitEulerLMM` and
  the existing `IsHomogeneousSolution` (the strategy explicitly
  flagged the cycle-036 sign convention; we did not modify it).

### `LinearMultistepMethod.IsConvergent` (Definition 402A)
- Entity ID: `def:402A`. Textbook statement (quoted from
  `entities/def_402A.json`):
  > "Consider a linear multistep method used with a starting method
  > as described in the previous discussion. Let `Y_m` denote the
  > approximation to `y(x)` found using `m` steps with
  > `h = (x − x_0)/m`. The function `f` is assumed to be continuous
  > and to satisfy a Lipschitz condition in its second variable. The
  > linear multistep method is said to be 'convergent' if, for any
  > such initial value problem, `Y_m − y(x) → 0`, as `m → ∞`."
- Lean statement captures: same content. The textbook universal
  quantifier "for any such initial value problem" is unrolled into
  explicit binders for `f`, `L`, `(x₀, y₀, yex)`, `start`, `x`,
  and `Y`. The conclusion is the textbook `Tendsto`-form limit.
- Definition-smuggling check: ✓ defined directly via the
  `Tendsto` limit, **not** as "stable + consistent" (that
  equivalence is `thm:406D`, an honest theorem to be proved later).
- Hypothesis-strength check: continuity is `Continuous (Function.uncurry f)`
  (joint continuity in `(x, y)`), matching the textbook's
  context-dependent reading of "f continuous"; Lipschitz uses
  `OpenMath.Chapter1.Section110.LipschitzInSecond Set.univ L f`,
  matching the textbook hypothesis verbatim. We do NOT add
  hypotheses beyond what the textbook states (no boundedness, no
  smoothness).
- Tautology check: ✓ no hypothesis equals the conclusion.

### `isLMMSolution_zero_iff` (helper, not a separate textbook concept)
- Lean statement: `IsLMMSolution h x₀ (fun _ _ => 0) Y ↔
  IsHomogeneousSolution Y`.
- Captures: the textbook-implicit fact that the homogeneous
  recurrence (403a) is exactly the LMM recurrence (404 / §404
  defining equation) at `f ≡ 0`. This is folklore.
- Identity check: ✓ proof closes via `intro/unfold/constructor/
  simp/rw/linarith` — does NOT close with `:= h`, `:= id`, or
  `exact h_<name>`.
- Hypothesis-strength check: only `M`, `h`, `x₀`, `Y` (no extras).

### `const_sequence_isHomogeneousSolution` (helper, not a separate textbook concept)
- Lean statement: under `M.IsPreconsistent`, the constant sequence
  `fun _ => c` solves the homogeneous recurrence.
- Captures: a known consequence of preconsistency (the LMM preserves
  constants iff `Σ α_i = 1`, the (404a) condition).
- Identity check: ✓ proof closes via `intro/have/rw` — not via
  `exact h`.
- Hypothesis-strength check: the only hypothesis besides `M` and `c`
  is `M.IsPreconsistent`, which is necessary (a method with
  `Σ α_i ≠ 1` does not preserve constants). Cannot be weakened.

## Dead ends
- First compile attempt failed because `Section404.lean` imported
  only `Mathlib`, not the sibling `OpenMath.Chapter1.Section110`.
  Lean reported `Unknown identifier
  OpenMath.Chapter1.Section110.LipschitzInSecond` and a downstream
  `LE Type` cascade on the `ℝ≥0` parser. Fixed by adding the import.
- Second attempt: the import resolved `LipschitzInSecond` but
  `ℝ≥0` still tripped a `LE Type` synthesize failure. Cause:
  `ℝ≥0` is a *scoped* notation (in `NNReal`); fixed by adding
  `open scoped NNReal Topology` at the top of the file.

## Discovery
- The `Section404.lean` file did not previously import any sibling
  OpenMath module; cycle 038 added the first cross-chapter
  dependency (`OpenMath.Chapter1.Section110`). This is fine — both
  files compile under `import Mathlib`. The added line will let
  future Chapter-4 / §40 content reuse all of §110's Lipschitz
  machinery without redefining.
- The `ℝ≥0` notation is `open scoped NNReal`. We now have this
  scope opened in the §40 file as well; future cycles adding
  Chapter-4 content here can reuse the notation without further
  setup. Note `Topology` was added speculatively for `nhds`; it was
  not strictly required for the predicate (Mathlib auto-resolves
  `nhds` without it for Real numbers) but is harmless and matches
  Section110.lean's convention.
- The strategy's explicit "if your manual proof finishes first,
  keep it; if Aristotle returns a cleaner proof, use Aristotle's"
  rule applied: Aristotle was not invoked this cycle because the
  manual proofs typechecked on the first attempt after import fixes.

## Suggested next approach
Per the planner's preview (strategy §10), **cycle 039 should pick up
`thm:243A`** — the cross-chapter Ch.2→Ch.4 deferral. All three
dependencies (`def:402A`, `def:403A`, `def:404B`) are now formalized,
and `thm:243A` is the oldest deferral on the books. Closing it (a)
removes legacy debt before more §40 material is stacked, and (b)
serves as a forcing function: if `thm:243A` cannot be stated
cleanly using the new predicates, that is a faithfulness signal
worth catching now.

If the planner judges `thm:243A` to need yet more infrastructure
(it likely needs the Euler one-step convergence `thm:213A/B`
formalized as a usable consumer first), fall back to **`def:406A`
(local truncation error)** — but verify whether its transitive
dependencies on §301A / §306A / §311B are *content-required* or
merely *contextual* before committing.
