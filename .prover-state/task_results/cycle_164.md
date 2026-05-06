# Cycle 164 Results

## Worked on

`def:530B`/`def:530C` Path A r-parametric refactor **Phase B.3
(reconciliation lemmas)**, per the cycle-164 strategy's Priority 1.

Concretely, eight reconciliation theorems landed in Section520 and
Section530 exhibiting the cycle 162 Phase A parametric families
(`paddedREulerGLM (r : ℕ)`, `padCompatStartingMethodR (r : ℕ)`) as
the common generalisation of the pre-existing cycle
131/133/137/156/159/161 hand-written instances:

GLM-side (`OpenMath/Chapter5/Section520.lean`, immediately after
the `paddedREulerGLM` definition):

- `paddedREulerGLM_zero_eq_explicitEulerGLM`
- `paddedREulerGLM_one_eq_padded2DEulerGLM`
- `paddedREulerGLM_two_eq_padded3DEulerGLM`
- `paddedREulerGLM_three_eq_padded4DEulerGLM`

Starting-method-side (`OpenMath/Chapter5/Section530.lean`,
immediately after `padCompatStartingMethodR_constituents_isExplicit`):

- `padCompatStartingMethodR_zero_eq_trivialStartingMethod`
- `padCompatStartingMethodR_one_eq_padCompatStartingMethod`
- `padCompatStartingMethodR_two_eq_pad3CompatStartingMethod`
- `padCompatStartingMethodR_three_eq_pad4CompatStartingMethod`

## Approach

For each lemma:

1. Reduce the structure equality via `mk.injEq` to a conjunction of
   per-field equalities.
2. The `s = 1`-block field (`A` for GLMs, `stages` for starting
   methods) is `rfl` on both sides.
3. The remaining fields (`U`, `B`, `V` matrices for GLMs; `method`
   dependent function for starting methods) are reduced via `ext`
   followed by `fin_cases` on the row/column or constituent index,
   then `simp` to discharge the indicator-vs-`!![…]` (resp.
   `if i.val = 0`-vs-pattern-match) reduction at concrete indices.

GLM-side closure (works uniformly across r ∈ {0, 1, 2, 3}):
```
refine GeneralLinearMethod.mk.injEq .. |>.mpr ?_
refine ⟨rfl, ?_, ?_, ?_⟩
all_goals
  ext i j
  fin_cases i <;> fin_cases j <;> simp
```
(For r = 0 the `<;>` is unnecessary since `Fin 1` has only one
element, so the r = 0 lemma uses `; ;` instead to silence the linter.)

Starting-method-side closure (handles the dependent type with HEq):
```
refine StartingMethod.mk.injEq .. |>.mpr ?_
refine ⟨rfl, heq_of_eq ?_⟩
funext i
fin_cases i
· show padCompatMethodR _ ⟨0, _⟩ = ... ⟨0, _⟩
  unfold padCompatMethodR ...
  simp
· ...
```

The `heq_of_eq` bridge is needed because `StartingMethod`'s
`method` field has type depending on `stages`; `mk.injEq` gives
`HEq` for that field rather than `Eq`. Since `stages = fun _ => 1`
agrees on both sides by `rfl`, the underlying types match, and
`heq_of_eq` can promote the per-index `Eq` proof.

## Result

**SUCCESS.** All eight reconciliation theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`), verified individually
via `mcp__lean-lsp__lean_verify`. No errors, no sorries; the only
warnings were stylistic (unused simp args, unnecessary `<;>` for
single-goal cases) and were cleaned up. Sorry count remained 0 → 0.

The full Section520 and Section530 files compile clean; downstream
files unaffected (no signature changes in any pre-existing
declaration, only new theorem additions).

## Faithfulness check

All eight new declarations are `theorem`s, not `def`s or
`structure`s. None introduces a new mathematical concept.

For each:
- **Tautology check**: the conclusion `paddedREulerGLM r = X` (or
  `padCompatStartingMethodR r = X`) does NOT appear as any
  hypothesis (the lemmas have no hypotheses other than the
  implicitly-bound ambient `r`, which is fixed by the LHS).
- **Identity check**: each proof is genuine matrix-equality reasoning
  (`mk.injEq` + `ext` + `fin_cases` + `simp` / `unfold ...; simp`),
  not `exact h_*`.
- **Hypothesis strength check**: the eight lemmas have no
  hypotheses; the equalities are unconditional. Nothing to weaken.

These reconciliations do not introduce a new textbook-named
concept; they exhibit definitional equivalence between two
encodings of the *same* concept (the padded explicit-Euler GLM
family, resp. the row-0-active starting method family) at concrete
small-r values. The textbook (Butcher §520 / §530) does not
distinguish "parametric" vs "hand-written" encodings; both are the
same mathematical object. The reconciliations therefore have no
direct entity counterpart to quote — they are bridge lemmas
internal to the Lean development, supporting a future cycle 165
retirement of the hand-written instances in favor of the
parametric family.

## Dead ends

1. **Initial closure attempt with redundant `simp` arguments.**
   The first GLM-side draft used
   `simp [paddedREulerGLM, padded2DEulerGLM, Matrix.of_apply]` per
   field. The simp linter flagged all three arguments as unused —
   `mk.injEq` already unfolds the `Matrix.of fun ... => if ...`
   bodies, and `!![…]` matches via the standard `Matrix.cons_val_*`
   simp lemmas already loaded. Cleaned up to bare `simp`.

2. **`decide` on matrix equalities.** Tried as a quick first attempt
   per the strategy's recipe; failed because `Matrix.of_apply`
   reductions get stuck on `Classical.choice` for `Real.decidableEq`.
   Expected for ℝ-valued matrices; pivoted to `simp`.

3. **Funext on the starting-method `method` field without `heq_of_eq`.**
   The first Section530 draft used
   `refine ⟨rfl, ?_⟩; funext i; ...` directly. `funext` failed
   because `mk.injEq` produced an `HEq` (not `Eq`) for the dependent
   `method` field. Inserting `heq_of_eq` before the funext bridges
   the two — the underlying types match (both `Fin 1 →
   GeneralizedRungeKuttaMethod 1` after `stages = rfl`), so the HEq
   reduces to Eq.

## Discovery

1. **Dependent-structure `mk.injEq` produces HEq for fields whose
   type depends on earlier fields.** For
   `StartingMethod (r := 1)`,
   `mk.injEq` gives
   `mk s₁ m₁ = mk s₂ m₂ ↔ s₁ = s₂ ∧ HEq m₁ m₂`. When the dependent
   types resolve (here both `stages = fun _ => 1`), bridging via
   `heq_of_eq` is the right move. This pattern will recur whenever
   we equate dependent structures (e.g., future
   `IRKStable`/`HasOrderRelativeTo_explicit` wrappers that take
   `StartingMethod r` as an existential witness).

2. **Per-r-arity uniformity of the GLM closure.** The same closure
   tactic block (`ext + fin_cases <;> fin_cases <;> simp`) works
   verbatim for r ∈ {1, 2, 3} (the r = 0 case needs `;` instead of
   `<;>` to placate the linter). This validates the strategy's
   prediction that the four GLM reconciliations would close
   uniformly without per-r tuning.

3. **Heterogeneity between GLM and starting-method closures.** The
   GLM matrices' concrete bodies (`Matrix.of fun ... => if ...` vs
   `!![…]`) reduce to the same indicator function under `simp`
   without explicit unfolding hints. The starting-method
   constituent functions (`padCompatMethodR` vs the pattern-match
   definitions `padCompatMethod`/`pad3CompatMethod`/
   `pad4CompatMethod`) require explicit `unfold` of both sides plus
   `simp` to reduce the `if i.val = 0`-vs-pattern-match decision.
   This is a structural difference: `Matrix.of` is opaque enough
   that simp picks up `Matrix.of_apply` automatically, but
   per-constructor pattern-matching definitions need the `unfold`
   hint.

## Suggested next approach

**Cycle 165: Retirement of the hand-written
`padded{2,3,4}DEulerGLM` / `pad{2,3,4}CompatStartingMethod`
instances and their cycle 156/157/159/161 witnesses, using the
Phase B.3 reconciliations landed this cycle as the bridges.**

The reconciliations enable a clean retirement path:

1. Replace each downstream use of `padded2DEulerGLM` with
   `paddedREulerGLM 1` (rewriting via the reconciliation).
2. Replace each downstream use of `padded3DEulerGLM` with
   `paddedREulerGLM 2`.
3. Replace each downstream use of `padded4DEulerGLM` with
   `paddedREulerGLM 3`.
4. Same for `padCompatStartingMethod` → `padCompatStartingMethodR 1`,
   etc.
5. Once no remaining use of the hand-written instances, delete:
   - `padded{2,3,4}DEulerGLM` definitions and their structure-lemma
     witnesses
   - `pad{Compat,3Compat,4Compat}Method` constituent functions
   - `pad{Compat,3Compat,4Compat}StartingMethod` definitions and
     their `_isNonDegenerate` / `_constituents_isExplicit` /
     `_applyExplicit` lemmas
   - the cycle 156/157/159/161 `HasOrderRelativeTo_explicit` and
     `HasOrder_explicit` witnesses (subsumed by cycle 163's
     parametric versions instantiated at `r ∈ {1, 2, 3}`)
   - the cycle-164 reconciliations themselves (since their LHS and
     RHS will both be defined in terms of the parametric family
     after retirement, making them redundant).

Estimated retirement scope: ~500–700 LOC removed, single-cycle
deliverable, axiom-clean throughout. Prerequisites:

- Verify that no downstream theorem depends *non-rewritably* on the
  hand-written shape (e.g., via `simp [padded2DEulerGLM]` patterns
  that would need re-tuning to `simp [paddedREulerGLM]` plus an
  explicit `r = 1` instantiation).
- Confirm that the cycle 156/157/159/161 `_padCompatStarting`
  HasOrderRelativeTo_explicit witnesses can be replaced by
  `paddedREulerGLM_hasOrderZero_padCompatStartingR 1` (resp.
  r = 2, 3) without introducing extra elaborate-time costs.

Both prerequisites are tractable in a single cycle; the cycle 164
reconciliations specifically discharge any concern that the
hand-written and parametric families differ in any observable way.

**Backup if cycle 165 retirement is blocked**: pivot to `def:451A`
G-stable (the cycle 164 strategy's Priority 2 backup, which itself
remained unused this cycle since Phase B.3 closed cleanly).
