# Cycle 220 Results

## Worked on

`thm:382B` — *Runge–Kutta method composition inverse* (Butcher §382 p. 307).
Goal per cycle 220 strategy §B: ship the §382 group inverse element on
the quotient `Quotient Equivalent.setoidSigma` — that is, both
absorption laws `[m · m⁻¹] = [m⁻¹ · m] = 1` at the `Equivalent` level
and their quotient-level lifts.

## Approach

Followed the strategy §J recommended invocation sequence (P1 → P6)
linearly. All deliverables fit in a single ~90-min cycle as the
strategy budgeted.

### Code shipped (six new symbols at `OpenMath/Chapter3/Section381.lean`)

**P1.** `RKTableau.inverse {s : ℕ} (M : RKTableau s) : RKTableau s` —
the literal Butcher §382 p. 307 formula
`(A i j − b j, −b i, c i − ∑ j, b j)`. ~10 LOC including docstring.
Plus three `@[simp]` unfold lemmas `inverse_A` / `inverse_b` /
`inverse_c` (~10 LOC) so projection rewrites fire cleanly in P2.

**P2.** `inverse_isRKOneStep_of_isRKOneStep` (~20 LOC). The
load-bearing algebraic observation: the same stage tuple `Y`
witnessing `M.IsRKOneStep f y₀ H y_mid` also witnesses
`M.inverse.IsRKOneStep f y_mid H y₀`. Closes via:

```lean
  · intro i
    simp only [inverse_A, sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [hY_stage i, hY_out]
    abel
  · simp only [inverse_b, neg_smul, Finset.sum_neg_distrib, smul_neg]
    rw [hY_out]
    abel
```

**P4 helper.** `isRKOneStep_of_inverse_isRKOneStep` (~20 LOC).
Symmetric helper for the left absorption law. Routed direct (NOT
through `M.inverse.inverse = M` per §C.4 of the strategy). Slightly
longer than P2 because we need to unfold `inverse_b` / `Finset.sum_neg`
on `hY_out` *before* it can rewrite — the M.inverse hypothesis has
`-M.b i` inside the sum.

**P3.** `compose_inverse_equivalent` (~14 LOC). Right absorption
`@Equivalent (s+s) 0 (M.compose M.inverse) RKTableau.id`. Proof
shape mirrors cycle 219's `compose_id_equivalent` verbatim with
`id_isRKOneStep_iff` on the *id*-side and
`inverse_isRKOneStep_of_isRKOneStep` + `equivalent_self M.inverse`
on the *compose*-side.

**P4 main.** `inverse_compose_equivalent` (~14 LOC). Left
absorption. Symmetric to P3 with sides swapped.

**P5.** `composeQ_inverse_right` and `composeQ_inverse_left`
(~10 LOC combined). Immediate `Quotient.sound` consequences of P3
and P4. Identical syntactic shape to cycle 219's
`composeQ_id_right` / `composeQ_id_left` — verified one-shot.

**P6.** Two `example`s in `namespace OpenMath.Chapter3.Section381`
(~12 LOC) exercising the quotient-level absorption laws on
`⟨2, paddedEuler⟩` and `⟨2, paddedEuler.inverse⟩`. Provides the
cycle 030 non-vacuity backbone.

### Total LOC

~110 LOC across 9 new symbols (6 theorems + 1 def + 2 examples) +
3 `@[simp]` unfold lemmas. Section381.lean grew from 3100 to 3251
lines. Warm rebuild 6.205s (34th consecutive cycle of stable §381
health since cycle 184 GPFS recovery; well within strategy §F
tolerance).

## Result

SUCCESS — all six theorems axiom-clean
`[propext, Classical.choice, Quot.sound]` (`lean_verify` confirmed
on `compose_inverse_equivalent`, `inverse_compose_equivalent`,
`composeQ_inverse_right`, `composeQ_inverse_left`,
`inverse_isRKOneStep_of_isRKOneStep`,
`isRKOneStep_of_inverse_isRKOneStep`). Sorry count remains 0. No
regressions: cycle 218/219 verification preserved (`composeQ_id_left`,
`composeQ_id_right`, `composeQ_eq_of_equivalent` all still
`[propext, Classical.choice, Quot.sound]`). `thm:382B` flipped from
`unformalized` to `formalized` in `lean_status.json`. `plan.md` row
flipped from `[ ]` to `[x]`. Both textbook forms of
`thm:382B` (Equivalent-level absorption laws AND the bracketed
quotient-level laws) closed.

## Faithfulness check

### `RKTableau.inverse {s : ℕ} (M : RKTableau s) : RKTableau s`

- Entity ID: `thm:382B` proof construction (Butcher §382 p. 307,
  inverse-method tableau).
- Textbook formula (quoted from `entities/thm_382B.json`'s
  proof_latex tableau):
  > `c1 − sum b_j   a_11 − b_1   a_12 − b_2   ···   a_1s − b_s   0   0   ···   0`
  > `c2 − sum b_j   a_21 − b_1   a_22 − b_2   ···   a_2s − b_s   0   0   ···   0`
  > ...
  > `cs − sum b_j   as1 − b_1    a_s2 − b_2   ···   a_ss − b_s   0   0   ···   0`
  > `                -b_1         -b_2        ···    -b_s        b_1 b_2 ··· b_s`
  This is the m^{-1} · m tableau. The m · m^{-1} tableau in the same
  json yields the SAME `inverse` formula: `A_ij - b_j` for the
  M.inverse block, `-b_i` for M.inverse's output row, and
  `c_i - sum b_j` for M.inverse's abscissas.
- Lean statement captures: SAME content — `M.inverse.A i j = M.A i j
  - M.b j`, `M.inverse.b i = -M.b i`, `M.inverse.c i = M.c i - ∑ j,
  M.b j` (literal Butcher formula, no simplification or reordering).
- No divergence.

### `compose_inverse_equivalent` / `inverse_compose_equivalent`

- Entity ID: `thm:382B` (Butcher §382, the textbook theorem).
- Textbook statement (quoted from `entities/thm_382B.json`):
  > `[m · m⁻¹] = [m⁻¹ · m] = 1`
- Lean statements capture: `compose_inverse_equivalent` is the
  un-bracketed `Equivalent`-level form `M.compose M.inverse ≡ id`;
  `inverse_compose_equivalent` is `M.inverse.compose M ≡ id`. These
  are equivalent to the bracketed claim via `Quotient.sound` (which
  is exactly what `composeQ_inverse_right` / `composeQ_inverse_left`
  do).
- Justification: the bracketed form `[m · m⁻¹] = 1` is captured
  literally by `composeQ_inverse_right`/`composeQ_inverse_left`.
  The `Equivalent`-level form is the more general "un-bracketed"
  statement (analogous to cycle 217's (382g) form for
  `thm:382A`) — the Quotient form is an immediate corollary, but
  the Equivalent-level form is the load-bearing one for the future
  `Group` instance proof (cycle 222+).

### Definition-smuggling check

- `RKTableau.inverse` is a definition, not a structure with Prop
  fields. No smuggling possible.
- `compose_inverse_equivalent` / `inverse_compose_equivalent` /
  `composeQ_inverse_right` / `composeQ_inverse_left` are
  theorems with substantive proofs (no `exact h_hypothesis`
  identity-shenanigans). The proofs invoke cycle 213/214
  `compose_isRKOneStep_iff`, cycle 203 `equivalent_self`, cycle 219
  `id_isRKOneStep_iff`, and the new cycle 220 step-inversion
  helpers — substantive mathematical work.

### Tautology check

- None of the six new theorems' conclusions appear verbatim as
  hypotheses. All six involve genuine combination of the
  step-inversion lemmas with `compose_isRKOneStep_iff` + uniqueness
  from `equivalent_self`.

### Hypothesis strength check

- No extra hypotheses on `M : RKTableau s`. No completeness
  hypothesis needed on `N` — the proofs go through the existing
  `Equivalent`'s `[CompleteSpace N]` quantifier from `equivalent_self`.
- No `0 < s` / `[NeZero s]` hypotheses (per strategy §I — `s = 0` is
  vacuously valid).

## Dead ends

### Strategy §C `equivalent_self.{u}` annotation

The strategy §B P3/P4 prescribed `M.inverse.equivalent_self.{u}` and
`M.equivalent_self.{u}` with explicit universe annotation. R7 in
the strategy §D anticipated this might be needed. Lean rejected
this — `equivalent_self` is universe-monomorphic (no `.{u}` in its
declaration at line 1802). Fix (5 min): dropped `.{u}` from the
call sites. Cycle 219's `compose_id_equivalent` actually uses the
unannotated form `M.equivalent_self f L hL` (which the cycle 220
strategy mis-quoted as needing `.{u}`).

### Dot-notation universe parsing

`M.compose_inverse_equivalent.{u}` is parsed as
`M.{u}.compose_inverse_equivalent` (Lean treats `.{u}` as belonging
to the leftmost identifier `M`, not the rightmost). Lean error:
`invalid use of explicit universe parameters, M is a local
variable`. Fix (2 min): rewrite as `compose_inverse_equivalent.{u}
M` (function-application form). Same fix for `inverse_compose_equivalent.{u} M`.

### No other dead ends

All other anticipated risks R1–R6 did NOT fire. R1
(`Finset.sum_neg_distrib` name drift) pre-confirmed via
`lean_loogle` — the name is exactly `Finset.sum_neg_distrib` (older
form) and it's the active Mathlib name. R2 (`linear_combination`
failure on module goals) — sidestepped entirely: `abel` closes
both stage- and output-equation goals after the `simp only [...]`
+ `rw [hY_stage i, hY_out]` preprocessing. R3 (field projection
unfolds) — `@[simp]` unfold lemmas defined inline make this a
no-op. R4 (`Equivalent` quantifier shape) — cycle 219 pattern
applied verbatim. R5 (`IsRKOneStep` instance-argument unpacking) —
`intro N _ _ _ f L hL` (three underscores) per cycle 219. R6
(spurious `.{u}` on `RKTableau`) — never attempted.

## Discovery

### `abel` closes module-equation goals after rewriting hypotheses

Cycle 207's `pReduced_equivalent` proof (which the strategy §D R2
suggested as a model if `linear_combination` failed) uses similar
patterns. Lesson: for goals of the shape "LHS in N = RHS in N
where both sides are linear combinations of summands `H • ∑ c_i •
f (Y i)`", the recipe is:
1. `simp only [...]` to unfold all `def`-level definitions and
   apply distributivity laws (`sub_smul`, `Finset.sum_sub_distrib`,
   `smul_sub`, `neg_smul`, `Finset.sum_neg_distrib`, `smul_neg`).
2. `rw [hyp₁, hyp₂, ...]` to substitute the constraint hypotheses
   on the way to a pure abelian-group equality.
3. `abel` (or `module` if `abel` fails) to discharge.

This pattern recurs throughout the §382 group structure proofs
(cycle 219's `compose_id_equivalent`/`id_compose_equivalent` used
the same shape — note cycle 219 didn't need step 1 because
`id_isRKOneStep_iff` is closed by `simpa`). Cycle 220's two new
step-inversion proofs are the most arithmetically-involved
instances yet.

### `Finset.sum_neg_distrib` vs `Finset.sum_neg`

`Finset.sum_neg` in current Mathlib is a strict-monotonicity
result (`∀ i ∈ s, f i < 0 → ∑ < 0`). The "negation pulls outside
the sum" lemma is `Finset.sum_neg_distrib`. Cycle 220 confirms
this name; future cycles can rely on it.

### `equivalent_self` is universe-monomorphic

Cycle 203's `equivalent_self` declaration omits `.{u}` annotation.
This is *not* an oversight — it works because `Equivalent`'s
universe-polymorphism is implicit in its `∀ {N : Type*}` quantifier,
and the universe is unified from the outer scope when
`equivalent_self` is applied. Future strategy authors: do NOT
recommend `M.equivalent_self.{u}` in call sites.

### Dot-notation universe annotation is rightmost-only

`X.f.{u}` is `X.{u}.f`, not `X.(f.{u})`. To pass universe to a
namespace function via dot notation, use function-application
form: `f.{u} X` instead of `X.f.{u}`. This is a common subtle
trap when refactoring between dot-notation and explicit
function-application styles. Apply only to fully-qualified
identifiers (e.g., `Equivalent.setoidSigma.{u}` works because the
namespace path is the whole identifier).

## Suggested next approach

Cycle 221+ outlook per cycle 220 strategy §G housekeeping
discussion:

**Cycle 221** — §382 associativity at the `Equivalent` level.
Target: `compose_equivalent_compose_assoc : @Equivalent ((s₁+s₂)+s₃)
(s₁+(s₂+s₃)) ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose
M₃))`. This finesses cycle 210's deferred HEq-plumbing blocker on
the *un-quotiented* `compose_assoc : (M₁.compose M₂).compose M₃ =
M₁.compose (M₂.compose M₃)` (which requires HEq because stage
counts `(s₁+s₂)+s₃ ≠ s₁+(s₂+s₃)` are not defeq). The
`Equivalent`-form sidesteps HEq entirely by working at the abstract
`IsRKOneStep` level (`compose_isRKOneStep_iff` factors both sides
into nested sequential steps, and `equivalent_self` collapses the
uniqueness). LOC estimate: ~40 (analogous to cycle 217's
heterogeneous `compose_equivalent_compose`). The
`Quotient.inductionOn₃` + `Quotient.sound` lift to a quotient-level
`composeQ_assoc` follows for ~15 LOC.

**Cycle 222** — `instance : Group (Quotient Equivalent.setoidSigma)`.
With identity (cycle 219), inverse (cycle 220), and associativity
(cycle 221) all in hand, the `Group` instance is mechanical:
plug in `composeQ` for `mul`, `Quotient.mk ⟨0, RKTableau.id⟩` for
`one`, `Quotient.map (fun ⟨s, M⟩ => ⟨s, M.inverse⟩) ...` for `inv`,
discharge the four group axioms via `composeQ_id_left`,
`composeQ_id_right`, `composeQ_inverse_left`,
`composeQ_inverse_right`, and `composeQ_assoc`. LOC estimate: ~30
including the `inv` definition's respect-of-`Equivalent` proof
(probably needs a `compose_equivalent_compose`-style lemma for
`inverse`: if `M ≡ M'` then `M.inverse ≡ M'.inverse`; that may
require an extra ~30 LOC of cycle 222 setup or could be cycle 221
work).

**§441 Phase C.2** — Still GPFS-blocked (37th consecutive timeout).
No change.
