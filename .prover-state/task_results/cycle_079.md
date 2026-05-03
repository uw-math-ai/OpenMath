# Cycle 079 Results

## Worked on
`thm:410D` (Butcher §410D, log-form order condition for linear multistep methods)
in `OpenMath/Chapter4/Section410.lean`.

## Approach
Per the Cycle 079 strategy's Priority 0 check: ran one
`mcp__aristotle__get_status` call on project
`18504be5-2481-4d60-9d7b-12b8a5cd2b47` (the cycle 077 §410D log-form
helper batch). Status: **COMPLETE, 100%**. Aristotle's
`ARISTOTLE_SUMMARY.md` reported all five sub-lemmas closed with no
sorry's and only standard axioms.

The strategy then directed Path A — "incorporate §410D Aristotle
results". The strategy assumed the §410D scaffold was already
landed at lines ~949 and ~969 of `Section410.lean` (per the
`thm_410D_substitution.md` issue description). However, on
inspection: the file was 799 lines with no §410D scaffold, no
`oneOverOnePlusPS`/`logOnePlusPS` definitions, and no `thm_410D`
statement. **The cycle 077 issue file was aspirational — the §410D
scaffold was never committed to git**. So Path A had to be expanded
from "drop in two missing proofs" into "land the entire §410D
infrastructure plus theorem".

This was still feasible because Aristotle had supplied a working
self-contained proof of all five sub-lemmas. The integration plan:

1. Append `oneOverOnePlusPS`, `logOnePlusPS` definitions, basic
   coefficient lemmas (`oneOverOnePlusPS_coeff`,
   `logOnePlusPS_constantCoeff`, `logOnePlusPS_coeff_one`).
2. Append the five Aristotle-proved helpers verbatim, adapting only
   the namespace (`AristotleCycle077` → `OpenMath.Chapter4.Section410`)
   and using existing in-file definitions (`expPS`, `expNegPS`,
   `expPS_mul_expNegPS_eq_one`).
3. Append `genFnLog M := subst logOnePlusPS (genFn M)`.
4. Prove `thm_410D` as a 4-line chain: `rw [thm_410B]; unfold
   genFnLog; refine ⟨coeff_subst_eq_zero_of_coeff_eq_zero ...,
   coeff_eq_zero_of_coeff_subst_eq_zero ... ...⟩`.
5. Land two non-vacuity witnesses
   (`explicitEulerLMM_genFnLog_O_z2`,
   `explicitEulerLMM_hasOrderAtLeast_one_via_410D`).

After insertion, `lake env lean OpenMath/Chapter4/Section410.lean`
returned exit 0 with only linter warnings (unused simp arguments
in Aristotle's tactic blocks). `lake build OpenMath.Chapter4.Section410`
completed with 8030 jobs, no errors. `#print axioms` on `thm_410D`
and the four load-bearing sub-lemmas all returned
`[propext, Classical.choice, Quot.sound]` only.

## Result
**SUCCESS.** `thm:410D` is fully formalized in
`OpenMath/Chapter4/Section410.lean` as
`OpenMath.Chapter4.Section410.thm_410D`. Progress 50/175 → 51/175.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `def oneOverOnePlusPS`
- Textbook concept: `(1+z)^{-1} = 1 - z + z² - z³ + ...` (geometric
  series). Per `thm_410D.json` `context_latex`: this is the natural
  formal-power-series inverse of `1 + z`.
- Lean statement: `PowerSeries.mk fun n => (-1)^n` with the
  validation `onePlusX_mul_oneOverOnePlusPS_eq_one` proving
  `(1 + X) · oneOverOnePlusPS = 1`.
- Captures: **same content** (definition matches textbook
  power-series form, identity property is proved).

### `def logOnePlusPS`
- Textbook (`thm_410D.json` variables.log(1+z)):
  > "log(1+z) is defined for |z|<1 by its power series:
  >  log(1+z) = z - (1/2)z^2 + (1/3)z^3 - ..."
- Lean statement: `PowerSeries.mk fun n => if n = 0 then 0 else
  (-1)^(n-1) / n`. So `coeff 0 = 0`, `coeff 1 = 1`, `coeff 2 = -1/2`,
  `coeff 3 = 1/3`, ...
- Captures: **same content** (matches Butcher's power-series
  definition exactly).

### `def genFnLog`
- Textbook (`thm_410D.json` equations.410d):
  > "α((1+z)^{-1}) - log(1+z) β((1+z)^{-1}) = O(z^{p+1})"
- Lean statement: `genFnLog M := PowerSeries.subst logOnePlusPS (genFn M)`.
  Unfolding via the algebra-hom property of `subst` and
  `subst_logOnePlusPS_expNegPS` (`exp(-log(1+z)) = (1+z)⁻¹`):
  `subst logOnePlusPS (genFn M) = α((1+z)⁻¹) - log(1+z) · β((1+z)⁻¹)`.
- Captures: **same content** (the substitution faithfully realizes
  Butcher's eq. 410d in the backward-sign convention used throughout
  Chapter 4).

### `theorem thm_410D`
- Textbook (`thm_410D.json` statement_latex):
  > "A linear multistep formula [α, β] has order p if and only if
  >  z/log(1+z) · α(1+z) + β(1+z) = O(z^p)."
- Lean statement: `M.HasOrderAtLeast p ↔ ∀ j ≤ p,
  coeff j (genFnLog M) = 0`, where `genFnLog M = subst log (genFn M)`
  evaluates to `α((1+z)⁻¹) - log(1+z) · β((1+z)⁻¹)`.
- Captures: **same content**, expressed in the backward-sign
  convention. The `context_latex` field of `thm_410D.json`
  explicitly gives the equivalent form
  `α((1+z)⁻¹) - log(1+z) · β((1+z)⁻¹) = O(z^{p+1})` (eq. 410d) as
  the derived condition the theorem is about, so the Lean statement
  is faithful even though it differs syntactically from
  `statement_latex`.

### Helper theorems (`onePlusX_mul_oneOverOnePlusPS_eq_one`,
`coeff_subst_eq_zero_of_coeff_eq_zero`,
`coeff_eq_zero_of_coeff_subst_eq_zero`,
`subst_logOnePlusPS_expPS_eq_one_add_X`,
`subst_logOnePlusPS_expNegPS`, plus the auxiliary
`derivative_expPS`, `derivative_logOnePlusPS`,
`eq_zero_of_derivative_eq_mul_oneOverOnePlusPS`,
`constantCoeff_subst_logOnePlusPS_expPS`)
- These are not Butcher-named lemmas; they are infrastructure for
  the §410D substitution argument.
- Each performs genuine power-series algebra (Cauchy product,
  order-of-substitution monotonicity, ODE uniqueness, multiplicative-
  inverse uniqueness). None re-export a hypothesis. None of their
  conclusions appear verbatim as hypotheses.

### Pre-commit checklist outcomes
- [x] **Tautology check**: `thm_410D` conclusion `M.HasOrderAtLeast
      p ↔ ∀ j ≤ p, coeff j (genFnLog M) = 0` is not a hypothesis.
- [x] **Identity check**: `thm_410D` proof is `rw [thm_410B];
      unfold genFnLog; refine ⟨_, _⟩` followed by application of
      the substitution lemmas — does real combinatorial work.
- [x] **Definition smuggling check**: `oneOverOnePlusPS`,
      `logOnePlusPS`, and `genFnLog` are all defined directly from
      their power-series coefficient formulas (or from `subst`).
      None encode an "order condition" as a definition; the order
      condition is genuinely the conclusion of `thm_410D`.
- [x] **Hypothesis strength check**: `thm_410D` requires only
      `(M : LinearMultistepMethod k) (p : ℕ)` — same as the
      textbook. No extra hypotheses.
- [x] **Absent theorem check**: All four sub-lemmas referenced in
      the proof of `thm_410D` (`thm_410B`, `genFnLog`,
      `coeff_subst_eq_zero_of_coeff_eq_zero`,
      `coeff_eq_zero_of_coeff_subst_eq_zero`) are present and
      proved.
- [x] **`lake build` clean**: `lake build OpenMath.Chapter4.Section410`
      completed successfully (8030 jobs, only linter warnings).
- [x] **Axioms**: `#print axioms thm_410D` →
      `[propext, Classical.choice, Quot.sound]`. Same for the four
      load-bearing sub-lemmas.

## Dead ends
None. The Aristotle batch returned working proofs for all five
sub-lemmas, and integration was clean. The only friction was the
discovery that the §410D scaffold the strategy assumed was present
had never been committed — but this added scope rather than
blocking progress, since the Aristotle file was self-contained
enough to drop in.

A few of Aristotle's tactic blocks generate linter warnings about
unused simp arguments. These are cosmetic and do not affect
correctness; left as-is to avoid risk of perturbing the working
proof.

## Discovery
1. **Aristotle's ODE-uniqueness route works for log/exp identities
   in formal power series.** The proof of
   `subst_logOnePlusPS_expPS_eq_one_add_X` shows: to prove
   `subst log expPS = 1 + X`, define `G := subst log expPS - (1+X)`,
   show `G(0) = 0` and `D(G) = G · (1+X)⁻¹`, and conclude `G = 0`.
   The only non-trivial input is `D(expPS) = expPS` (Aristotle's
   `derivative_expPS`) and `D(logOnePlusPS) = oneOverOnePlusPS`
   (Aristotle's `derivative_logOnePlusPS`), both of which fall to
   coefficient-by-coefficient computation.
   This is a generally useful technique for any
   `subst (formal power-series log) (formal power-series exp) =
   linear` style identity.
2. **Aristotle's reverse-direction substitution lemma**
   (`coeff_eq_zero_of_coeff_subst_eq_zero`) closes the previously
   blocking subroutine for §410D in roughly 30 lines via strong
   induction on `j`, leveraging the leading-coefficient identity
   `coeff (j+1) (g^(j+1)) = (coeff 1 g)^(j+1) = 1` for unit-leading
   `g`. Cycle 077's task results estimated this would need a
   dedicated helper; Aristotle inlined it via `induction'`-with-
   `Finset.sum_eq_single`.
3. **Issue files describing scaffolds that were never committed are
   misleading.** The cycle 077 issue
   `thm_410D_substitution.md` describes line numbers (949, 969) for
   sorries that don't exist in committed code. Future planners
   should verify the assumed file state with `git ls-files` /
   `wc -l` before assuming the scaffold is in place.

## Suggested next approach
The §410 cluster (`thm:410A`, `thm:410B`, `thm:410C`, `thm:410D`)
is now fully closed. Natural next picks:

1. **`lem:383B`** — *Associativity of multiplicative forest mappings*
   (Butcher §383). The cycle 079 strategy's Path B already laid out
   a clean three-sub-lemma decomposition; cycle 080 can pick this
   up directly. Requires no new infrastructure beyond what's already
   in `OpenMath/Chapter3/Section383.lean` (cycle 078).
2. **`thm:422A`** — *The underlying one-step method (LMM)* (§422).
   Builds on §410 (now complete). Per `plan.md` line 181 this is
   the chapter-4 successor cluster after §410.
3. **`thm:441C` / `lem:441A` / `lem:441B`** — the order-bound
   cluster for stable LMMs. Depends on §410D (now closed) and
   would directly use `thm_410D` as the order characterization.
4. **Issue cleanup**: the `thm_410D_substitution.md` issue file is
   now resolved — cycle 080 should delete it (or move it to a
   `resolved/` sub-folder if such a convention exists).

The Aristotle-first strategy continues to pay dividends: this
cycle's 5-lemma batch unblocked the entire §410D theorem with no
manual proof work needed beyond gluing the `thm_410D` ↔ chain
through `thm_410B`. The cycle 077 batch represents ~80 minutes of
queue time + 2.5 hours of Aristotle compute for what would have
been multiple cycles of manual ODE-uniqueness and Bell-polynomial
work.
