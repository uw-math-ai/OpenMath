# Cycle 728 Results

## Worked on

§521 Step G — opening the **non-BDF** general-LMM unit-circle ladder
in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Landed all three
strategy targets:

- **G.1** `D_mul_toGLM_charpoly_eval_one_general` (mandatory)
- **G.2** `D_mul_toGLM_charpoly_eval_one_general_of_bdf` (stretch — BDF
  cross-check, recovers F.4 via the D.11b route)
- **G.3** `D_mul_toGLM_charpoly_eval_zero_general` (stretch — ξ = 0
  mirror, trivial re-export of D.11a)

Promoted `rowFAlphaResidual_eval_one_of_bdf_eq_zero` (line 2209) from
`private` to public so G.2 can cite it directly (the cleaner of the two
options the strategy offered).

## Approach

Followed the strategy's exact prescription. For G.1:
1. `rw [D_mul_toGLM_charpoly_eval_one_substituted m hz hs]` — D.11b
   form.
2. `rw [rowYQuot_eval_one m hs]` — substitutes
   `(rowYQuot m).eval 1 = -∑α(castSucc l)`.
3. `ring` — failed (see below).

For G.2: `rw G.1`, then two `Finset.sum_eq_zero` lemmas (one citing
the now-public `rowFAlphaResidual_eval_one_of_bdf_eq_zero` for the
residual sum, one zeroing `∑β castSucc` from the BDF hypothesis),
then `ring`.

For G.3: pure re-export of `D_mul_toGLM_charpoly_eval_zero_substituted`
under the G naming convention — definitionally equal, so the proof is
just the older lemma applied as a term.

## Result

**SUCCESS** — all three theorems compile and `lake build` passes (8087
jobs) with no new warnings introduced. Three separate commits as the
strategy suggested.

## Dead ends

**G.1 first attempt with bare `rw + ring`**: the strategy's predicted
"`ring` should close on first try" did not pan out. After the two
`rw`s, the LHS contains
`z * ∑ x, (β x.castSucc - β_last * α x.castSucc)` — a sum of
differences — while the algebraically-equivalent RHS has it
distributed as `z * ∑β - z * β_last * ∑α`. `ring` is a pure
ring-algebra tactic; it does not push linear maps through `Finset.sum`
or distribute scalars over sums.

**Fix**: added an intermediate `have hsum_split` that uses
`Finset.sum_sub_distrib` and `← Finset.mul_sum` to push the LHS into
the same shape, after which `ring` closes immediately. This is a
structural-only patch — no `simp`, `push_cast`, or `field_simp`
needed, exactly per the strategy's "everything lives in ℂ" hint.

## Discovery

- `ring` does not interact with `Finset.sum` distribution.
  `Finset.sum_sub_distrib` + `← Finset.mul_sum` is the reliable
  pre-step for ring identities mixing pointwise-defined and
  distributed sums. Worth keeping in mind for any future Step H
  algebra that pulls scalars over `Finset.sum`.
- Promoting `rowFAlphaResidual_eval_one_of_bdf_eq_zero` from
  `private` to public is harmless: it has a meaningful BDF-shaped
  signature and matches the public-surface conventions of the
  surrounding D.16/E.* lemmas (`D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf`
  is already public). No callers outside this module yet, so no
  downstream impact.
- The "G.2 must agree statement-wise with F.4" cross-check from the
  strategy holds: both have signature
  `(1 - z β_last) · charpoly.eval 1 = stabilityPolyPoly.eval 1` under
  the same `hbdf, hz, hs` hypotheses. F.4 routes through D.11c +
  E.2 + F.3; G.2 routes through D.11b + F.3 + D.16d. The convergence
  is real evidence that G.1 is set up correctly.

## Suggested next approach

The strategy's Step H seam is now genuinely ripe: closed-form
expansion of `∑ l, (rowFAlphaResidual m l).eval 1` for general LMMs.
The skeleton is `rowFAlphaResidual_eval_one_eq_double_sum` (line
2197 — note: this is currently `private`; promote when needed). The
F.1 analogue for off-diagonal `(charmatrix(PY 0)).adjugate k j` with
`j ≠ ⟨s-1,_⟩` is the missing infrastructure piece — that's a
self-contained adjugate-entry calculation that should fit in one
cycle.

After Step H lands, G.1's RHS will collapse to an explicit polynomial
in `α, β, z`, and we can attempt the **general**
`LMM.toGLM_isAStable_iff` directly via root-counting on the unit
circle.

A bookkeeping suggestion for the planner: the D-naming convention
(`D.11a`, `D.11b`, `D.11c`, `D.16d`, etc.) has gotten dense enough
that a one-page index file (`.prover-state/§521_index.md` or as a
section in `plan.md`) mapping each `D.*` letter to its theorem name
and route would help future cycles avoid re-deriving the topology.
File size of `StabilityCharpoly.lean` is now 2611 lines; still under
the 3000 cap but Step H may push it past, at which point a split
between D-ladder algebra and F/G-ladder evaluations would be natural.
