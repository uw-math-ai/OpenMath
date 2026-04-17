# Cycle 100 Results

## Worked on
Definition 355A — Order Stars and the Ehle Barrier (Section 355 of Iserles).

Created `OpenMath/OrderStars.lean` with complete, sorry-free formalization.

## Approach
1. Wrote the full file with sorry-first structure: definitions, structural properties, topological properties, exact exponential results, A-stability link, forward Euler verification, imaginary axis characterization, and Ehle wedge classification.
2. Submitted to Aristotle (project c39f5a9d) while waiting for Mathlib build.
3. Closed all sorrys manually before Aristotle completed — Aristotle results not needed.
4. Fixed two compilation issues:
   - `exp_add` ambiguity (resolved with `Complex.exp_add`)
   - `rexp_zero` identifier (corrected to `Real.exp_zero`)

## Result
SUCCESS — All 22 theorems proved, zero sorrys. File compiles clean.

### Theorems proved:
- `orderStar_norm_eq`: ‖R(z)·e⁻ᶻ‖ = ‖R(z)‖·exp(-Re(z))
- `orderStar_union`: 𝒜⁺ ∪ 𝒜⁻ ∪ 𝒜⁰ = ℂ
- `orderStarPlus_disjoint_minus`, `orderStarPlus_disjoint_bdry`, `orderStarMinus_disjoint_bdry`
- `isOpen_orderStarPlus`, `isOpen_orderStarMinus`, `isClosed_orderStarBdry`
- `mem_orderStarBdry_zero`: R(0)=1 → 0 ∈ 𝒜⁰
- `orderStarBdry_exp_eq_univ`, `orderStarPlus_exp_eq_empty`, `orderStarMinus_exp_eq_empty`
- `mem_orderStarPlus_of_norm_gt_one`: ‖R(z)‖>1 ∧ Re(z)≤0 → z ∈ 𝒜⁺
- `orderStarPlus_inter_lhp_nonempty_of_not_aStable`
- `forwardEuler_neg3_mem_orderStarPlus`, `forwardEuler_orderStarPlus_inter_lhp`
- `orderStarPlus_imaginaryAxis`, `orderStarMinus_imaginaryAxis`, `orderStarBdry_imaginaryAxis`
- `InEhleWedge` definition + 9 classification theorems for Padé pairs

## Dead ends
None — the strategy target was well-chosen and all proofs went through cleanly.

## Discovery
- `Complex.norm_exp` is the key bridge lemma: ‖exp z‖ = Real.exp z.re
- Lean 4.28 has `exp_add` ambiguity between `Real.exp_add` and `Complex.exp_add` when both `Complex` and `Real` are opened — must qualify explicitly
- `rexp_zero` is not a valid identifier; use `Real.exp_zero`
- The imaginary axis characterization is clean: (↑t * I).re = 0, so exp factor = 1

## Suggested next approach
- Theorem 355B (Ehle barrier proper): requires winding number theory. The `InEhleWedge` classification is ready to serve as the conclusion.
- Theorem 301A: continue rooted tree infrastructure (List-based BTree approach)
- Theorem 342C remaining implications: requires elementary differentials (def:310A)

## Aristotle
- Submitted project c39f5a9d (COMPLETE). Not incorporated — all proofs were completed manually before Aristotle finished.
