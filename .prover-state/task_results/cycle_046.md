# Cycle 046 Results

## Worked on
Lobatto IIIA and IIIB 2-stage methods (Option C from strategy: more higher-order methods / Lobatto IIIA).

## Approach
- **Sorry-first**: Wrote complete proof structure for Lobatto IIIA with all statements, verified compilation, then closed all proofs. No sorrys needed — all proofs close directly.
- **Lobatto IIIA 2-stage** (`OpenMath/LobattoIIIA.lean`): Defined the Butcher tableau and proved:
  - Consistency (weight sum + row-sum)
  - Order 2 (and NOT order 3)
  - Non-negative weights
  - Not explicit
  - Stiffly accurate (bᵢ = a_{2,i})
  - Stability function R(z) = (2+z)/(2-z)
  - **A-stability**: |R(z)| ≤ 1 for Re(z) ≤ 0, via |D|² − |N|² = −8Re(z) ≥ 0
  - **NOT L-stable**: R(x) → −1 as x → −∞ (proved tendsto + uniqueness argument)
  - **NOT algebraically stable**: M₁₁ = −1/4 < 0
- **Lobatto IIIB 2-stage** (`OpenMath/LobattoIIIB.lean`): Defined the Butcher tableau and proved:
  - Weight condition (∑ bᵢ = 1)
  - **NOT row-sum consistent** (c₁ = 0 ≠ ∑ⱼ a₁ⱼ = 1/2) — hence NOT consistent
  - Order 2 despite not being consistent (quadrature conditions hold)
  - NOT order 3
  - A-stability and NOT L-stable (reuses Lobatto IIIA stability function proofs)
  - **NOT algebraically stable**: M₂₂ = −1/4 < 0
- Updated `OpenMath.lean` root import file to include all missing files (DahlquistEquivalence, Collocation, SDIRK, RadauIIA3, LobattoIIIC, LobattoIIIA, LobattoIIIB).

## Result
**SUCCESS** — Two new sorry-free files. All proofs compile cleanly with no errors and no warnings. All key theorems verified (standard axioms only).

## Dead ends
- `Complex.ofNat_re` and `Complex.dist_ofReal` don't exist in current Mathlib — had to use alternative approaches (`norm_num at this` and `dist_comm; dist_eq_norm` with real form rewrites).
- `NormedAddCommGroup.tendsto_nhds` not applicable for non-zero limits — used `Metric.tendsto_nhds` instead.
- `nlinarith` struggles with `ε * (2 - x) > 4` from `x < -4/ε` — needed explicit intermediate arithmetic steps.

## Discovery
- Lobatto IIIA and IIIB share the same stability function R(z) = (2+z)/(2-z), identical to the implicit midpoint rule. This allows IIIB to directly reuse IIIA's A-stability proof.
- Lobatto IIIB is interesting as a formally non-consistent (row-sum fails) method that still has order 2. This demonstrates that order can be achieved through quadrature conditions alone.
- The Lobatto III family is now fully represented: IIIA, IIIB, IIIC — with contrasting stability properties (only IIIC is L-stable and algebraically stable).

## Suggested next approach
- **SDIRK3** (3-stage, order 3, L-stable) — follows the SDIRK2 pattern.
- **Extend collocation framework**: Prove Gauss nodes give B(2s), connect GL2 order 4 to B(4)∧C(2)∧D(2).
- **3-stage Gauss-Legendre** (order 6) — ambitious but impactful.
