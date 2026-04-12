# Cycle 047 Results

## Worked on
Lobatto IIIA 3-stage method — new file `OpenMath/LobattoIIIA3.lean`.

## Approach
Followed Option C from the strategy (more higher-order methods). Formalized the
3-stage Lobatto IIIA method, which extends the 2-stage version from the previous
cycle. Used rational coefficients throughout (no irrational numbers needed).

Key insight: the stability function of Lobatto IIIA 3-stage is identical to the
GL2 stability function (both are the (2,2)-Padé approximant to e^z). This allowed
reusing all GL2 stability results directly.

Used the collocation framework from `Collocation.lean`: proved B(4) (Simpson's rule)
and C(3) (collocation conditions), then derived order 4 via `HasOrderGe4_of_B4_C3`.

## Result
SUCCESS — 13 sorry-free theorems in new file `OpenMath/LobattoIIIA3.lean`:

1. `rkLobattoIIIA3` — Butcher tableau definition (3-stage, rational coefficients)
2. `rkLobattoIIIA3_consistent` — consistency (∑ bᵢ = 1, row-sum condition)
3. `rkLobattoIIIA3_nonNegWeights` — non-negative weights
4. `rkLobattoIIIA3_stifflyAccurate` — b = last row of A
5. `rkLobattoIIIA3_not_explicit` — not explicit (a₂₂ = 1/3 ≠ 0)
6. `rkLobattoIIIA3_B4` — Simpson's rule satisfies B(4)
7. `rkLobattoIIIA3_C3` — collocation satisfies C(3)
8. `rkLobattoIIIA3_D1` — satisfies D(1)
9. `rkLobattoIIIA3_order4` — order 4 (from B(4) ∧ C(3))
10. `rkLobattoIIIA3_not_B5` — B(5) fails (order exactly 4)
11. `lobIIIA3_aStable` — A-stable (= GL2 stability function)
12. `lobIIIA3_not_stiffDecay` — NOT L-stable (R → 1)
13. `rkLobattoIIIA3_not_algStable` — NOT algebraically stable (M₁₁ = -1/36)

## Dead ends
None — the approach was clean. All proofs followed established patterns.

## Discovery
- Lobatto IIIA 3-stage shares its stability function with GL2 (both are the
  (2,2)-diagonal Padé approximant). This means A-stability and NOT-L-stability
  follow for free from existing GL2 results.
- The B(4) ∧ C(3) → order 4 infrastructure from `Collocation.lean` works
  perfectly for this method, avoiding the need to verify 8 order conditions
  individually (as was done for RadauIIA3).
- D(1) is easily verified for this method.

## Suggested next approach
- **Lobatto IIIB 3-stage** and **Lobatto IIIC 3-stage**: natural extensions using
  the same rational coefficients and nodes. IIIC 3-stage would be order 4, L-stable.
- **A(α)-stability for BDF methods**: conceptual infrastructure from Section 4.5.
- **SDIRK3**: 3-stage SDIRK (order 3, L-stable), but requires irrational coefficients.
