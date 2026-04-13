# Cycle 072 Results

## Worked on
Nørsett's even-order theorem for symmetric RK methods: symmetric + order 3 → order 4.
Added to `OpenMath/Symmetry.lean`.

## Approach
Proved the key step of Iserles Theorem 2.8 / Hairer–Nørsett–Wanner Theorem II.8.4:
if a symmetric, row-sum consistent Runge–Kutta method satisfies all order conditions
through order 3, then it automatically satisfies all four fourth-order conditions.

The proof technique for each order condition is the **pairing trick**: for any function h,
∑ h(i) = ∑ h(rev(i)) (since rev is a bijection on Fin s). Combined with the three
symmetry identities (bᵢ = b_{rev(i)}, cᵢ + c_{rev(i)} = 1, A[i][j] + A[rev(i)][rev(j)] = b[j]),
this yields sum identities that determine the fourth-order conditions from the third-order ones.

Key helper lemmas:
1. **`c_rev`**: c[rev(i)] = 1 − c[i]
2. **`symm_Ac_rev`**: f(rev(i)) = f(i) − cᵢ + 1/2, where f(i) = ∑ⱼ aᵢⱼcⱼ
3. **`symm_Ac2_sum`**: g(i) + g(rev(i)) = 1/3 − cᵢ + 2f(i), where g(i) = ∑ⱼ aᵢⱼcⱼ²
4. **`symm_D_pair`**: D(j) + D(rev(j)) = b[j], where D(j) = ∑ᵢ bᵢaᵢⱼ

Proof of each fourth-order condition:
- **order4a** (∑ bᵢcᵢ³ = 1/4): pair c³ + (1−c)³ = 1 − 3c + 3c²
- **order4b** (∑ bᵢcᵢf(i) = 1/8): pair using f(rev(i)) = f(i) − cᵢ + 1/2
- **order4c** (∑ bᵢg(i) = 1/12): pair using g(i) + g(rev(i)) identity
- **order4d** (∑ D(j)f(j) = 1/24): rewrite as ∑ D(j)f(j), pair using D and f identities

## Result
**SUCCESS** — 6 new theorems/lemmas, all sorry-free:

1. `IsSymmetric.c_rev`: c[rev(i)] = 1 − c[i]
2. `symm_Ac_rev`: Ac-sum antisymmetry under rev
3. `symm_Ac2_sum`: Ac²-sum symmetry identity
4. `symm_D_pair`: D(j) + D(rev(j)) = b[j]
5. `IsSymmetric.order4_of_order3`: symmetric + row-sum consistent + order ≥ 3 → order ≥ 4
   (the main theorem, proving all four fourth-order conditions)

All verified via Lean LSP with zero axioms (no sorry, no native_decide).

## Dead ends
None — the pairing technique worked cleanly for all four conditions.

## Discovery
- The **pairing trick** (i ↔ rev(i)) is a uniform proof technique for symmetric-method
  order theorems. Each order condition at level p+1 can be reduced to known sums at level ≤ p
  by pairing terms and using the three symmetry identities.
- The key insight is that each higher-order sum involving aᵢⱼ has a corresponding
  antisymmetry relation (like f(rev(i)) = f(i) − cᵢ + 1/2) that allows the pairing
  to "cancel" one degree and express the result in terms of lower-order sums.
- The D(j) pairing for order4d requires a two-step re-indexing: first use the A-symmetry
  to get ∑ bᵢA[rev(i)][rev(j)], then re-index via rev to get ∑ bₖA[k][rev(j)] using
  weight symmetry.

## Suggested next approach
- Extend to **order 5 → order 6**: prove `IsSymmetric.order6_of_order5`. This requires
  proving all 20 sixth-order conditions from the 17 fifth-order conditions + symmetry.
  The same pairing technique applies but with more complex intermediate sums.
- The general pattern for the even-order theorem at all levels would require B-series
  theory (Butcher group, elementary differentials), which is a substantial infrastructure
  investment.
- Alternatively, formalize embedded RK pairs (Chapter 5) or Lagrange interpolation →
  collocation correspondence (Theorem 2.4).
