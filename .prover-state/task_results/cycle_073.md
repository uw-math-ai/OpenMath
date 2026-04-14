# Cycle 073 Results

## Worked on
Algebraic adjoint theory for Runge–Kutta methods: `IsSelfAdjoint`, `IsAdjointPair`,
GL3 M=0, concrete adjoint pair verifications, structural theorems.
Added new file `OpenMath/Adjoint.lean`.

## Approach
Formalized the algebraic adjoint theory from Hairer–Nørsett–Wanner Section II.8
and Iserles Section 4.2. Key new definitions and theorems:

**Definitions:**
- `IsSelfAdjoint`: b[i]·A[i][j] + b[j]·A[j][i] = b[i]·b[j] for all i,j
- `IsAdjointPair`: two methods sharing weights with the above cross-relation

**Structural theorems:**
1. `isSelfAdjoint_iff_algStabMatrix_zero`: M=0 ↔ self-adjoint
2. `IsSelfAdjoint.toAlgStable`: self-adjoint + non-neg weights → algebraically stable
3. `IsAdjointPair.symm`: adjoint pair relation is symmetric
4. `isSelfAdjoint_iff_adjointPair_self`: self-adjoint ↔ adjoint pair with self
5. `IsAdjointPair.consistent_iff`: adjoint pairs preserve consistency
6. `IsSelfAdjoint.satisfiesD1`: self-adjoint + consistent → D(1)
7. `IsAdjointPair.adjoint_D1_sum`: ∑ bᵢ a'ᵢⱼ = bⱼ(1−cⱼ) for adjoint pairs

**Concrete verifications (self-adjoint):**
- Implicit midpoint, GL2, GL3 (new: `rkGaussLegendre3_algStabMatrix_zero`)
- Lobatto IIIA/IIIB 2-stage

**Concrete verifications (NOT self-adjoint):**
- Forward Euler, backward Euler, Lobatto IIIC 3-stage
- Lobatto IIIA/IIIB 3-stage (despite being Nørsett-symmetric!)
- Radau IIA 3-stage

**Adjoint pairs:**
- Forward Euler ↔ Backward Euler
- Lobatto IIIA 2-stage ↔ IIIB 2-stage
- Lobatto IIIA 3-stage ↔ IIIB 3-stage

## Result
SUCCESS — new file `OpenMath/Adjoint.lean` with ~25 theorems/definitions, zero sorry's.

Key new contributions:
- GL3 algebraic stability matrix identically zero (9 entries verified)
- Complete classification table: self-adjoint vs alg-stable vs symmetric
- Structural theorem: self-adjoint + consistent → D(1)
- Structural theorem: adjoint pair D(1)-like identity

## Dead ends
- Initially attempted `IsSymmetric.toSelfAdjoint` (symmetric → self-adjoint), but discovered
  this is **mathematically false**: Lobatto IIIA 3-stage is symmetric (Nørsett) but NOT
  self-adjoint (b[0]·A[0][0] + b[0]·A[0][0] = 0 ≠ 1/36 = b[0]²). The symmetry condition
  uses the rev permutation while self-adjointness uses the transpose—these are different!
- Initially had `adjoint_D1_sum` with wrong RHS (`bⱼ·c'ⱼ` instead of `bⱼ(1−cⱼ)`).
  Fixed by carefully tracking which method's nodes appear.

## Discovery
- **Nørsett symmetry ≠ algebraic self-adjointness.** The symmetry condition
  A[i][j] + A[rev(i)][rev(j)] = b[j] involves the rev permutation, while
  self-adjointness b[i]·A[i][j] + b[j]·A[j][i] = b[i]·b[j] involves the transpose.
  These coincide for Gauss methods (which are centrosymmetric) but diverge for
  Lobatto IIIA/IIIB 3-stage.
- **Self-adjoint → D(1)** is a clean structural result connecting the algebraic
  adjoint property to simplifying assumptions. Combined with B(s) and C(s),
  this provides an alternative route to high-order proofs for Gauss methods.
- The pairing trick from cycle 072 (rev permutation) and the transpose-based
  self-adjoint theory are two distinct algebraic tools for RK analysis.

## Suggested next approach
- Extend to **Radau IA ↔ Radau IIA adjoint pairs**: these methods should form
  adjoint pairs, connecting to the "complementary pairs" theory.
- Prove **self-adjoint + B(p) + C(q) → order ≥ p+q** using the D(1) result
  as a base case, potentially improving the existing order proofs.
- Alternatively, formalize **embedded RK pairs** (Chapter 5) or the
  **Lagrange interpolation → collocation** correspondence (Theorem 2.4).
