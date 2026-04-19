import OpenMath.BNStability
import OpenMath.GaussLegendre3
import OpenMath.RadauIA2
import OpenMath.RadauIA3
import OpenMath.RadauIIA3

/-!
# BN-Stability Corollaries for Collocation Families

These are concrete Chapter 4 corollaries of Theorem 357C:
once a collocation Runge–Kutta method has been proved algebraically stable,
BN-stability follows immediately.

This file packages the already-formalized Gauss and Radau families into
explicit BN-stability theorems.
-/

namespace ButcherTableau

/-- The Gauss-Legendre 2-stage collocation method is BN-stable because it is
algebraically stable. -/
theorem rkGaussLegendre2_bnStable : rkGaussLegendre2.IsBNStable :=
  alg_stable_implies_bn_stable rkGaussLegendre2_algStable

/-- The Gauss-Legendre 3-stage collocation method is BN-stable because it is
algebraically stable. -/
theorem rkGaussLegendre3_bnStable : rkGaussLegendre3.IsBNStable :=
  alg_stable_implies_bn_stable rkGaussLegendre3_algStable

/-- The Radau IA 2-stage collocation method is BN-stable because it is
algebraically stable. -/
theorem rkRadauIA2_bnStable : rkRadauIA2.IsBNStable :=
  alg_stable_implies_bn_stable rkRadauIA2_algStable

/-- The Radau IA 3-stage collocation method is BN-stable because it is
algebraically stable. -/
theorem rkRadauIA3_bnStable : rkRadauIA3.IsBNStable :=
  alg_stable_implies_bn_stable rkRadauIA3_algStable

/-- The Radau IIA 3-stage collocation method is BN-stable because it is
algebraically stable. -/
theorem rkRadauIIA3_bnStable : rkRadauIIA3.IsBNStable :=
  alg_stable_implies_bn_stable rkRadauIIA3_algStable

end ButcherTableau
