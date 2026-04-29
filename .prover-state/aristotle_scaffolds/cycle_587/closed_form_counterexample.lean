import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

private noncomputable def alphaCounter : AugSeries :=
  ⟨1, fun τ =>
    match τ with
    | BTree.leaf => 1
    | _ => 0⟩

private noncomputable def betaCounter : AugSeries :=
  ⟨1, fun τ =>
    match τ with
    | BTree.node [BTree.node []] => 1
    | _ => 0⟩

private theorem actual_counterexample_value :
    bSeriesConvAug alphaCounter betaCounter
        (BTree.node [BTree.node [BTree.leaf]]) = 1 := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest,
    alphaCounter, betaCounter]

private theorem naive_counterexample_rhs :
    alphaCounter.toFun (BTree.node [BTree.node [BTree.leaf]])
        * betaCounter.emptyVal
      + ∑ S : Finset (Fin 1), alphaCounter.toFun (BTree.node [BTree.leaf]) ^ S.card
          * betaCounter.toFun
              (BTree.node (List.replicate (1 - S.card) (BTree.node [BTree.leaf])))
      = 0 := by
  rw [sum_finset_fin_succ_card_eq 0
    (fun k => alphaCounter.toFun (BTree.node [BTree.leaf]) ^ k
      * betaCounter.toFun
          (BTree.node (List.replicate (1 - k) (BTree.node [BTree.leaf]))))]
  simp [alphaCounter, betaCounter,
    show ∀ S : Finset (Fin 0), S = ∅ from fun S => by
      ext x
      exact x.elim0]

end ButcherTableau
