import OpenMath.ButcherGroup.Section386Conv

open Finset

namespace ButcherTableau

mutual
  theorem aristotle_innerCut_canon_count
      (α : BTree → ℝ) (τ : BTree) :
      ((τ.innerCut α).countP
        (· = ((some τ, (1 : ℝ)) : Option BTree × ℝ))) = 1 := by
    sorry

  theorem aristotle_innerCutForest_canon_count
      (α : BTree → ℝ) (children : List BTree) :
      ((BTree.innerCutForest children α).countP
        (· = children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ)))) = 1 := by
    sorry
end

end ButcherTableau
