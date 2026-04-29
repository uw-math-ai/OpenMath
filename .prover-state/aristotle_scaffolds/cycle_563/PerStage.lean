import OpenMath.ButcherGroup.Section384SlicesMixed

open Finset

namespace ButcherTableau

theorem cycle563_kept_triple_leaf_summand_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    (∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j)
      =
        (coef BTree.leaf) ^ 3 * (∑ j : Fin t, t₂.A i j)
        + 3 * (coef BTree.leaf) ^ 2 *
            (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))
        + 3 * (coef BTree.leaf) *
            (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 2)
        + (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 3) := by
  sorry

end ButcherTableau
