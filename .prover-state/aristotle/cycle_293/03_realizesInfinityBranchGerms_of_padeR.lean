import OpenMath.PadeOrderStars

open Complex

def padeR_realizesInfinityBranchGerms
    (n d : ℕ) (data : OrderArrowTerminationData) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  refine realizesInfinityBranchGerms_of_padeR ?_ ?_
  · sorry
  · sorry
