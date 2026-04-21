import OpenMath.Pade
import OpenMath.OrderStars

open Complex

theorem thm_355D_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (happrox : IsRationalApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  simpa using
    (thm_355D_of_concreteRationalApprox
      (R := padeR n d) data happrox hreal hconcrete)

theorem thm_355E'_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  simpa using
    (thm_355E'_of_concreteRationalApprox
      (R := padeR n d) data hpade hreal hconcrete)

theorem concreteRationalApproxToExp_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hcont : Continuous (fun z => ‖padeR n d z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_eq_exp :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖padeR n d z * exp (-z)‖ < 1)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖padeR n d z * exp (-z)‖)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        1 < ‖padeR n d z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        ‖padeR n d z * exp (-z)‖ < 1) :
    ConcreteRationalApproxToExp (padeR n d) data := by
  simpa using
    (concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions_of_no_nonzero_eq_exp
      (R := padeR n d) data hcont
      hzero_not_mem_down_support hzero_not_mem_up_support hno_nonzero_eq_exp
      hlocal_minus_near_down hlocal_plus_near_up
      hfar_plus_on_orderWeb hfar_minus_on_orderWeb)

/-- Honest Padé-local boundary for the repaired Ehle barrier seam.
This bundles exactly the concrete hypotheses currently needed to apply the
Padé-side 355D/355E' wrappers together with `ehle_barrier_nat`, without
pretending that the explicit endpoint counts already supply the separate 355G
correction-term witnesses. -/
structure PadeREhleBarrierInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  numeratorDegree_eq : data.numeratorDegree = n
  denominatorDegree_eq : data.denominatorDegree = d
  pade : IsPadeApproxToExp data
  realizesInfinityBranchGerms : RealizesInfinityBranchGerms (padeR n d) data
  concrete : ConcreteRationalApproxToExp (padeR n d) data
  ehle : EhleBarrierInput data

def padeREhleBarrierInput_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hpade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hcont : Continuous (fun z => ‖padeR n d z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_eq_exp :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖padeR n d z * exp (-z)‖ < 1)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖padeR n d z * exp (-z)‖)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        1 < ‖padeR n d z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        ‖padeR n d z * exp (-z)‖ < 1)
    (hehle : EhleBarrierInput data) :
    PadeREhleBarrierInput n d data := by
  refine ⟨hnum, hden, hpade, hreal, ?_, hehle⟩
  exact concreteRationalApproxToExp_of_padeR
    hcont
    hzero_not_mem_down_support
    hzero_not_mem_up_support
    hno_nonzero_eq_exp
    hlocal_minus_near_down
    hlocal_plus_near_up
    hfar_plus_on_orderWeb
    hfar_minus_on_orderWeb

theorem PadeREhleBarrierInput.thm_355D
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  exact thm_355D_of_padeR n d data h.pade.toIsRationalApproxToExp
    h.realizesInfinityBranchGerms h.concrete

theorem PadeREhleBarrierInput.thm_355E'
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  exact thm_355E'_of_padeR n d data h.pade h.realizesInfinityBranchGerms h.concrete

theorem PadeREhleBarrierInput.ehle_barrier_nat
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    InEhleWedge n d := by
  exact _root_.ehle_barrier_nat n d
    ⟨data, h.numeratorDegree_eq, h.denominatorDegree_eq, h.ehle⟩

/-- First concrete Padé-side consumer of the repaired Ehle barrier boundary.
What remains below this theorem is to construct the three concrete inputs now
made explicit by `PadeREhleBarrierInput`: realized infinity branch germs for
`padeR n d`, the concrete no-infinity contradiction package, and the separate
355G correction-term witnesses in `EhleBarrierInput`. -/
theorem ehle_barrier_nat_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    InEhleWedge n d := by
  exact h.ehle_barrier_nat

/-- For Padé order webs, the exact coincidence exclusion is an honest consequence
of the unit-level exclusion already exposed by `OrderStars`. The fully uniform
statement without this extra hypothesis is false already for `padeR 0 0 = 1`. -/
theorem padeR_no_nonzero_eq_exp_on_orderWeb
    (n d : ℕ)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
        ‖padeR n d z * exp (-z)‖ = 1 → False) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  intro z hz_ne hz_web hz_eq
  apply hno_nonzero_unit_points_on_orderWeb z hz_ne hz_web
  calc
    ‖padeR n d z * exp (-z)‖ = ‖exp z * exp (-z)‖ := by simp [hz_eq]
    _ = ‖(1 : ℂ)‖ := by rw [← Complex.exp_add]; simp
    _ = 1 := by simp
