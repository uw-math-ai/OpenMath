import OpenMath.PadeOrderStars.Core

open Complex

/-- Compact Whyburn-style separation seam: if two closed subsets land in
different connected components, they can be separated by a clopen set. -/
private theorem exists_clopen_separating_closed_sets_of_component_images_disjoint
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj :
      Disjoint ((ConnectedComponents.mk) '' A) ((ConnectedComponents.mk) '' B)) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ B ⊆ Cᶜ := by
  let A' : Set (ConnectedComponents X) := ConnectedComponents.mk '' A
  let B' : Set (ConnectedComponents X) := ConnectedComponents.mk '' B
  have hA' : IsClosed A' := by
    exact (hA.isCompact.image ConnectedComponents.continuous_coe).isClosed
  have hB' : IsClosed B' := by
    exact (hB.isCompact.image ConnectedComponents.continuous_coe).isClosed
  have hA_sub : A' ⊆ B'ᶜ := by
    intro x hxA hxB
    exact hdisj.le_bot ⟨hxA, hxB⟩
  obtain ⟨D, hDclopen, hAD, hDB⟩ :=
    exists_clopen_of_closed_subset_open hA' hB'.isOpen_compl hA_sub
  refine ⟨ConnectedComponents.mk ⁻¹' D, ?_, ?_, ?_⟩
  · exact (ConnectedComponents.isQuotientMap_coe.isClopen_preimage).2 hDclopen
  · intro x hx
    exact hAD ⟨x, hx, rfl⟩
  · intro x hx hxC
    have hxB' : ConnectedComponents.mk x ∈ B' := ⟨x, hx, rfl⟩
    exact hDB hxC hxB'

/-- If no connected subset meets two closed sets in a compact Hausdorff space,
their points lie in different connected components, hence the previous clopen
separation lemma applies. -/
private theorem exists_clopen_of_no_connected_subset_meeting_both
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB :
      ∀ S : Set X, IsConnected S → (S ∩ A).Nonempty → (S ∩ B).Nonempty → False) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ B ⊆ Cᶜ := by
  have hdisj : Disjoint ((ConnectedComponents.mk) '' A) ((ConnectedComponents.mk) '' B) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rcases hxA with ⟨a, haA, hax⟩
    rcases hxB with ⟨b, hbB, hbx⟩
    have hab : connectedComponent a = connectedComponent b := by
      exact (ConnectedComponents.coe_eq_coe).mp (hax.trans hbx.symm)
    have hconn : IsConnected (connectedComponent a) := isConnected_connectedComponent
    have hneA : (connectedComponent a ∩ A).Nonempty := ⟨a, mem_connectedComponent, haA⟩
    have hneB : (connectedComponent a ∩ B).Nonempty := by
      refine ⟨b, ?_, hbB⟩
      rw [hab]
      exact mem_connectedComponent
    exact hAB (connectedComponent a) hconn hneA hneB
  exact
    exists_clopen_separating_closed_sets_of_component_images_disjoint
      hA hB hdisj

noncomputable def oddDownArrowRadiusPhaseCenter (n d : ℕ) : ℝ :=
  Real.pi / ((↑(n + d) + 1) : ℝ)

def oddDownArrowRadiusPhaseWedge (δ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    p.1 ∈ Set.Icc (0 : ℝ) δ ∧
      p.2 ∈ Set.Icc (-p.1) p.1}

noncomputable def oddDownArrowRadiusPhasePoint (n d : ℕ) (p : ℝ × ℝ) : ℂ :=
  (↑p.1 : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + p.2) * I)

noncomputable def oddDownArrowRadiusPhaseValue (n d : ℕ) (p : ℝ × ℝ) : ℂ :=
  padeR n d (oddDownArrowRadiusPhasePoint n d p) *
    exp (-(oddDownArrowRadiusPhasePoint n d p))

noncomputable def oddDownArrowRadiusPhaseIm (n d : ℕ) (p : ℝ × ℝ) : ℝ :=
  Complex.im (oddDownArrowRadiusPhaseValue n d p)

noncomputable def oddDownArrowRadiusPhaseZeroSet (n d : ℕ) (δ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    p ∈ oddDownArrowRadiusPhaseWedge δ ∧
      oddDownArrowRadiusPhaseIm n d p = 0}

private theorem isClosed_oddDownArrowRadiusPhaseWedge (δ : ℝ) :
    IsClosed (oddDownArrowRadiusPhaseWedge δ) := by
  have hfst : IsClosed {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) δ} :=
    isClosed_Icc.preimage continuous_fst
  have hleft : IsClosed {p : ℝ × ℝ | -p.1 ≤ p.2} :=
    isClosed_le (continuous_fst.neg) continuous_snd
  have hright : IsClosed {p : ℝ × ℝ | p.2 ≤ p.1} :=
    isClosed_le continuous_snd continuous_fst
  have hphase : IsClosed {p : ℝ × ℝ | -p.1 ≤ p.2 ∧ p.2 ≤ p.1} := hleft.inter hright
  have hwedge :
      oddDownArrowRadiusPhaseWedge δ =
        {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) δ} ∩
          {p : ℝ × ℝ | -p.1 ≤ p.2 ∧ p.2 ≤ p.1} := by
    ext p
    simp [oddDownArrowRadiusPhaseWedge, Set.mem_Icc, and_left_comm, and_assoc, and_comm]
  rw [hwedge]
  exact hfst.inter hphase

private theorem isCompact_oddDownArrowRadiusPhaseWedge {δ : ℝ} :
    IsCompact (oddDownArrowRadiusPhaseWedge δ) := by
  let box : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (-δ) δ
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  refine hbox.of_isClosed_subset (isClosed_oddDownArrowRadiusPhaseWedge δ) ?_
  intro p hp
  rcases hp with ⟨hp1, hp2⟩
  rcases hp2 with ⟨hp2l, hp2r⟩
  refine ⟨hp1, ?_⟩
  refine ⟨?_, ?_⟩
  · have hneg : -δ ≤ -p.1 := by linarith [hp1.2]
    exact le_trans hneg hp2l
  · exact le_trans hp2r hp1.2

private theorem norm_oddDownArrowRadiusPhasePoint
    (n d : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    ‖oddDownArrowRadiusPhasePoint n d p‖ = p.1 := by
  simpa [oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter] using
    norm_ofReal_mul_exp_I p.1 (oddDownArrowRadiusPhaseCenter n d + p.2) hp

private theorem continuousOn_oddDownArrowRadiusPhaseValue
    (n d : ℕ) {δ δQ : ℝ}
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) :
    ContinuousOn (oddDownArrowRadiusPhaseValue n d) (oddDownArrowRadiusPhaseWedge δ) := by
  have hpoint : Continuous (oddDownArrowRadiusPhasePoint n d) := by
    change Continuous (fun p : ℝ × ℝ =>
      (↑p.1 : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + p.2) * I))
    continuity
  have hp : Continuous (padeP n d) := by
    unfold padeP
    fun_prop
  have hq : Continuous (padeQ n d) := padeQ_continuous n d
  have hR :
      ContinuousOn (fun p : ℝ × ℝ => padeR n d (oddDownArrowRadiusPhasePoint n d p))
        (oddDownArrowRadiusPhaseWedge δ) := by
    have hq_ne :
        ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
          padeQ n d (oddDownArrowRadiusPhasePoint n d p) ≠ 0 := by
      intro p hpw
      apply hδQ
      have hp1_nonneg : 0 ≤ p.1 := hpw.1.1
      have hp1_le : p.1 ≤ δ := hpw.1.2
      have hnorm : ‖oddDownArrowRadiusPhasePoint n d p‖ = p.1 :=
        norm_oddDownArrowRadiusPhasePoint n d hp1_nonneg
      have hp1_lt : p.1 < δQ := lt_of_le_of_lt hp1_le hδltQ
      simpa [hnorm] using hp1_lt
    simpa [oddDownArrowRadiusPhaseValue, padeR] using
      (hp.comp hpoint).continuousOn.div (hq.comp hpoint).continuousOn hq_ne
  have hexp : Continuous (fun p : ℝ × ℝ => exp (-(oddDownArrowRadiusPhasePoint n d p))) := by
    fun_prop
  simpa [oddDownArrowRadiusPhaseValue] using hR.mul hexp.continuousOn

private theorem continuousOn_oddDownArrowRadiusPhaseIm
    (n d : ℕ) {δ δQ : ℝ}
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) :
    ContinuousOn (oddDownArrowRadiusPhaseIm n d) (oddDownArrowRadiusPhaseWedge δ) := by
  unfold oddDownArrowRadiusPhaseIm
  intro p hp
  have hcomp :
      ContinuousWithinAt
        ((fun z : ℂ => Complex.im z) ∘ oddDownArrowRadiusPhaseValue n d)
        (oddDownArrowRadiusPhaseWedge δ) p :=
    ContinuousWithinAt.comp (t := Set.univ)
      Complex.continuous_im.continuousAt.continuousWithinAt
      (continuousOn_oddDownArrowRadiusPhaseValue n d hδQ hδltQ p hp) (by
        intro q hq
        simp)
  simpa [Function.comp] using hcomp

theorem isCompact_oddDownArrowRadiusPhaseZeroSet
    (n d : ℕ) {δ δQ : ℝ}
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) :
    IsCompact (oddDownArrowRadiusPhaseZeroSet n d δ) := by
  have hwedge : IsCompact (oddDownArrowRadiusPhaseWedge δ) :=
    isCompact_oddDownArrowRadiusPhaseWedge
  have hzero_closed : IsClosed (oddDownArrowRadiusPhaseZeroSet n d δ) := by
    simpa [oddDownArrowRadiusPhaseZeroSet] using
      (continuousOn_oddDownArrowRadiusPhaseIm n d hδQ hδltQ).preimage_isClosed_of_isClosed
        (isClosed_oddDownArrowRadiusPhaseWedge δ) isClosed_singleton
  exact hwedge.of_isClosed_subset hzero_closed (by
    intro p hp
    exact hp.1)

theorem mem_oddDownArrowRadiusPhaseZeroSet_zero
    (n d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (0, 0) ∈ oddDownArrowRadiusPhaseZeroSet n d δ := by
  refine ⟨?_, ?_⟩
  · exact ⟨⟨le_rfl, hδ⟩, by simp⟩
  · simp [oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
      oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter, padeR,
      padeP_eval_zero, padeQ_eval_zero]

private theorem isCompact_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet
    (n d : ℕ) {δ δQ : ℝ} (hδ : 0 ≤ δ)
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) :
    IsCompact
      (Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)) := by
  let K := oddDownArrowRadiusPhaseZeroSet n d δ
  have hK : IsCompact K := isCompact_oddDownArrowRadiusPhaseZeroSet n d hδQ hδltQ
  have hzero : (0, 0) ∈ K := mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ
  haveI : CompactSpace K := (isCompact_iff_compactSpace.mp hK)
  have hconn_sub : IsCompact (connectedComponent (⟨(0, 0), hzero⟩ : K)) :=
    isClosed_connectedComponent.isCompact
  have hconnIn : IsCompact (connectedComponentIn K (0, 0)) := by
    simpa [K, connectedComponentIn_eq_image hzero] using
      hconn_sub.image continuous_subtype_val
  simpa using hconnIn.image continuous_fst

theorem isClosed_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet
    (n d : ℕ) {δ δQ : ℝ} (hδ : 0 ≤ δ)
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) :
    IsClosed
      (Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)) :=
  (isCompact_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet
    n d hδ hδQ hδltQ).isClosed

theorem oddDownArrowRadiusPhaseRe_pos_on_wedge_of_small_norm
    (n d : ℕ) {δ δre : ℝ}
    (hre_small : ∀ z : ℂ, ‖z‖ < δre →
      0 < Complex.re (padeR n d z * exp (-z)))
    (hδlt : δ < δre) :
    ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
      0 < Complex.re (oddDownArrowRadiusPhaseValue n d p) := by
  intro p hpw
  apply hre_small
  have hp1_nonneg : 0 ≤ p.1 := hpw.1.1
  have hp1_le : p.1 ≤ δ := hpw.1.2
  have hnorm : ‖oddDownArrowRadiusPhasePoint n d p‖ = p.1 :=
    norm_oddDownArrowRadiusPhasePoint n d hp1_nonneg
  have hp1_lt : p.1 < δre := lt_of_le_of_lt hp1_le hδlt
  simpa [oddDownArrowRadiusPhaseValue, hnorm] using hp1_lt

private theorem mem_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet_of_connected_subset
    (n d : ℕ) {δ : ℝ} {S : Set (ℝ × ℝ)}
    (hSconn : IsConnected S)
    (hSsub : S ⊆ oddDownArrowRadiusPhaseZeroSet n d δ)
    (hzeroS : (0, 0) ∈ S)
    {p : ℝ × ℝ} (hpS : p ∈ S) :
    p.1 ∈ Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0) := by
  have hScomp :
      S ⊆ connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0) :=
    hSconn.2.subset_connectedComponentIn hzeroS hSsub
  exact ⟨p, hScomp hpS, rfl⟩

theorem exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet
    (n d : ℕ) {δ δQ : ℝ} (hδ : 0 ≤ δ)
    (hδQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hδltQ : δ < δQ) {r : ℝ}
    (hrmiss :
      r ∉ Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)) :
    ∃ C : Set {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ},
      IsClopen C ∧
        ({⟨(0, 0), mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ⟩} :
          Set {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ}) ⊆ C ∧
        ({p : {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ} | p.1.1 = r}) ⊆ Cᶜ := by
  let K : Set (ℝ × ℝ) := oddDownArrowRadiusPhaseZeroSet n d δ
  let X := {p // p ∈ K}
  have hcompact : IsCompact K := isCompact_oddDownArrowRadiusPhaseZeroSet n d hδQ hδltQ
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hcompact
  let x0 : X := ⟨(0, 0), mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ⟩
  let A : Set X := {x0}
  let B : Set X := {p : X | p.1.1 = r}
  have hA : IsClosed A := isClosed_singleton
  have hB : IsClosed B := by
    have hcont : Continuous fun p : X => p.1.1 :=
      continuous_fst.comp continuous_subtype_val
    simpa [B] using isClosed_singleton.preimage hcont
  have hAB :
      ∀ S : Set X, IsConnected S → (S ∩ A).Nonempty → (S ∩ B).Nonempty → False := by
    intro S hSconn hSA hSB
    rcases hSA with ⟨a, haS, haA⟩
    rcases Set.mem_singleton_iff.mp haA with rfl
    rcases hSB with ⟨b, hbS, hbB⟩
    let T : Set (ℝ × ℝ) := Subtype.val '' S
    have hTconn : IsConnected T := by
      simpa [T] using hSconn.image (fun p : X => (p : ℝ × ℝ)) continuous_subtype_val.continuousOn
    have hTsub : T ⊆ K := by
      intro p hp
      rcases hp with ⟨q, hqS, rfl⟩
      exact q.2
    have hTzero : (0, 0) ∈ T := by
      exact ⟨x0, haS, rfl⟩
    have hbT : (b : ℝ × ℝ) ∈ T := ⟨b, hbS, rfl⟩
    have hbmem :
        b.1.1 ∈ Prod.fst '' connectedComponentIn K (0, 0) := by
      simpa [K] using
        mem_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet_of_connected_subset
          n d hTconn hTsub hTzero hbT
    have hrmem :
        r ∈ Prod.fst '' connectedComponentIn K (0, 0) := by
      rcases hbmem with ⟨q, hqK, hqfst⟩
      refine ⟨q, hqK, ?_⟩
      exact hqfst.trans hbB
    exact hrmiss hrmem
  simpa [A, B] using exists_clopen_of_no_connected_subset_meeting_both hA hB hAB

private theorem exp_neg_sub_linear_factorization :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      exp (-z) - (1 - z) = z ^ 2 * h z := by
  obtain ⟨h, hh⟩ := expTaylor_exp_neg_leading_term 0
  refine ⟨h, ?_⟩
  intro z
  simpa [expTaylor, Finset.range_one] using hh z

private theorem padeQ_sub_linear_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeQ n d z - (1 - ((d : ℂ) / (n + d : ℂ)) * z) = z ^ 2 * h z := by
  let m : ℕ := n + d
  let lin : Polynomial ℂ := 1 - Polynomial.C ((d : ℂ) / (m : ℂ)) * Polynomial.X
  let r : Polynomial ℂ :=
    PadeAsymptotics.padeQ_poly n d -
      lin
  have hm_ne : (m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have h0 : r.coeff 0 = 0 := by
    rw [show r.coeff 0 =
        (PadeAsymptotics.padeQ_poly n d).coeff 0 - lin.coeff 0 by
          simp [r, Polynomial.coeff_sub]]
    have hratio : ((((m).factorial : ℕ) : ℂ) / ((m.factorial : ℂ))) = 1 := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne']
    simp [lin, PadeAsymptotics.padeQ_poly_coeff, m, hratio]
  have h1 : r.coeff 1 = 0 := by
    have hm_fact :
        (((m - 1).factorial : ℕ) : ℂ) / ((m.factorial : ℂ)) = 1 / (m : ℂ) := by
      have hstep : (((m).factorial : ℕ) : ℂ) =
          (m : ℂ) * (((m - 1).factorial : ℕ) : ℂ) := by
        rw [show m = (m - 1) + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      rw [hstep]
      field_simp [hm_ne, Nat.cast_ne_zero.mpr (Nat.factorial_pos (m - 1)).ne']
    have hq1 : (PadeAsymptotics.padeQ_poly n d).coeff 1 = -((d : ℂ) / (m : ℂ)) := by
      rw [PadeAsymptotics.padeQ_poly_coeff]
      simp [m, hm_fact, Nat.choose_one_right]
      ring
    rw [show r.coeff 1 =
        (PadeAsymptotics.padeQ_poly n d).coeff 1 - lin.coeff 1 by
          simp [r, Polynomial.coeff_sub], hq1]
    have hconst : ((1 : Polynomial ℂ).coeff 1 : ℂ) = 0 := by
      simpa using (Polynomial.coeff_one (R := ℂ) (n := 1))
    simp [lin, hconst]
  have hX2 : Polynomial.X ^ 2 ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · exact h0
    · exact h1
  obtain ⟨g, hg⟩ := hX2
  refine ⟨fun z => g.eval z, ?_⟩
  intro z
  have hlin_eval : lin.eval z = 1 - ((d : ℂ) / (m : ℂ)) * z := by
    simp [lin]
  have hEval := congrArg (fun p : Polynomial ℂ => p.eval z) hg
  simpa [r, m, lin, hlin_eval, PadeAsymptotics.padeQ_poly_eval, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    using hEval

private theorem padeQ_inv_linear_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ, padeQ n d z ≠ 0 →
      (padeQ n d z)⁻¹ - (1 + ((d : ℂ) / (n + d : ℂ)) * z) = z ^ 2 * h z := by
  obtain ⟨k, hk⟩ := padeQ_sub_linear_factorization n d hm
  let α : ℂ := (d : ℂ) / (n + d : ℂ)
  refine ⟨fun z =>
    if hq : padeQ n d z = 0 then 0
    else ((-(α * z * k z) + (α ^ 2 - k z)) / padeQ n d z), ?_⟩
  intro z hq
  have hkz : padeQ n d z = 1 - α * z + z ^ 2 * k z := by
    have hkz' : padeQ n d z = z ^ 2 * k z + (1 - α * z) := by
      exact sub_eq_iff_eq_add.mp (by simpa [α] using hk z)
    simpa [add_assoc, add_comm, add_left_comm] using hkz'
  simp [hq, α]
  calc
    (padeQ n d z)⁻¹ - (1 + ↑d / (↑n + ↑d) * z)
        = ((1 : ℂ) - (1 + ↑d / (↑n + ↑d) * z) * padeQ n d z) / padeQ n d z := by
            field_simp [hq]
    _ = (-z ^ 2 * (k z - (↑d / (↑n + ↑d)) ^ 2 + (↑d / (↑n + ↑d)) * z * k z)) /
          padeQ n d z := by
            rw [hkz]
            ring
    _ = z ^ 2 * (((-(↑d / (↑n + ↑d) * z * k z) + (((↑d / (↑n + ↑d)) ^ 2 - k z))) /
          padeQ n d z)) := by
            field_simp [hq]
            ring

private theorem exp_neg_div_padeQ_linear_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ, padeQ n d z ≠ 0 →
      exp (-z) / padeQ n d z - (1 - ((n : ℂ) / (n + d : ℂ)) * z) = z ^ 2 * h z := by
  obtain ⟨hE, hhE⟩ := exp_neg_sub_linear_factorization
  obtain ⟨hQ, hhQ⟩ := padeQ_inv_linear_factorization n d hm
  let α : ℂ := (d : ℂ) / (n + d : ℂ)
  refine ⟨fun z =>
    if hq : padeQ n d z = 0 then 0
    else hE z * (padeQ n d z)⁻¹ + (1 - z) * hQ z - α, ?_⟩
  intro z hq
  have hE_eq : exp (-z) = 1 - z + z ^ 2 * hE z := by
    have hE_eq' := sub_eq_iff_eq_add.mp (hhE z)
    simpa [add_assoc, add_comm, add_left_comm] using hE_eq'
  have hQ_eq : (padeQ n d z)⁻¹ = 1 + α * z + z ^ 2 * hQ z := by
    have hQ_eq' := sub_eq_iff_eq_add.mp (hhQ z hq)
    simpa [add_assoc, add_comm, add_left_comm] using hQ_eq'
  have hm_ne : ((n + d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hfrac : ((d : ℂ) / (n + d : ℂ)) + ((n : ℂ) / (n + d : ℂ)) = 1 := by
    have hfrac' : (((d : ℂ) + (n : ℂ)) * ((n + d : ℂ))⁻¹) = 1 := by
      have hcast : ((d : ℂ) + (n : ℂ)) = ((n + d : ℕ) : ℂ) := by
        norm_num [Nat.cast_add, add_comm, add_left_comm, add_assoc]
      rw [hcast]
      simpa [hm_ne] using mul_inv_cancel₀ hm_ne
    calc
      ((d : ℂ) / (n + d : ℂ)) + ((n : ℂ) / (n + d : ℂ)) =
          (((d : ℂ) + (n : ℂ)) * ((n + d : ℂ))⁻¹) := by
            ring
      _ = 1 := hfrac'
  have hlin :
      -z + z * ((d : ℂ) / (n + d : ℂ)) + z * ((n : ℂ) / (n + d : ℂ)) = 0 := by
    calc
      -z + z * ((d : ℂ) / (n + d : ℂ)) + z * ((n : ℂ) / (n + d : ℂ)) =
          z * (((d : ℂ) / (n + d : ℂ)) + ((n : ℂ) / (n + d : ℂ)) - 1) := by
            ring
      _ = 0 := by
            rw [hfrac]
            ring
  simp [hq, α, div_eq_mul_inv]
  rw [hE_eq, hQ_eq]
  calc
    (1 - z + z ^ 2 * hE z) * (1 + α * z + z ^ 2 * hQ z) -
        (1 - ((n : ℂ) / (n + d : ℂ)) * z) =
      (-z + z * α + z * ((n : ℂ) / (n + d : ℂ))) +
        (z ^ 2 * hE z - z ^ 2 * α + z ^ 2 * hQ z +
          (z ^ 3 * hE z * α - z ^ 3 * hQ z) +
          z ^ 4 * hE z * hQ z) := by
            ring
    _ = z ^ 2 * hE z - z ^ 2 * α + z ^ 2 * hQ z +
        (z ^ 3 * hE z * α - z ^ 3 * hQ z) +
        z ^ 4 * hE z * hQ z := by
          rw [hlin]
          simp
    _ = z ^ 2 * (hE z * (1 + α * z + z ^ 2 * hQ z) + (1 - z) * hQ z - α) := by
          ring

/-- The explicit degree-`n + d + 2` coefficient in the odd down-arrow local
expansion of `padeR n d z * exp (-z)` around `z = 0`. -/
noncomputable def padeRExpNegSecondCoeff (n d : ℕ) : ℝ :=
  padePhiErrorConst n d *
    (((n : ℝ) - d) * (((n + d : ℕ) : ℝ) + 1)) /
      ((((n + d : ℕ) : ℝ)) * (((n + d : ℕ) : ℝ) + 2))

/-- The exact degree-`n + d + 2` coefficient of the Padé defect after the
leading degree-`n + d + 1` term is removed. -/
private noncomputable def padeDefectSecondCoeff (n d : ℕ) : ℂ :=
  (1 / (((n + d + 2).factorial : ℂ))) -
    ((d : ℂ) / (n + d : ℂ)) / (((n + d + 1).factorial : ℂ)) -
    (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (n + d + 2 : ℂ))

/-- The exact degree-`m + 2` coefficient in
`expTaylor m z * exp (-z)`. -/
private noncomputable def expTaylorExpNegSecondCoeff (m : ℕ) : ℂ :=
  ((m + 1 : ℂ) / (((m + 2).factorial : ℂ)))

/-- Second-order Padé-defect factorization local to the odd down-arrow seam. -/
private theorem padeDefect_sub_second_factorization
    (n d : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeP n d z - padeQ n d z * expTaylor (n + d) z -
          ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            z ^ (n + d + 1) -
          padeDefectSecondCoeff n d * z ^ (n + d + 2) =
        z ^ (n + d + 3) * h z := by
  let r : Polynomial ℂ :=
    PadeAsymptotics.padeDefect_poly n d -
      Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
        Polynomial.X ^ (n + d + 1) -
      Polynomial.C (padeDefectSecondCoeff n d) * Polynomial.X ^ (n + d + 2)
  have hX : Polynomial.X ^ (n + d + 3) ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    by_cases hlt : k < n + d + 1
    · rw [show r.coeff k =
          (PadeAsymptotics.padeDefect_poly n d).coeff k -
            (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                (padePhiErrorConst n d : ℂ)) *
              Polynomial.X ^ (n + d + 1)).coeff k -
            (Polynomial.C (padeDefectSecondCoeff n d) *
              Polynomial.X ^ (n + d + 2)).coeff k by
            simp [r, Polynomial.coeff_sub]]
      rw [PadeAsymptotics.padeDefect_poly_coeff_lt _ _ _ hlt,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
      have hk1 : k ≠ n + d + 1 := Nat.ne_of_lt hlt
      have hk2 : k ≠ n + d + 2 := by omega
      simp [hk1, hk2]
    · have hk_cases : k = n + d + 1 ∨ k = n + d + 2 := by omega
      rcases hk_cases with rfl | rfl
      · rw [show r.coeff (n + d + 1) =
            (PadeAsymptotics.padeDefect_poly n d).coeff (n + d + 1) -
              (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                  (padePhiErrorConst n d : ℂ)) *
                Polynomial.X ^ (n + d + 1)).coeff (n + d + 1) -
              (Polynomial.C (padeDefectSecondCoeff n d) *
                Polynomial.X ^ (n + d + 2)).coeff (n + d + 1) by
              simp [r, Polynomial.coeff_sub]]
        rw [PadeAsymptotics.padeDefect_poly_coeff_succ,
          Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
        simp
      · rw [show r.coeff (n + d + 2) =
            (PadeAsymptotics.padeDefect_poly n d).coeff (n + d + 2) -
              (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                  (padePhiErrorConst n d : ℂ)) *
                Polynomial.X ^ (n + d + 1)).coeff (n + d + 2) -
              (Polynomial.C (padeDefectSecondCoeff n d) *
                Polynomial.X ^ (n + d + 2)).coeff (n + d + 2) by
              simp [r, Polynomial.coeff_sub]]
        rw [PadeAsymptotics.padeDefect_poly_coeff_succ_succ,
          Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
        simp [padeDefectSecondCoeff]
  obtain ⟨g, hg⟩ := hX
  refine ⟨fun z => g.eval z, ?_⟩
  intro z
  have hEval := congrArg (fun p : Polynomial ℂ => p.eval z) hg
  simpa [r, PadeAsymptotics.padeDefect_poly, PadeAsymptotics.padeP_poly_eval,
    PadeAsymptotics.padeQ_poly_eval, PadeAsymptotics.expTaylor_poly_eval,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, padeDefectSecondCoeff] using hEval

/-- Second-order truncated-exponential factorization at the origin. -/
private theorem expTaylor_exp_neg_second_order_factorization
    (m : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      expTaylor m z * exp (-z) -
          (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
            expTaylorExpNegSecondCoeff m * z ^ (m + 2)) =
        z ^ (m + 3) * h z := by
  obtain ⟨hNext, hhNext⟩ := expTaylor_exp_neg_leading_term (m + 1)
  obtain ⟨hExp, hhExp⟩ :
      ∃ h : ℂ → ℂ, ∀ z : ℂ, exp (-z) - (1 - z) = z ^ 2 * h z := by
    obtain ⟨h, hh⟩ := expTaylor_exp_neg_leading_term 0
    refine ⟨h, ?_⟩
    intro z
    simpa [expTaylor, Finset.range_one] using hh z
  let a : ℂ := (1 : ℂ) / (((m + 2).factorial : ℂ))
  have hcoeff :
      (1 / (((m + 1).factorial : ℂ))) - a =
        expTaylorExpNegSecondCoeff m := by
    dsimp [a]
    have hfact : (((m + 2).factorial : ℕ) : ℂ) =
        (m + 2 : ℂ) * (((m + 1).factorial : ℕ) : ℂ) := by
      rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [show expTaylorExpNegSecondCoeff m = ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) by rfl]
    rw [hfact]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (m + 1)).ne',
      Nat.cast_ne_zero.mpr (show m + 2 ≠ 0 by omega)]
    calc
      (1 : ℂ) - 1 / (m + 2 : ℂ) =
          ((m + 2 : ℂ) / (m + 2 : ℂ)) - 1 / (m + 2 : ℂ) := by
            field_simp [show (m + 2 : ℂ) ≠ 0 by
              exact_mod_cast (show m + 2 ≠ 0 by omega)]
      _ = ((m + 1 : ℂ) / (m + 2 : ℂ)) := by
            ring
  refine ⟨fun z => hNext z - ((1 : ℂ) / (((m + 1).factorial : ℂ))) * hExp z, ?_⟩
  intro z
  have hsplit :
      expTaylor (m + 1) z =
        expTaylor m z + z ^ (m + 1) / (((m + 1).factorial : ℂ)) := by
    unfold expTaylor
    rw [Finset.sum_range_succ]
  have hNext_eq :
      expTaylor (m + 1) z * exp (-z) =
        1 - a * z ^ (m + 2) + z ^ (m + 3) * hNext z := by
    have hNext_eq' := sub_eq_iff_eq_add.mp (hhNext z)
    simpa [a, add_assoc, add_comm, add_left_comm] using hNext_eq'
  have hExp_eq : exp (-z) = 1 - z + z ^ 2 * hExp z := by
    have hExp_eq' := sub_eq_iff_eq_add.mp (hhExp z)
    simpa [add_assoc, add_comm, add_left_comm] using hExp_eq'
  calc
    expTaylor m z * exp (-z) -
        (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
          expTaylorExpNegSecondCoeff m * z ^ (m + 2)) =
      (expTaylor (m + 1) z * exp (-z) -
          (z ^ (m + 1) / (((m + 1).factorial : ℂ))) * exp (-z)) -
        (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
          expTaylorExpNegSecondCoeff m * z ^ (m + 2)) := by
            rw [hsplit]
            ring
    _ = (1 - a * z ^ (m + 2) + z ^ (m + 3) * hNext z -
          (z ^ (m + 1) / (((m + 1).factorial : ℂ))) *
            (1 - z + z ^ 2 * hExp z)) -
        (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
          expTaylorExpNegSecondCoeff m * z ^ (m + 2)) := by
            rw [hNext_eq, hExp_eq]
    _ = z ^ (m + 3) * (hNext z - ((1 : ℂ) / (((m + 1).factorial : ℂ))) * hExp z) := by
          rw [← hcoeff]
          ring

/-- The explicit degree-`n + d + 2` coefficient in the odd down-arrow seam
comes from combining the truncated-exponential second coefficient with the
Padé-defect second coefficient and the linear denominator correction. -/
private theorem padeR_exp_neg_second_coeff_identity
    (n d : ℕ) (hm : 0 < n + d) :
    expTaylorExpNegSecondCoeff (n + d) +
        padeDefectSecondCoeff n d -
        (((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
          ((n : ℂ) / (n + d : ℂ))) =
      (padeRExpNegSecondCoeff n d : ℂ) := by
  let m : ℕ := n + d
  have hm_pos : 0 < m := by simpa [m] using hm
  have hm_ne : (m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm_pos)
  have hm2_ne_nat : m + 2 ≠ 0 := by omega
  have hm2_ne : (m + 2 : ℂ) ≠ 0 := by
    exact_mod_cast hm2_ne_nat
  have hfact :
      (((m + 2).factorial : ℕ) : ℂ) =
        (m + 2 : ℂ) * (((m + 1).factorial : ℕ) : ℂ) := by
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hfactorial_cancel :
      ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) +
          (1 / (((m + 2).factorial : ℂ))) =
        (1 / (((m + 1).factorial : ℂ))) := by
    rw [hfact]
    field_simp [hm2_ne,
      Nat.cast_ne_zero.mpr (Nat.factorial_pos (m + 1)).ne']
    ring
  have hcoeff :
      (1 / (((m + 1).factorial : ℂ))) -
          ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
          (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ)) -
          (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (m : ℂ))) =
        (padePhiErrorConst n d : ℂ) *
          ((((n : ℂ) - d) * (m + 1 : ℂ)) / ((m : ℂ) * (m + 2 : ℂ))) := by
    dsimp [m]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (n + d + 1)).ne',
      show ((n + d : ℂ)) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm),
      show ((n + d + 2 : ℂ)) ≠ 0 by
        exact_mod_cast (show n + d + 2 ≠ 0 by omega)]
    push_cast
    ring
  have hstart :
      expTaylorExpNegSecondCoeff (n + d) +
          padeDefectSecondCoeff n d -
          (((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (n + d : ℂ))) =
        ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) +
          ((1 / (((m + 2).factorial : ℂ))) -
            ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
            (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ))) -
          (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (m : ℂ))) := by
    simp [m, padeDefectSecondCoeff, expTaylorExpNegSecondCoeff]
  calc
    expTaylorExpNegSecondCoeff (n + d) +
          padeDefectSecondCoeff n d -
          (((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (n + d : ℂ))) =
        ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) +
          ((1 / (((m + 2).factorial : ℂ))) -
            ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
            (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ))) -
          (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (m : ℂ))) := hstart
    _ = (1 / (((m + 1).factorial : ℂ))) -
          ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
          (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ)) -
          (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            ((n : ℂ) / (m : ℂ))) := by
          calc
            ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) +
                ((1 / (((m + 2).factorial : ℂ))) -
                  ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
                  (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ))) -
                (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
                  ((n : ℂ) / (m : ℂ))) =
              (((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) +
                  (1 / (((m + 2).factorial : ℂ)))) -
                ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
                (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ)) -
                (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
                  ((n : ℂ) / (m : ℂ))) := by ring
            _ = (1 / (((m + 1).factorial : ℂ))) -
                ((d : ℂ) / (m : ℂ)) / (((m + 1).factorial : ℂ)) -
                (padePhiErrorConst n d : ℂ) * ((d + 1 : ℂ) / (m + 2 : ℂ)) -
                (((1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
                  ((n : ℂ) / (m : ℂ))) := by rw [hfactorial_cancel]
    _ =
        (padePhiErrorConst n d : ℂ) *
          ((((n : ℂ) - d) * (m + 1 : ℂ)) / ((m : ℂ) * (m + 2 : ℂ))) := hcoeff
    _ = (padeRExpNegSecondCoeff n d : ℂ) := by
        simp [m, padeRExpNegSecondCoeff]
        ring

/-- Cycle-345 analytic seam: one order beyond `padeR_exp_neg_leading_term`, with
the explicit degree-`n + d + 2` coefficient isolated. This is kept local to the
odd down-arrow continuation argument. -/
private theorem padeR_exp_neg_second_order_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
          (1
            - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)
            + (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2)) =
        z ^ (n + d + 3) * h z := by
  let m : ℕ := n + d
  let a : ℂ := (1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)
  let b : ℂ := padeDefectSecondCoeff n d
  let c : ℂ := expTaylorExpNegSecondCoeff m
  obtain ⟨hD, hhD⟩ := padeDefect_sub_second_factorization n d
  obtain ⟨hE, hhE⟩ := expTaylor_exp_neg_second_order_factorization m
  obtain ⟨hQ, hhQ⟩ := exp_neg_div_padeQ_linear_factorization n d hm
  have hcoeff :
      c + b - a * ((n : ℂ) / (n + d : ℂ)) = (padeRExpNegSecondCoeff n d : ℂ) := by
    simpa [m, a, b, c] using padeR_exp_neg_second_coeff_identity n d hm
  refine ⟨fun z =>
    if hz : z = 0 then 0 else
    if hq : padeQ n d z = 0 then
      (padeR n d z * exp (-z) -
          (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2))) /
        z ^ (n + d + 3)
    else
      hE z +
        a * hQ z +
        (-b * ((n : ℂ) / (n + d : ℂ))) +
        z * b * hQ z +
        hD z * (exp (-z) / padeQ n d z), ?_⟩
  intro z
  by_cases hz : z = 0
  · subst hz
    simp [padeRExpNegSecondCoeff, padeR, padeP_eval_zero, padeQ_eval_zero]
  · by_cases hq : padeQ n d z = 0
    · have hzpow : z ^ (n + d + 3) ≠ 0 := by
        exact pow_ne_zero _ hz
      simp [hz, hq]
      field_simp [hzpow]
    · have hsplit :
          padeR n d z * exp (-z) =
            expTaylor m z * exp (-z) +
              (padeP n d z - padeQ n d z * expTaylor m z) *
                (exp (-z) / padeQ n d z) := by
        rw [padeR]
        field_simp [hq]
        simp [m]
      simp [hz, hq]
      have hD_eq :
          padeP n d z - padeQ n d z * expTaylor m z =
            a * z ^ (n + d + 1) +
              b * z ^ (n + d + 2) +
              z ^ (n + d + 3) * hD z := by
        have hD_eq' := sub_eq_iff_eq_add.mp (hhD z)
        have hD_eq'' := sub_eq_iff_eq_add.mp hD_eq'
        simpa [m, a, b, add_assoc, add_comm, add_left_comm] using hD_eq''
      have hE_eq :
          expTaylor m z * exp (-z) =
            1 - (1 : ℂ) / (((n + d + 1).factorial : ℂ)) * z ^ (n + d + 1) +
              c * z ^ (n + d + 2) +
              z ^ (n + d + 3) * hE z := by
        have hE_eq' := sub_eq_iff_eq_add.mp (hhE z)
        simpa [m, c, add_assoc, add_comm, add_left_comm] using hE_eq'
      have hQ_eq :
          exp (-z) / padeQ n d z =
            1 - ((n : ℂ) / (n + d : ℂ)) * z + z ^ 2 * hQ z := by
        have hQ_eq' := sub_eq_iff_eq_add.mp (hhQ z hq)
        simpa [add_assoc, add_comm, add_left_comm] using hQ_eq'
      have hcoeffz :
          z ^ (n + d + 2) * (c + b - a * ((n : ℂ) / (n + d : ℂ))) =
            z ^ (n + d + 2) * (padeRExpNegSecondCoeff n d : ℂ) := by
        rw [hcoeff]
      rw [hsplit, hD_eq, hE_eq, hQ_eq]
      field_simp [hq]
      rw [← hcoeffz]
      ring

private theorem padeDefect_sub_second_local_bound
    (n d : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖padeP n d z - padeQ n d z * expTaylor (n + d) z -
            ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
              z ^ (n + d + 1) -
            padeDefectSecondCoeff n d * z ^ (n + d + 2)‖ ≤
          K * ‖z‖ ^ (n + d + 3) := by
  let r : Polynomial ℂ :=
    PadeAsymptotics.padeDefect_poly n d -
      Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
        Polynomial.X ^ (n + d + 1) -
      Polynomial.C (padeDefectSecondCoeff n d) * Polynomial.X ^ (n + d + 2)
  have hX : Polynomial.X ^ (n + d + 3) ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    by_cases hlt : k < n + d + 1
    · rw [show r.coeff k =
          (PadeAsymptotics.padeDefect_poly n d).coeff k -
            (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                (padePhiErrorConst n d : ℂ)) *
              Polynomial.X ^ (n + d + 1)).coeff k -
            (Polynomial.C (padeDefectSecondCoeff n d) *
              Polynomial.X ^ (n + d + 2)).coeff k by
            simp [r, Polynomial.coeff_sub]]
      rw [PadeAsymptotics.padeDefect_poly_coeff_lt _ _ _ hlt,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
      have hk1 : k ≠ n + d + 1 := Nat.ne_of_lt hlt
      have hk2 : k ≠ n + d + 2 := by omega
      simp [hk1, hk2]
    · have hk_cases : k = n + d + 1 ∨ k = n + d + 2 := by omega
      rcases hk_cases with rfl | rfl
      · rw [show r.coeff (n + d + 1) =
            (PadeAsymptotics.padeDefect_poly n d).coeff (n + d + 1) -
              (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                  (padePhiErrorConst n d : ℂ)) *
                Polynomial.X ^ (n + d + 1)).coeff (n + d + 1) -
              (Polynomial.C (padeDefectSecondCoeff n d) *
                Polynomial.X ^ (n + d + 2)).coeff (n + d + 1) by
              simp [r, Polynomial.coeff_sub]]
        rw [PadeAsymptotics.padeDefect_poly_coeff_succ,
          Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
        simp
      · rw [show r.coeff (n + d + 2) =
            (PadeAsymptotics.padeDefect_poly n d).coeff (n + d + 2) -
              (Polynomial.C ((1 / (((n + d + 1).factorial : ℂ))) -
                  (padePhiErrorConst n d : ℂ)) *
                Polynomial.X ^ (n + d + 1)).coeff (n + d + 2) -
              (Polynomial.C (padeDefectSecondCoeff n d) *
                Polynomial.X ^ (n + d + 2)).coeff (n + d + 2) by
              simp [r, Polynomial.coeff_sub]]
        rw [PadeAsymptotics.padeDefect_poly_coeff_succ_succ,
          Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
        simp [padeDefectSecondCoeff]
  obtain ⟨g, hg⟩ := hX
  obtain ⟨B, hB⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
      (g.continuous.continuousOn)
  refine ⟨max B 1, by positivity, ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz
  have hgbound : ‖g.eval z‖ ≤ max B 1 := by
    exact le_trans (hB z hzmem) (le_max_left _ _)
  have hEval := congrArg (fun p : Polynomial ℂ => p.eval z) hg
  have hEq :
      padeP n d z - padeQ n d z * expTaylor (n + d) z -
          ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
            z ^ (n + d + 1) -
          padeDefectSecondCoeff n d * z ^ (n + d + 2) =
        z ^ (n + d + 3) * g.eval z := by
    simpa [r, PadeAsymptotics.padeDefect_poly, PadeAsymptotics.padeP_poly_eval,
      PadeAsymptotics.padeQ_poly_eval, PadeAsymptotics.expTaylor_poly_eval,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, padeDefectSecondCoeff] using hEval
  rw [hEq, norm_mul, norm_pow]
  calc
    ‖z‖ ^ (n + d + 3) * ‖g.eval z‖ ≤ ‖z‖ ^ (n + d + 3) * max B 1 := by
      exact mul_le_mul_of_nonneg_left hgbound (pow_nonneg (norm_nonneg z) _)
    _ = max B 1 * ‖z‖ ^ (n + d + 3) := by ring

private theorem expTaylor_exp_neg_second_local_norm_bound
    (m : ℕ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖expTaylor m z * exp (-z) -
            (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
              expTaylorExpNegSecondCoeff m * z ^ (m + 2))‖ ≤
          K * ‖z‖ ^ (m + 3) := by
  obtain ⟨δNext, KNext, hδNext, hKNext, hNext⟩ := expTaylor_exp_neg_local_norm_bound (m + 1)
  obtain ⟨δLin, KLin, hδLin, hKLin, hLin⟩ := expTaylor_exp_neg_local_norm_bound 0
  let δ : ℝ := min 1 (min δNext δLin)
  let Kbase : ℝ := KNext + ((1 : ℝ) / ((m + 1).factorial : ℝ)) * KLin
  have hcoeff :
      (1 / (((m + 1).factorial : ℂ))) - (1 / (((m + 2).factorial : ℂ))) =
        expTaylorExpNegSecondCoeff m := by
    have hfact : (((m + 2).factorial : ℕ) : ℂ) =
        (m + 2 : ℂ) * (((m + 1).factorial : ℕ) : ℂ) := by
      rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [show expTaylorExpNegSecondCoeff m = ((m + 1 : ℂ) / (((m + 2).factorial : ℂ))) by rfl]
    rw [hfact]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (m + 1)).ne',
      Nat.cast_ne_zero.mpr (show m + 2 ≠ 0 by omega)]
    calc
      (1 : ℂ) - 1 / (m + 2 : ℂ) =
          ((m + 2 : ℂ) / (m + 2 : ℂ)) - 1 / (m + 2 : ℂ) := by
            field_simp [show (m + 2 : ℂ) ≠ 0 by
              exact_mod_cast (show m + 2 ≠ 0 by omega)]
      _ = ((m + 1 : ℂ) / (m + 2 : ℂ)) := by ring
  refine ⟨δ, Kbase + 1, lt_min zero_lt_one (lt_min hδNext hδLin), by positivity, ?_⟩
  intro z hz
  have hzNext : ‖z‖ < δNext := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzLin : ‖z‖ < δLin := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hLin' :
      ‖exp (-z) - (1 - z)‖ ≤ KLin * ‖z‖ ^ 2 := by
    simpa [expTaylor, Finset.range_one] using hLin z hzLin
  have hsplit_expTaylor :
      expTaylor (m + 1) z =
        expTaylor m z + z ^ (m + 1) / (((m + 1).factorial : ℂ)) := by
    unfold expTaylor
    rw [Finset.sum_range_succ]
  have hsplit :
      expTaylor m z * exp (-z) -
          (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) +
            expTaylorExpNegSecondCoeff m * z ^ (m + 2)) =
        (expTaylor (m + 1) z * exp (-z) -
            (1 - (1 : ℂ) / (((m + 2).factorial : ℂ)) * z ^ (m + 2))) -
          (z ^ (m + 1) / (((m + 1).factorial : ℂ))) * (exp (-z) - (1 - z)) := by
    rw [hsplit_expTaylor, ← hcoeff]
    ring
  have hterm2 :
      ‖(z ^ (m + 1) / (((m + 1).factorial : ℂ))) * (exp (-z) - (1 - z))‖ ≤
        (((1 : ℝ) / ((m + 1).factorial : ℝ)) * KLin) * ‖z‖ ^ (m + 3) := by
    have hfacnorm : ‖(((m + 1).factorial : ℂ))‖ = ((m + 1).factorial : ℝ) := by
      simp
    calc
      ‖(z ^ (m + 1) / (((m + 1).factorial : ℂ))) * (exp (-z) - (1 - z))‖ =
          ‖z ^ (m + 1) / (((m + 1).factorial : ℂ))‖ * ‖exp (-z) - (1 - z)‖ := by
            rw [norm_mul]
      _ = (‖z‖ ^ (m + 1) / ((m + 1).factorial : ℝ)) * ‖exp (-z) - (1 - z)‖ := by
            rw [norm_div, norm_pow, hfacnorm]
      _ = (((1 : ℝ) / ((m + 1).factorial : ℝ)) * ‖z‖ ^ (m + 1)) * ‖exp (-z) - (1 - z)‖ := by
            field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (m + 1)).ne']
      _ ≤ ((((1 : ℝ) / ((m + 1).factorial : ℝ)) * ‖z‖ ^ (m + 1)) * (KLin * ‖z‖ ^ 2)) := by
            gcongr
      _ = (((1 : ℝ) / ((m + 1).factorial : ℝ)) * KLin) * ‖z‖ ^ (m + 3) := by
            rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
            ring
  rw [hsplit]
  calc
    ‖(expTaylor (m + 1) z * exp (-z) - (1 - (1 : ℂ) / (((m + 2).factorial : ℂ)) * z ^ (m + 2))) -
        (z ^ (m + 1) / (((m + 1).factorial : ℂ))) * (exp (-z) - (1 - z))‖
      ≤ ‖expTaylor (m + 1) z * exp (-z) - (1 - (1 : ℂ) / (((m + 2).factorial : ℂ)) * z ^ (m + 2))‖ +
          ‖(z ^ (m + 1) / (((m + 1).factorial : ℂ))) * (exp (-z) - (1 - z))‖ := by
            exact norm_sub_le _ _
    _ ≤ KNext * ‖z‖ ^ (m + 3) +
          (((1 : ℝ) / ((m + 1).factorial : ℝ)) * KLin) * ‖z‖ ^ (m + 3) := by
            exact add_le_add (hNext z hzNext) hterm2
    _ = Kbase * ‖z‖ ^ (m + 3) := by
          dsimp [Kbase]
          ring
    _ ≤ (Kbase + 1) * ‖z‖ ^ (m + 3) := by
          have hpow : 0 ≤ ‖z‖ ^ (m + 3) := pow_nonneg (norm_nonneg z) _
          nlinarith

private theorem padeQ_sub_linear_local_bound
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖padeQ n d z - (1 - ((d : ℂ) / (n + d : ℂ)) * z)‖ ≤ K * ‖z‖ ^ 2 := by
  let m : ℕ := n + d
  let lin : Polynomial ℂ := 1 - Polynomial.C ((d : ℂ) / (m : ℂ)) * Polynomial.X
  let r : Polynomial ℂ :=
    PadeAsymptotics.padeQ_poly n d - lin
  have hm_ne : (m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have h0 : r.coeff 0 = 0 := by
    rw [show r.coeff 0 =
        (PadeAsymptotics.padeQ_poly n d).coeff 0 - lin.coeff 0 by
          simp [r, Polynomial.coeff_sub]]
    have hratio : ((((m).factorial : ℕ) : ℂ) / ((m.factorial : ℂ))) = 1 := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne']
    simp [lin, PadeAsymptotics.padeQ_poly_coeff, m, hratio]
  have h1 : r.coeff 1 = 0 := by
    have hm_fact :
        (((m - 1).factorial : ℕ) : ℂ) / ((m.factorial : ℂ)) = 1 / (m : ℂ) := by
      have hstep : (((m).factorial : ℕ) : ℂ) =
          (m : ℂ) * (((m - 1).factorial : ℕ) : ℂ) := by
        rw [show m = (m - 1) + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      rw [hstep]
      field_simp [hm_ne, Nat.cast_ne_zero.mpr (Nat.factorial_pos (m - 1)).ne']
    have hq1 : (PadeAsymptotics.padeQ_poly n d).coeff 1 = -((d : ℂ) / (m : ℂ)) := by
      rw [PadeAsymptotics.padeQ_poly_coeff]
      simp [m, hm_fact, Nat.choose_one_right]
      ring
    rw [show r.coeff 1 =
        (PadeAsymptotics.padeQ_poly n d).coeff 1 - lin.coeff 1 by
          simp [r, Polynomial.coeff_sub], hq1]
    have hconst : ((1 : Polynomial ℂ).coeff 1 : ℂ) = 0 := by
      simpa using (Polynomial.coeff_one (R := ℂ) (n := 1))
    simp [lin, hconst]
  have hX2 : Polynomial.X ^ 2 ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · exact h0
    · exact h1
  obtain ⟨g, hg⟩ := hX2
  obtain ⟨B, hB⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
      (g.continuous.continuousOn)
  refine ⟨max B 1, by positivity, ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz
  have hgbound : ‖g.eval z‖ ≤ max B 1 := by
    exact le_trans (hB z hzmem) (le_max_left _ _)
  have hlin_eval : lin.eval z = 1 - ((d : ℂ) / (m : ℂ)) * z := by
    simp [lin]
  have hEval := congrArg (fun p : Polynomial ℂ => p.eval z) hg
  have hEq :
      padeQ n d z - (1 - ((d : ℂ) / (n + d : ℂ)) * z) =
        z ^ 2 * g.eval z := by
    simpa [r, m, lin, hlin_eval, PadeAsymptotics.padeQ_poly_eval, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      using hEval
  rw [hEq, norm_mul, norm_pow]
  calc
    ‖z‖ ^ 2 * ‖g.eval z‖ ≤ ‖z‖ ^ 2 * max B 1 := by
      exact mul_le_mul_of_nonneg_left hgbound (pow_nonneg (norm_nonneg z) _)
    _ = max B 1 * ‖z‖ ^ 2 := by ring

private theorem padeQ_inv_linear_local_norm_bound
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖(padeQ n d z)⁻¹ - (1 + ((d : ℂ) / (n + d : ℂ)) * z)‖ ≤
          K * ‖z‖ ^ 2 := by
  let α : ℂ := (d : ℂ) / (n + d : ℂ)
  obtain ⟨Ksub, hKsub, hsub⟩ := padeQ_sub_linear_local_bound n d hm
  obtain ⟨δinv, hδinv, hinv⟩ := padeQ_inv_bound n d
  obtain ⟨δnz, hδnz, hnz⟩ := padeQ_ne_zero_nhds n d
  let δ : ℝ := min 1 (min δinv δnz)
  let Kbase : ℝ := 2 * (‖α‖ ^ 2 + (1 + ‖α‖) * Ksub)
  refine ⟨δ, Kbase + 1, lt_min zero_lt_one (lt_min hδinv hδnz), by positivity, ?_⟩
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hz (min_le_left _ _))
  have hzinv : ‖z‖ < δinv := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hznz : ‖z‖ < δnz := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hqne : padeQ n d z ≠ 0 := hnz z hznz
  let e : ℂ := padeQ n d z - (1 - α * z)
  have he : ‖e‖ ≤ Ksub * ‖z‖ ^ 2 := by
    simpa [α, e] using hsub z hz1
  have hone : ‖1 + α * z‖ ≤ 1 + ‖α‖ := by
    calc
      ‖1 + α * z‖ ≤ ‖(1 : ℂ)‖ + ‖α * z‖ := norm_add_le _ _
      _ = 1 + ‖α‖ * ‖z‖ := by rw [norm_mul]; simp
      _ ≤ 1 + ‖α‖ * 1 := by
            gcongr
      _ = 1 + ‖α‖ := by ring
  have hnum :
      ‖α ^ 2 * z ^ 2 - (1 + α * z) * e‖ ≤
        (‖α‖ ^ 2 + (1 + ‖α‖) * Ksub) * ‖z‖ ^ 2 := by
    have hterm1 :
        ‖α ^ 2 * z ^ 2‖ ≤ ‖α‖ ^ 2 * ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow]
    have hterm2 :
        ‖(1 + α * z) * e‖ ≤ (1 + ‖α‖) * Ksub * ‖z‖ ^ 2 := by
      calc
        ‖(1 + α * z) * e‖ = ‖1 + α * z‖ * ‖e‖ := norm_mul _ _
        _ ≤ (1 + ‖α‖) * (Ksub * ‖z‖ ^ 2) := by
              exact mul_le_mul hone he (by positivity) (by positivity)
        _ = (1 + ‖α‖) * Ksub * ‖z‖ ^ 2 := by ring
    calc
      ‖α ^ 2 * z ^ 2 - (1 + α * z) * e‖ ≤ ‖α ^ 2 * z ^ 2‖ + ‖(1 + α * z) * e‖ := by
        exact norm_sub_le _ _
      _ ≤ ‖α‖ ^ 2 * ‖z‖ ^ 2 + (1 + ‖α‖) * Ksub * ‖z‖ ^ 2 := by
        exact add_le_add hterm1 hterm2
      _ = (‖α‖ ^ 2 + (1 + ‖α‖) * Ksub) * ‖z‖ ^ 2 := by ring
  have hqeq : padeQ n d z = 1 - α * z + e := by
    simp [e]
  have hkey :
      (padeQ n d z)⁻¹ - (1 + α * z) =
        (α ^ 2 * z ^ 2 - (1 + α * z) * e) / padeQ n d z := by
    calc
      (padeQ n d z)⁻¹ - (1 + α * z) =
          ((1 : ℂ) - (1 + α * z) * padeQ n d z) / padeQ n d z := by
            field_simp [hqne]
      _ = ((1 : ℂ) - (1 + α * z) * (1 - α * z + e)) / padeQ n d z := by
            rw [hqeq]
      _ = (α ^ 2 * z ^ 2 - (1 + α * z) * e) / padeQ n d z := by
            ring
  rw [hkey, norm_div, div_eq_mul_inv]
  calc
    ‖α ^ 2 * z ^ 2 - (1 + α * z) * e‖ * ‖padeQ n d z‖⁻¹ ≤
      ((‖α‖ ^ 2 + (1 + ‖α‖) * Ksub) * ‖z‖ ^ 2) * ‖padeQ n d z‖⁻¹ := by
        gcongr
    _ = ((‖α‖ ^ 2 + (1 + ‖α‖) * Ksub) * ‖z‖ ^ 2) * ‖(padeQ n d z)⁻¹‖ := by
          rw [norm_inv]
    _ ≤ ((‖α‖ ^ 2 + (1 + ‖α‖) * Ksub) * ‖z‖ ^ 2) * 2 := by
          gcongr
          exact hinv z hzinv
    _ = Kbase * ‖z‖ ^ 2 := by
          dsimp [Kbase]
          ring
    _ ≤ (Kbase + 1) * ‖z‖ ^ 2 := by
          have hpow : 0 ≤ ‖z‖ ^ 2 := pow_nonneg (norm_nonneg z) _
          nlinarith

private theorem exp_neg_div_padeQ_linear_local_norm_bound
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖exp (-z) / padeQ n d z - (1 - ((n : ℂ) / (n + d : ℂ)) * z)‖ ≤
          K * ‖z‖ ^ 2 := by
  let α : ℂ := (d : ℂ) / (n + d : ℂ)
  let β : ℂ := (n : ℂ) / (n + d : ℂ)
  obtain ⟨δE, KE, hδE, hKE, hE⟩ := expTaylor_exp_neg_local_norm_bound 0
  obtain ⟨δQ, KQ, hδQ, hKQ, hQ⟩ := padeQ_inv_linear_local_norm_bound n d hm
  obtain ⟨δinv, hδinv, hinv⟩ := padeQ_inv_bound n d
  obtain ⟨δnz, hδnz, hnz⟩ := padeQ_ne_zero_nhds n d
  let δ : ℝ := min 1 (min δE (min δQ (min δinv δnz)))
  let Kbase : ℝ := ‖α‖ + 2 * KE + 2 * KQ
  have hm_ne : ((n + d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hfrac : α + β = 1 := by
    have hfrac' : (((d : ℂ) + (n : ℂ)) * ((n + d : ℂ))⁻¹) = 1 := by
      have hcast : ((d : ℂ) + (n : ℂ)) = ((n + d : ℕ) : ℂ) := by
        norm_num [Nat.cast_add, add_comm, add_left_comm, add_assoc]
      rw [hcast]
      simpa [hm_ne] using mul_inv_cancel₀ hm_ne
    calc
      α + β = (((d : ℂ) + (n : ℂ)) * ((n + d : ℂ))⁻¹) := by
        dsimp [α, β]
        ring
      _ = 1 := hfrac'
  refine ⟨δ, Kbase + 1, lt_min zero_lt_one (lt_min hδE (lt_min hδQ (lt_min hδinv hδnz))),
    by positivity, ?_⟩
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hz (min_le_left _ _))
  have hzE : ‖z‖ < δE := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzQ : ‖z‖ < δQ := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hzinv : ‖z‖ < δinv := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hznz : ‖z‖ < δnz := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hqne : padeQ n d z ≠ 0 := hnz z hznz
  let eExp : ℂ := exp (-z) - (1 - z)
  let eInv : ℂ := (padeQ n d z)⁻¹ - (1 + α * z)
  have hExp' : ‖eExp‖ ≤ KE * ‖z‖ ^ 2 := by
    simpa [eExp, expTaylor, Finset.range_one] using hE z hzE
  have hInv' : ‖eInv‖ ≤ KQ * ‖z‖ ^ 2 := by
    simpa [eInv, α] using hQ z hzQ
  have hOneSub : ‖1 - z‖ ≤ 2 := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := by
        simpa [sub_eq_add_neg] using norm_add_le (1 : ℂ) (-z)
      _ = 1 + ‖z‖ := by norm_num
      _ ≤ 1 + 1 := by
            gcongr
      _ = 2 := by norm_num
  have hkey :
      exp (-z) / padeQ n d z - (1 - β * z) =
        eExp * (padeQ n d z)⁻¹ + (1 - z) * eInv - α * z ^ 2 := by
    have hExpEq : exp (-z) = 1 - z + eExp := by
      simp [eExp]
    have hInvEq : 1 + α * z + eInv = (padeQ n d z)⁻¹ := by
      simp [eInv]
    rw [div_eq_mul_inv, hExpEq]
    have hlin :
        -z + α * z + β * z = 0 := by
      calc
        -z + α * z + β * z = z * (α + β - 1) := by ring
        _ = 0 := by rw [hfrac]; ring
    calc
      (1 - z + eExp) * (padeQ n d z)⁻¹ - (1 - β * z) =
          (1 - z + eExp) * (1 + α * z + eInv) - (1 - β * z) := by
              rw [← hInvEq]
      _ =
          (-z + α * z + β * z) - α * z ^ 2 +
            eExp * (1 + α * z + eInv) + (1 - z) * eInv := by
              ring
      _ = eExp * (1 + α * z + eInv) + (1 - z) * eInv - α * z ^ 2 := by
            rw [hlin]
            ring
      _ = eExp * (padeQ n d z)⁻¹ + (1 - z) * eInv - α * z ^ 2 := by
            simp [eInv]
  have hterm1 :
      ‖eExp * (padeQ n d z)⁻¹‖ ≤ 2 * KE * ‖z‖ ^ 2 := by
    calc
      ‖eExp * (padeQ n d z)⁻¹‖ = ‖eExp‖ * ‖(padeQ n d z)⁻¹‖ := norm_mul _ _
      _ ≤ (KE * ‖z‖ ^ 2) * 2 := by
            exact mul_le_mul hExp' (hinv z hzinv) (by positivity) (by positivity)
      _ = 2 * KE * ‖z‖ ^ 2 := by ring
  have hterm2 :
      ‖(1 - z) * eInv‖ ≤ 2 * KQ * ‖z‖ ^ 2 := by
    calc
      ‖(1 - z) * eInv‖ = ‖1 - z‖ * ‖eInv‖ := norm_mul _ _
      _ ≤ 2 * (KQ * ‖z‖ ^ 2) := by
            exact mul_le_mul hOneSub hInv' (by positivity) (by positivity)
      _ = 2 * KQ * ‖z‖ ^ 2 := by ring
  have hterm3 :
      ‖α * z ^ 2‖ ≤ ‖α‖ * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_pow]
  rw [hkey]
  calc
    ‖eExp * (padeQ n d z)⁻¹ + (1 - z) * eInv - α * z ^ 2‖
      ≤ ‖eExp * (padeQ n d z)⁻¹‖ + ‖(1 - z) * eInv‖ + ‖α * z ^ 2‖ := by
            have h12 := norm_add_le (eExp * (padeQ n d z)⁻¹) ((1 - z) * eInv)
            have h123 := norm_sub_le (eExp * (padeQ n d z)⁻¹ + (1 - z) * eInv) (α * z ^ 2)
            linarith
    _ ≤ 2 * KE * ‖z‖ ^ 2 + 2 * KQ * ‖z‖ ^ 2 + ‖α‖ * ‖z‖ ^ 2 := by
          nlinarith [hterm1, hterm2, hterm3]
    _ = Kbase * ‖z‖ ^ 2 := by
          dsimp [Kbase]
          ring
    _ ≤ (Kbase + 1) * ‖z‖ ^ 2 := by
          have hpow : 0 ≤ ‖z‖ ^ 2 := pow_nonneg (norm_nonneg z) _
          nlinarith

theorem padeR_exp_neg_second_order_local_bound
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ K₂ δ₂ : ℝ, 0 < K₂ ∧ 0 < δ₂ ∧
      ∀ z : ℂ, ‖z‖ < δ₂ →
        ‖padeR n d z * exp (-z) -
            (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2))‖ ≤
          K₂ * ‖z‖ ^ (n + d + 3) := by
  let m : ℕ := n + d
  let a : ℂ := (1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)
  let b : ℂ := padeDefectSecondCoeff n d
  let c : ℂ := expTaylorExpNegSecondCoeff m
  let β : ℂ := (n : ℂ) / (n + d : ℂ)
  obtain ⟨KD, hKD, hD⟩ := padeDefect_sub_second_local_bound n d
  obtain ⟨δE, KE, hδE, hKE, hE⟩ := expTaylor_exp_neg_second_local_norm_bound m
  obtain ⟨δQ, KQ, hδQ, hKQ, hQ⟩ := exp_neg_div_padeQ_linear_local_norm_bound n d hm
  obtain ⟨δinv, hδinv, hinv⟩ := padeQ_inv_bound n d
  obtain ⟨δnz, hδnz, hnz⟩ := padeQ_ne_zero_nhds n d
  let δ₂ : ℝ := min 1 (min δE (min δQ (min δinv δnz)))
  let Kbase : ℝ := KE + KD * (2 * Real.exp 1) + ‖b * β‖ + (‖a‖ + ‖b‖) * KQ
  have hcoeff :
      c + b - a * β = (padeRExpNegSecondCoeff n d : ℂ) := by
    simpa [m, a, b, c, β] using padeR_exp_neg_second_coeff_identity n d hm
  refine ⟨Kbase + 1, δ₂, by positivity,
    lt_min zero_lt_one (lt_min hδE (lt_min hδQ (lt_min hδinv hδnz))), ?_⟩
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hz (min_le_left _ _))
  have hzE : ‖z‖ < δE := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzQ : ‖z‖ < δQ := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hzinv : ‖z‖ < δinv := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hznz : ‖z‖ < δnz := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hqne : padeQ n d z ≠ 0 := hnz z hznz
  let tail : ℂ :=
    expTaylor m z * exp (-z) -
      (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1) + c * z ^ (m + 2))
  let defect : ℂ :=
    padeP n d z - padeQ n d z * expTaylor m z - a * z ^ (m + 1) - b * z ^ (m + 2)
  let qval : ℂ := exp (-z) / padeQ n d z
  let qerr : ℂ := qval - (1 - β * z)
  have htail : ‖tail‖ ≤ KE * ‖z‖ ^ (m + 3) := by
    simpa [m, c, tail] using hE z hzE
  have hdefect : ‖defect‖ ≤ KD * ‖z‖ ^ (m + 3) := by
    simpa [m, a, b, defect] using hD z hz1
  have hqerr : ‖qerr‖ ≤ KQ * ‖z‖ ^ 2 := by
    simpa [qerr, qval, β] using hQ z hzQ
  have hqval_bound : ‖qval‖ ≤ 2 * Real.exp 1 := by
    have hExpNorm : ‖Complex.exp (-z)‖ ≤ Real.exp 1 := by
      calc
        ‖Complex.exp (-z)‖ ≤ Real.exp ‖-z‖ := Complex.norm_exp_le_exp_norm (-z)
        _ = Real.exp ‖z‖ := by simp
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hz1
    calc
      ‖qval‖ = ‖exp (-z) / padeQ n d z‖ := by rfl
      _ = ‖Complex.exp (-z)‖ * ‖(padeQ n d z)⁻¹‖ := by
            rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ Real.exp 1 * 2 := by
            exact mul_le_mul hExpNorm (hinv z hzinv) (by positivity) (by positivity)
      _ = 2 * Real.exp 1 := by ring
  have hsplit_frac :
      padeR n d z * exp (-z) =
        expTaylor m z * exp (-z) +
          (padeP n d z - padeQ n d z * expTaylor m z) * qval := by
    rw [padeR]
    dsimp [qval]
    field_simp [hqne]
    ring
  have hsplit :
      padeR n d z * exp (-z) -
          (1 - (padePhiErrorConst n d : ℂ) * z ^ (m + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * z ^ (m + 2)) =
        tail + defect * qval +
          (-b * β) * z ^ (m + 3) +
          (a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr := by
    have hcoeff' : (padeRExpNegSecondCoeff n d : ℂ) = c + b - a * β := by
      simpa using hcoeff.symm
    rw [hsplit_frac]
    dsimp [tail, defect, qerr]
    rw [hcoeff']
    ring
  have hdefect_qval :
      ‖defect * qval‖ ≤ KD * (2 * Real.exp 1) * ‖z‖ ^ (m + 3) := by
    calc
      ‖defect * qval‖ = ‖defect‖ * ‖qval‖ := norm_mul _ _
      _ ≤ (KD * ‖z‖ ^ (m + 3)) * (2 * Real.exp 1) := by
            exact mul_le_mul hdefect hqval_bound (by positivity) (by positivity)
      _ = KD * (2 * Real.exp 1) * ‖z‖ ^ (m + 3) := by ring
  have hzpow_le :
      ‖z‖ ^ (m + 4) ≤ ‖z‖ ^ (m + 3) := by
    rw [show m + 4 = (m + 3) + 1 by omega, pow_succ']
    nlinarith [pow_nonneg (norm_nonneg z) (m + 3), hz1]
  have hterm_a :
      ‖a * z ^ (m + 1) * qerr‖ ≤ ‖a‖ * KQ * ‖z‖ ^ (m + 3) := by
    calc
      ‖a * z ^ (m + 1) * qerr‖ = ‖a‖ * (‖z‖ ^ (m + 1) * ‖qerr‖) := by
            rw [norm_mul, norm_mul, norm_pow]
            ring
      _ ≤ ‖a‖ * (‖z‖ ^ (m + 1) * (KQ * ‖z‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hqerr (pow_nonneg (norm_nonneg z) _))
              (norm_nonneg _)
      _ = ‖a‖ * KQ * ‖z‖ ^ (m + 3) := by
            rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
            ring
  have hterm_b :
      ‖b * z ^ (m + 2) * qerr‖ ≤ ‖b‖ * KQ * ‖z‖ ^ (m + 3) := by
    calc
      ‖b * z ^ (m + 2) * qerr‖ = ‖b‖ * (‖z‖ ^ (m + 2) * ‖qerr‖) := by
            rw [norm_mul, norm_mul, norm_pow]
            ring
      _ ≤ ‖b‖ * (‖z‖ ^ (m + 2) * (KQ * ‖z‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hqerr (pow_nonneg (norm_nonneg z) _))
              (norm_nonneg _)
      _ = ‖b‖ * KQ * ‖z‖ ^ (m + 4) := by
            rw [show m + 4 = (m + 2) + 2 by omega, pow_add]
            ring
      _ ≤ ‖b‖ * KQ * ‖z‖ ^ (m + 3) := by
            gcongr
  have hprincipal :
      ‖(a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr‖ ≤
        (‖a‖ + ‖b‖) * KQ * ‖z‖ ^ (m + 3) := by
    have hsum :
        (a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr =
          a * z ^ (m + 1) * qerr + b * z ^ (m + 2) * qerr := by
      ring
    rw [hsum]
    calc
      ‖a * z ^ (m + 1) * qerr + b * z ^ (m + 2) * qerr‖
        ≤ ‖a * z ^ (m + 1) * qerr‖ + ‖b * z ^ (m + 2) * qerr‖ := norm_add_le _ _
      _ ≤ ‖a‖ * KQ * ‖z‖ ^ (m + 3) + ‖b‖ * KQ * ‖z‖ ^ (m + 3) := by
            exact add_le_add hterm_a hterm_b
      _ = (‖a‖ + ‖b‖) * KQ * ‖z‖ ^ (m + 3) := by ring
  have hthird :
      ‖(-b * β) * z ^ (m + 3)‖ ≤ ‖b * β‖ * ‖z‖ ^ (m + 3) := by
    rw [norm_mul, norm_pow]
    simp
  rw [hsplit]
  calc
    ‖tail + defect * qval + (-b * β) * z ^ (m + 3) +
        (a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr‖
      ≤ ‖tail‖ + ‖defect * qval‖ + ‖(-b * β) * z ^ (m + 3)‖ +
          ‖(a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr‖ := by
            have h12 := norm_add_le tail (defect * qval)
            have h123 := norm_add_le (tail + defect * qval) ((-b * β) * z ^ (m + 3))
            have h1234 := norm_add_le
              (tail + defect * qval + (-b * β) * z ^ (m + 3))
              ((a * z ^ (m + 1) + b * z ^ (m + 2)) * qerr)
            linarith
    _ ≤ KE * ‖z‖ ^ (m + 3) +
          KD * (2 * Real.exp 1) * ‖z‖ ^ (m + 3) +
          ‖b * β‖ * ‖z‖ ^ (m + 3) +
          (‖a‖ + ‖b‖) * KQ * ‖z‖ ^ (m + 3) := by
            nlinarith [htail, hdefect_qval, hthird, hprincipal]
    _ = Kbase * ‖z‖ ^ (m + 3) := by
          dsimp [Kbase]
          ring
    _ ≤ (Kbase + 1) * ‖z‖ ^ (m + 3) := by
          have hpow : 0 ≤ ‖z‖ ^ (m + 3) := pow_nonneg (norm_nonneg z) _
          nlinarith

private theorem padePhiErrorConst_neg_implies_pos_nd
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    0 < n + d := by
  by_contra h
  push_neg at h
  have hnz : n = 0 := by omega
  have hdz : d = 0 := by omega
  subst hnz
  subst hdz
  norm_num [padePhiErrorConst] at hC

private theorem padeRExpNegSecondCoeff_abs_lt_half_main
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    |padeRExpNegSecondCoeff n d| <
      (-padePhiErrorConst n d) * (((↑(n + d) + 1) : ℝ) / 2) := by
  let m : ℕ := n + d
  have hm : 0 < m := by
    simpa [m] using padePhiErrorConst_neg_implies_pos_nd n d hC
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hm1_pos : 0 < ((m : ℝ) + 1) := by positivity
  have hm2_pos : 0 < ((m : ℝ) + 2) := by positivity
  have hnegC : 0 < -padePhiErrorConst n d := by
    linarith
  have habsC : |padePhiErrorConst n d| = -padePhiErrorConst n d := abs_of_neg hC
  have habs_nd : |(n : ℝ) - d| ≤ (m : ℝ) := by
    refine abs_le.mpr ?_
    constructor <;> linarith [show (m : ℝ) = (n : ℝ) + d by
      norm_num [m, Nat.cast_add]]
  have hratio :
      |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| <
        ((m : ℝ) + 1) / 2 := by
    have hmprod_pos : 0 < (m : ℝ) * ((m : ℝ) + 2) := by positivity
    have habsden : |(m : ℝ) * ((m : ℝ) + 2)| = (m : ℝ) * ((m : ℝ) + 2) := by
      rw [abs_of_pos hmprod_pos]
    rw [abs_div, abs_mul, abs_of_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity), habsden]
    have hratio_le :
        |(n : ℝ) - d| * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) ≤
          ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
      calc
        |(n : ℝ) - d| * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) ≤
            (m : ℝ) * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) := by
              gcongr
        _ = ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
              field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm)]
    have hfrac :
        ((m : ℝ) + 1) / ((m : ℝ) + 2) < ((m : ℝ) + 1) / 2 := by
      have hinv : (1 : ℝ) / ((m : ℝ) + 2) < 1 / 2 := by
        rw [one_div_lt_one_div hm2_pos (by positivity : (0 : ℝ) < 2)]
        linarith
      have hmul :
          ((m : ℝ) + 1) * ((1 : ℝ) / ((m : ℝ) + 2)) <
            ((m : ℝ) + 1) * (1 / 2) := by
              exact mul_lt_mul_of_pos_left hinv hm1_pos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact lt_of_le_of_lt hratio_le hfrac
  have hformula :
      |padeRExpNegSecondCoeff n d| =
        |padePhiErrorConst n d| *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := by
    simp [padeRExpNegSecondCoeff, m, abs_mul, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm]
  calc
    |padeRExpNegSecondCoeff n d| =
        |padePhiErrorConst n d| *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := hformula
    _ = (-padePhiErrorConst n d) *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := by
            rw [habsC]
    _ < (-padePhiErrorConst n d) * (((m : ℝ) + 1) / 2) := by
          exact mul_lt_mul_of_pos_left hratio hnegC
    _ = (-padePhiErrorConst n d) * (((↑(n + d) + 1) : ℝ) / 2) := by
          simp [m]

/-- Remaining no-stop seam: show that the connected component of `(0,0)` in the
compact odd-wedge zero set projects onto the full radius interval. The compact
zero-set and closed-projection infrastructure is now live above this theorem. -/
private theorem oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0,
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        0 < Complex.im
          (padeR n d
              (((↑r : ℂ) *
                  exp (↑(oddDownArrowRadiusPhaseCenter n d - r) * I))) *
            exp (-(((↑r : ℂ) *
                exp (↑(oddDownArrowRadiusPhaseCenter n d - r) * I))))) ∧
        Complex.im
          (padeR n d
              (((↑r : ℂ) *
                  exp (↑(oddDownArrowRadiusPhaseCenter n d + r) * I))) *
            exp (-(((↑r : ℂ) *
                exp (↑(oddDownArrowRadiusPhaseCenter n d + r) * I))))) < 0 := by
  have hm : 0 < n + d := padePhiErrorConst_neg_implies_pos_nd n d hC
  obtain ⟨K₂, δ₂, hK₂, hδ₂, hφ₂⟩ := padeR_exp_neg_second_order_local_bound n d hm
  let p1 : ℝ := ((↑(n + d) + 1) : ℝ)
  let θ0 : ℝ := oddDownArrowRadiusPhaseCenter n d
  let absC2 : ℝ := |padeRExpNegSecondCoeff n d|
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  have hnegC : 0 < -padePhiErrorConst n d := by
    linarith
  have hC2_lt :
      absC2 < (-padePhiErrorConst n d) * p1 / 2 := by
    have hraw := padeRExpNegSecondCoeff_abs_lt_half_main n d hC
    dsimp [absC2, p1] at hraw ⊢
    nlinarith
  let gap : ℝ := (-padePhiErrorConst n d) * p1 / 2 - absC2
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  let δ : ℝ := min (δ₂ / 2) (min (1 / p1) (gap / (2 * K₂)))
  have hδpos : 0 < δ := by
    dsimp [δ]
    refine lt_min (half_pos hδ₂) ?_
    refine lt_min (one_div_pos.mpr hp1_pos) ?_
    exact div_pos hgap_pos (mul_pos two_pos hK₂)
  refine ⟨δ, hδpos, ?_⟩
  intro r hr
  have hr_delta : r < δ₂ := by
    have hδ_le_half : δ ≤ δ₂ / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hhalf : δ₂ / 2 < δ₂ := by
      linarith
    exact lt_trans (lt_of_lt_of_le hr.2 hδ_le_half) hhalf
  have hr_inv : r < 1 / p1 := by
    exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hαlt_one : p1 * r < 1 := by
    have hmul : p1 * r < p1 * (1 / p1) := mul_lt_mul_of_pos_left hr_inv hp1_pos
    have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
    rw [show p1 * (1 / p1) = 1 by field_simp [hp1_ne]] at hmul
    exact hmul
  have hαpi2 : p1 * r < Real.pi / 2 := by
    linarith [hαlt_one, Real.pi_gt_three]
  have hαpos : 0 < p1 * r := mul_pos hp1_pos hr.1
  have hhalf_lt_coeff :
      p1 * r / 2 < (2 / Real.pi) * (p1 * r) := by
    have hconst : (1 / 2 : ℝ) < 2 / Real.pi := by
      have hnum : 0 < 4 - Real.pi := by
        linarith [Real.pi_lt_four]
      have hden : 0 < 2 * Real.pi := by positivity
      have hcalc : 2 / Real.pi - 1 / 2 = (4 - Real.pi) / (2 * Real.pi) := by
        field_simp [show (Real.pi : ℝ) ≠ 0 by exact Real.pi_ne_zero]
        ring
      have : 0 < 2 / Real.pi - 1 / 2 := by
        rw [hcalc]
        exact div_pos hnum hden
      linarith
    have := mul_lt_mul_of_pos_right hconst hαpos
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hhalf_lt_sin : p1 * r / 2 < Real.sin (p1 * r) := by
    exact lt_trans hhalf_lt_coeff (Real.mul_lt_sin hαpos hαpi2)
  have hgap_bound : K₂ * r < gap := by
    have hr_gap : r < gap / (2 * K₂) := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    calc
      K₂ * r < K₂ * (gap / (2 * K₂)) := mul_lt_mul_of_pos_left hr_gap hK₂
      _ = gap / 2 := by
            field_simp [show (K₂ : ℝ) ≠ 0 by linarith]
      _ < gap := by linarith
  let zL : ℂ := (↑r : ℂ) * exp (↑(θ0 - r) * I)
  let zR : ℂ := (↑r : ℂ) * exp (↑(θ0 + r) * I)
  have hzL_norm : ‖zL‖ = r := by
    simpa [zL] using norm_ofReal_mul_exp_I r (θ0 - r) hr.1.le
  have hzR_norm : ‖zR‖ = r := by
    simpa [zR] using norm_ofReal_mul_exp_I r (θ0 + r) hr.1.le
  have hzL_delta : ‖zL‖ < δ₂ := by
    simpa [hzL_norm] using hr_delta
  have hzR_delta : ‖zR‖ < δ₂ := by
    simpa [hzR_norm] using hr_delta
  have hboundL := hφ₂ zL hzL_delta
  have hboundR := hφ₂ zR hzR_delta
  have hmainL :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
        (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) := by
    simpa [zL, p1, θ0, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_left (p := n + d) (c := padePhiErrorConst n d) r r)
  have hmainR :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
        -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) := by
    simpa [zR, p1, θ0, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) r r)
  have him_rem_L :
      abs
        (Complex.im (padeR n d zL * exp (-zL)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
        K₂ * r ^ (n + d + 3) := by
    have him_le :
        abs
          (Complex.im (padeR n d zL * exp (-zL)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
          ‖padeR n d zL * exp (-zL) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))‖ := by
      simpa using
        abs_im_sub_le_norm_sub
          (a := padeR n d zL * exp (-zL))
          (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))
    have hboundL' :
        ‖padeR n d zL * exp (-zL) -
          ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))‖ ≤
        K₂ * r ^ (n + d + 3) := by
      simpa [hzL_norm] using hboundL
    exact le_trans him_le hboundL'
  have him_rem_R :
      abs
        (Complex.im (padeR n d zR * exp (-zR)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
        K₂ * r ^ (n + d + 3) := by
    have him_le :
        abs
          (Complex.im (padeR n d zR * exp (-zR)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
          ‖padeR n d zR * exp (-zR) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))‖ := by
      simpa using
        abs_im_sub_le_norm_sub
          (a := padeR n d zR * exp (-zR))
          (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))
    have hboundR' :
        ‖padeR n d zR * exp (-zR) -
          ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))‖ ≤
        K₂ * r ^ (n + d + 3) := by
      simpa [hzR_norm] using hboundR
    exact le_trans him_le hboundR'
  have him_C2_L :
      abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
        absC2 * r ^ (n + d + 2) := by
    calc
      abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
          ‖(padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)‖ := Complex.abs_im_le_norm _
      _ = absC2 * r ^ (n + d + 2) := by
            rw [norm_mul, norm_pow, hzL_norm, Complex.norm_real]
            simp [absC2, Real.norm_eq_abs]
  have him_C2_R :
      abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
        absC2 * r ^ (n + d + 2) := by
    calc
      abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
          ‖(padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)‖ := Complex.abs_im_le_norm _
      _ = absC2 * r ^ (n + d + 2) := by
            rw [norm_mul, norm_pow, hzR_norm, Complex.norm_real]
            simp [absC2, Real.norm_eq_abs]
  have himdiffL :
      abs
        (Complex.im (padeR n d zL * exp (-zL)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
        absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by
    have him_approx2 :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) =
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) := by
      rw [Complex.add_im]
    have hsplit_im :
        Complex.im (padeR n d zL * exp (-zL)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
          (Complex.im (padeR n d zL * exp (-zL)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) := by
      rw [him_approx2]
      ring
    rw [hsplit_im]
    calc
      abs
          ((Complex.im (padeR n d zL * exp (-zL)) -
                Complex.im
                  ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                    (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
        abs
            (Complex.im (padeR n d zL * exp (-zL)) -
              Complex.im
                ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                  (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
          abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) := by
            exact abs_add_le _ _
      _ ≤ K₂ * r ^ (n + d + 3) + absC2 * r ^ (n + d + 2) := by
            exact add_le_add him_rem_L him_C2_L
      _ = absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by ring
  have himdiffR :
      abs
        (Complex.im (padeR n d zR * exp (-zR)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
        absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by
    have him_approx2 :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
            (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) =
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) := by
      rw [Complex.add_im]
    have hsplit_im :
        Complex.im (padeR n d zR * exp (-zR)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
          (Complex.im (padeR n d zR * exp (-zR)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) := by
      rw [him_approx2]
      ring
    rw [hsplit_im]
    calc
      abs
          ((Complex.im (padeR n d zR * exp (-zR)) -
                Complex.im
                  ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                    (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
            Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
        abs
            (Complex.im (padeR n d zR * exp (-zR)) -
              Complex.im
                ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                  (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
          abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) := by
            exact abs_add_le _ _
      _ ≤ K₂ * r ^ (n + d + 3) + absC2 * r ^ (n + d + 2) := by
            exact add_le_add him_rem_R him_C2_R
      _ = absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by ring
  have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
  have hpow2_pos : 0 < r ^ (n + d + 2) := pow_pos hr.1 _
  have hmain_lower :
      (-padePhiErrorConst n d) * p1 / 2 * r ^ (n + d + 2) <
        (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) := by
    rw [show r ^ (n + d + 2) = r * r ^ (n + d + 1) by rw [pow_succ']]
    rw [show (-padePhiErrorConst n d) * p1 / 2 * (r * r ^ (n + d + 1)) =
        r ^ (n + d + 1) * ((-padePhiErrorConst n d) * (p1 * r / 2)) by ring]
    rw [show (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) =
        r ^ (n + d + 1) * ((-padePhiErrorConst n d) * Real.sin (p1 * r)) by ring]
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hhalf_lt_sin hnegC) hpow_pos
  have hcorr_small :
      absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) <
        (-padePhiErrorConst n d) * p1 / 2 * r ^ (n + d + 2) := by
    have hlin :
        absC2 + K₂ * r < (-padePhiErrorConst n d) * p1 / 2 := by
      dsimp [gap] at hgap_bound hgap_pos
      nlinarith
    have hrewrite :
        absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) =
          r ^ (n + d + 2) * (absC2 + K₂ * r) := by
      rw [show r ^ (n + d + 3) = r * r ^ (n + d + 2) by rw [pow_succ']]
      ring
    rw [hrewrite]
    have hmul :
        r ^ (n + d + 2) * (absC2 + K₂ * r) <
          r ^ (n + d + 2) * ((-padePhiErrorConst n d) * p1 / 2) := by
      exact mul_lt_mul_of_pos_left hlin hpow2_pos
    have htarget :
        r ^ (n + d + 2) * ((-padePhiErrorConst n d) * p1 / 2) =
          (-padePhiErrorConst n d) * p1 / 2 * r ^ (n + d + 2) := by ring
    exact htarget ▸ hmul
  have hleft_core :
      0 < (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) -
        (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) := by
    linarith
  have hright_core :
      -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) +
        (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) < 0 := by
    linarith
  have hleft_bound :
      (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) -
        (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) ≤
        Complex.im (padeR n d zL * exp (-zL)) := by
    have h' := abs_le.mp himdiffL
    linarith [hmainL]
  have hright_bound :
      Complex.im (padeR n d zR * exp (-zR)) ≤
        -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) +
          (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) := by
    have h' := abs_le.mp himdiffR
    linarith [hmainR]
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hleft_core hleft_bound
  · exact lt_of_le_of_lt hright_bound hright_core

/-- Remaining no-stop seam: show that the connected component of `(0,0)` in the
compact odd-wedge zero set projects onto the full radius interval. The compact
zero-set and closed-projection infrastructure is now live above this theorem. -/
private theorem oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0,
      (∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) δ,
        ∃ s ∈ Set.Icc (-r) r,
          (r, s) ∈ oddDownArrowRadiusPhaseZeroSet n d δ) := by
  obtain ⟨δre, hδre, hre_small⟩ := padeR_exp_neg_re_pos_of_small_norm n d
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δslice, hδslice, hendpoint⟩ :=
    oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst n d hC
  let δ : ℝ := min (δre / 2) (min (δQ / 2) (δslice / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hδre) (lt_min (half_pos hδQ) (half_pos hδslice))
  have hδlt_re : δ < δre := by
    dsimp [δ]
    have hhalf : δre / 2 < δre := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hδlt_Q : δ < δQ := by
    dsimp [δ]
    have hhalf : δQ / 2 < δQ := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) hhalf
  have hre_wedge :
      ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p) :=
    oddDownArrowRadiusPhaseRe_pos_on_wedge_of_small_norm n d hre_small hδlt_re
  refine ⟨δ, hδ, hre_wedge, ?_⟩
  intro r hr
  rcases eq_or_lt_of_le hr.1 with rfl | hrpos
  · refine ⟨0, by simp, ?_⟩
    simpa using mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  · let θ0 : ℝ := oddDownArrowRadiusPhaseCenter n d
    have hrδQ : r < δQ := lt_of_le_of_lt hr.2 hδlt_Q
    have hr_slice : r ∈ Set.Ioo (0 : ℝ) δslice := by
      refine ⟨hrpos, ?_⟩
      have hδ_le_slice_half : δ ≤ δslice / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hhalf : δslice / 2 < δslice := by
        linarith
      exact lt_of_le_of_lt hr.2 (lt_of_le_of_lt hδ_le_slice_half hhalf)
    have hcont_complex :
        ContinuousOn
          (fun s : ℝ =>
            padeR n d ((↑r : ℂ) * exp (↑(θ0 + s) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + s) * I))))
          (Set.Icc (-r) r) :=
      padeR_exp_neg_continuousOn_angleArc n d θ0 r r δQ hrpos hrδQ hQ
    have him_cont : ContinuousOn (fun z : ℂ => Complex.im z) Set.univ :=
      Complex.continuous_im.continuousOn
    have hcont_im :
        ContinuousOn
          (fun s : ℝ =>
            Complex.im
              (padeR n d ((↑r : ℂ) * exp (↑(θ0 + s) * I)) *
                exp (-((↑r : ℂ) * exp (↑(θ0 + s) * I)))))
          (Set.Icc (-r) r) := by
      simpa [Function.comp] using
        (him_cont.comp hcont_complex (by
          intro x hx
          simp))
    have him_slice := hendpoint r hr_slice
    have him_left' :
        0 < Complex.im
          (padeR n d ((↑r : ℂ) * exp (↑(θ0 - r) * I)) *
            exp (-((↑r : ℂ) * exp (↑(θ0 - r) * I)))) := by
      simpa [θ0, oddDownArrowRadiusPhaseCenter] using him_slice.1
    have him_right' :
        Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 + r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + r) * I)))) < 0 := by
      simpa [θ0, oddDownArrowRadiusPhaseCenter] using him_slice.2
    have hzero_mem :
        (0 : ℝ) ∈ Set.Icc
          (Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 + r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + r) * I)))))
          (Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 - r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 - r) * I))))) := by
      exact ⟨le_of_lt him_right', le_of_lt him_left'⟩
    have hpre : IsPreconnected (Set.Icc (-r) r) := by
      simpa using isPreconnected_Icc
    have himage :=
      hpre.intermediate_value
        (show r ∈ Set.Icc (-r) r by simp [hrpos.le])
        (show -r ∈ Set.Icc (-r) r by simp [hrpos.le])
        hcont_im
    rcases himage hzero_mem with ⟨s, hsIcc, hszero⟩
    have hsZero :
        oddDownArrowRadiusPhaseIm n d (r, s) = 0 := by
      simpa [oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter, θ0] using hszero
    exact ⟨s, hsIcc, ⟨⟨hr, hsIcc⟩, hsZero⟩⟩

/-- If `f` is strictly anti-monotone on `[a, b]`, then `f` has at most one
zero there. -/
private theorem atMostOne_zero_of_strictAntiOn'
    {f : ℝ → ℝ} {a b : ℝ}
    (hanti : StrictAntiOn f (Set.Icc a b)) :
    ∀ s₁ ∈ Set.Icc a b, ∀ s₂ ∈ Set.Icc a b,
      f s₁ = 0 → f s₂ = 0 → s₁ = s₂ :=
  fun s₁ hs₁ s₂ hs₂ h₁ h₂ => StrictAntiOn.injOn hanti hs₁ hs₂ <| h₁.trans h₂.symm

/-- `cos(x) ≥ 1/2` when `|x| ≤ π/3`. -/
theorem cos_ge_half_of_abs_le' {x : ℝ} (hx : |x| ≤ Real.pi / 3) :
    1 / 2 ≤ Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_pi_div_three ▸
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [abs_le.mp hx]) (by linarith [abs_le.mp hx])

/-- A continuous function on `[-ρ, ρ]` with negative derivative on the interior
is `StrictAntiOn` there. -/
private theorem strictAntiOn_Icc_of_deriv_neg'
    {f : ℝ → ℝ} {ρ : ℝ}
    (hcont : ContinuousOn f (Set.Icc (-ρ) ρ))
    (hderiv : ∀ s ∈ Set.Ioo (-ρ) ρ, deriv f s < 0) :
    StrictAntiOn f (Set.Icc (-ρ) ρ) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Icc _ _
  · exact hcont
  · aesop

/-- If `f'` stays within `ε` of a negative constant `c_lead`, and `ε` is
strictly smaller than `|c_lead|`, then `f' < 0`. -/
private theorem deriv_neg_of_leading_neg_with_small_error'
    {f : ℝ → ℝ} {ρ : ℝ} {c_lead ε : ℝ}
    (_hc : c_lead < 0) (_hε : 0 ≤ ε) (hεsmall : ε < -c_lead)
    (hderiv_bound : ∀ s ∈ Set.Ioo (-ρ) ρ,
      |deriv f s - c_lead| ≤ ε) :
    ∀ s ∈ Set.Ioo (-ρ) ρ, deriv f s < 0 :=
  fun s hs => by linarith [abs_le.mp (hderiv_bound s hs)]

/-- Convert a complex derivative at a real point into a real derivative for
the imaginary part along the real axis. -/
private theorem hasDerivAt_im_of_complex_ofReal'
    {F : ℂ → ℂ} {F' : ℂ} {s : ℝ}
    (hF : HasDerivAt F F' (s : ℂ)) :
    HasDerivAt (fun t : ℝ => Complex.im (F (t : ℂ))) F'.im s := by
  have h1 : HasDerivAt (fun w : ℂ => -I * F w) (-I * F') (s : ℂ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hF.const_mul (-I)
  have h2 :
      HasDerivAt (fun t : ℝ => ((-I * F (t : ℂ)).re)) ((-I * F').re) s := by
    exact HasDerivAt.real_of_complex (z := s) (e := fun w : ℂ => -I * F w) (e' := -I * F') h1
  simpa [Complex.I_mul_re, mul_comm, mul_left_comm, mul_assoc] using h2

/-- Derivative of the fixed-radius phase path with respect to the slice
parameter. -/
private theorem oddDownArrowRadiusPhasePoint_hasDerivAt_snd
    (n d : ℕ) (ρ s : ℝ) :
    HasDerivAt
      (fun t : ℝ => oddDownArrowRadiusPhasePoint n d (ρ, t))
      (oddDownArrowRadiusPhasePoint n d (ρ, s) * I) s := by
  unfold oddDownArrowRadiusPhasePoint
  have hinner :
      HasDerivAt (fun t : ℝ => (↑(oddDownArrowRadiusPhaseCenter n d + t) : ℂ) * I) I s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((HasDerivAt.ofReal_comp
          ((hasDerivAt_const s (oddDownArrowRadiusPhaseCenter n d)).add (hasDerivAt_id s))).mul_const I)
  simpa [mul_assoc] using ((hinner.cexp).const_mul (ρ : ℂ))

/-- Cauchy derivative bound for the fixed-radius error term on a small ball. -/
private theorem error_deriv_bound_at_of_padeQ_ne_zero
    (n d : ℕ) {K δ₀ δQ ρ : ℝ}
    (hK : 0 < K) (_hδ₀ : 0 < δ₀) (_hδQ : 0 < δQ) (hρ : 0 < ρ)
    (h2ρ_δ₀ : 2 * ρ < δ₀) (h2ρ_δQ : 2 * ρ < δQ)
    (hQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖padeR n d z * exp (-z) -
        ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ ≤
      K * ‖z‖ ^ (n + d + 2))
    (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) ρ) :
    ‖deriv (fun z => padeR n d z * exp (-z) -
      ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) w‖ ≤
    K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) := by
  have h_diff : DifferentiableOn ℂ
      (fun z => padeR n d z * exp (-z) -
        (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)))
      (Metric.ball w ρ) := by
    refine DifferentiableOn.sub ?_ (Differentiable.differentiableOn (by norm_num))
    refine DifferentiableOn.mul ?_
      (Complex.differentiable_exp.comp_differentiableOn differentiableOn_id.neg)
    refine DifferentiableOn.div
      ((by unfold padeP; fun_prop : Differentiable ℂ (padeP n d)).differentiableOn)
      ((by unfold padeQ; fun_prop : Differentiable ℂ (padeQ n d)).differentiableOn)
      (fun z hz => hQ z (by
        have hzw : ‖z - w‖ < ρ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hz
        have hw' : ‖w‖ ≤ ρ := by simpa using hw
        calc
          ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_add_le (z - w) w
          _ < ρ + ρ := by linarith
          _ < δQ := by linarith))
  let F : ℂ → ℂ := fun z =>
    padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))
  have h_maps :
      Set.MapsTo F
        (Metric.ball w ρ)
        (Metric.closedBall (F w)
          (K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 2))) := by
    intro z hz
    have hz_norm : ‖z‖ < 2 * ρ := by
      have hzw : ‖z - w‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hw' : ‖w‖ ≤ ρ := by simpa using hw
      calc
        ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_add_le (z - w) w
        _ < ρ + ρ := by linarith
        _ = 2 * ρ := by ring
    have hw_norm : ‖w‖ ≤ ρ := by simpa using hw
    have hz_bound :
        ‖padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ ≤
          K * (2 * ρ) ^ (n + d + 2) := by
      refine le_trans (hφ z (by linarith)) ?_
      gcongr
    have hw_bound :
        ‖padeR n d w * exp (-w) - (1 - (padePhiErrorConst n d : ℂ) * w ^ (n + d + 1))‖ ≤
          K * ρ ^ (n + d + 2) := by
      refine le_trans (hφ w (by linarith)) ?_
      gcongr
    have hsum :
        ‖(padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) -
            (padeR n d w * exp (-w) - (1 - (padePhiErrorConst n d : ℂ) * w ^ (n + d + 1)))‖ ≤
          K * (2 * ρ) ^ (n + d + 2) + K * ρ ^ (n + d + 2) := by
      calc
        ‖(padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) -
            (padeR n d w * exp (-w) - (1 - (padePhiErrorConst n d : ℂ) * w ^ (n + d + 1)))‖
            ≤ ‖padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ +
                ‖padeR n d w * exp (-w) - (1 - (padePhiErrorConst n d : ℂ) * w ^ (n + d + 1))‖ := by
                  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                    norm_sub_le
                      (padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)))
                      (padeR n d w * exp (-w) - (1 - (padePhiErrorConst n d : ℂ) * w ^ (n + d + 1)))
        _ ≤ K * (2 * ρ) ^ (n + d + 2) + K * ρ ^ (n + d + 2) := by linarith
    have hpow_expand :
        K * (2 * ρ) ^ (n + d + 2) + K * ρ ^ (n + d + 2) =
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 2) := by
      rw [show (2 * ρ) ^ (n + d + 2) = 2 ^ (n + d + 2) * ρ ^ (n + d + 2) by rw [mul_pow]]
      ring
    have hmem :
        ‖F z - F w‖
          ≤ K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 2) := by
      simpa [hpow_expand]
        using hsum
    simpa [Metric.mem_closedBall, dist_eq_norm]
      using hmem
  have hderiv :=
    Complex.norm_deriv_le_div_of_mapsTo_ball h_diff h_maps hρ
  have hscale :
      (K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 2)) / ρ =
        K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) := by
    rw [pow_succ']
    field_simp [hρ.ne']
    ring
  simpa [hscale] using hderiv

/-- Lipschitz control for the fixed-radius error term on a small ball. -/
theorem error_lipschitz_on_ball_of_padeQ_ne_zero
    (n d : ℕ) {K δ₀ δQ ρ : ℝ}
    (hK : 0 < K) (hδ₀ : 0 < δ₀) (hδQ : 0 < δQ) (hρ : 0 < ρ)
    (h2ρ_δ₀ : 2 * ρ < δ₀) (h2ρ_δQ : 2 * ρ < δQ)
    (hQ : ∀ z : ℂ, ‖z‖ < δQ → padeQ n d z ≠ 0)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖padeR n d z * exp (-z) -
        ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ ≤
      K * ‖z‖ ^ (n + d + 2))
    (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ Metric.closedBall (0 : ℂ) ρ)
    (hz₂ : z₂ ∈ Metric.closedBall (0 : ℂ) ρ) :
    ‖(padeR n d z₂ * exp (-z₂) -
        ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₂ ^ (n + d + 1))) -
      (padeR n d z₁ * exp (-z₁) -
        ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₁ ^ (n + d + 1)))‖ ≤
      K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ‖z₂ - z₁‖ := by
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℂ)
    (f := fun z : ℂ =>
      padeR n d z * exp (-z) -
        ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) ?_ ?_
    (convex_closedBall (0 : ℂ) ρ) hz₁ hz₂
  · intro z hz
    refine DifferentiableAt.sub ?_ (by fun_prop)
    refine DifferentiableAt.mul ?_
      (Complex.differentiableAt_exp.comp z differentiableAt_id.neg)
    exact DifferentiableAt.div
      ((by unfold padeP; fun_prop : Differentiable ℂ (padeP n d)).differentiableAt)
      ((by unfold padeQ; fun_prop : Differentiable ℂ (padeQ n d)).differentiableAt)
      (hQ z (by simpa using lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (by linarith)))
  · intro z hz
    simpa using
      error_deriv_bound_at_of_padeQ_ne_zero
        n d hK hδ₀ hδQ hρ h2ρ_δ₀ h2ρ_δQ hQ hφ z hz

/-- Lower bound for the main term variation along a fixed-radius arc. -/
private theorem main_term_im_diff_bound_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0)
    {ρ s₁ s₂ : ℝ} (hρ : 0 < ρ) (hρ_small : (↑(n + d) + 1 : ℝ) * ρ ≤ Real.pi / 3)
    (hs₁ : s₁ ∈ Set.Icc (-ρ) ρ) (hs₂ : s₂ ∈ Set.Icc (-ρ) ρ) (hlt : s₁ < s₂) :
    let θ₀ := oddDownArrowRadiusPhaseCenter n d
    let z₁ := (↑ρ : ℂ) * exp (↑(θ₀ + s₁) * I)
    let z₂ := (↑ρ : ℂ) * exp (↑(θ₀ + s₂) * I)
    Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₁ ^ (n + d + 1)) -
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₂ ^ (n + d + 1)) ≥
      (-padePhiErrorConst n d) * ((↑(n + d) + 1 : ℝ)) *
        ρ ^ (n + d + 1) * (s₂ - s₁) / 2 := by
  let A : ℝ := (n + d + 1 : ℝ)
  have hmain₁ :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
        (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₁) * I)) ^ (n + d + 1))) =
        padePhiErrorConst n d * ρ ^ (n + d + 1) * Real.sin (A * s₁) := by
    simpa [A, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) ρ s₁)
  have hmain₂ :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
        (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₂) * I)) ^ (n + d + 1))) =
        padePhiErrorConst n d * ρ ^ (n + d + 1) * Real.sin (A * s₂) := by
    simpa [A, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) ρ s₂)
  have hρA : A * ρ ≤ Real.pi / 3 := by
    simpa [A] using hρ_small
  have hcont :
      ContinuousOn (fun x : ℝ => Real.sin (A * x)) (Set.Icc s₁ s₂) := by
    simpa [A, mul_comm] using
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hdiff :
      DifferentiableOn ℝ (fun x : ℝ => Real.sin (A * x)) (Set.Ioo s₁ s₂) := by
    intro x hx
    change DifferentiableWithinAt ℝ (fun y : ℝ => Real.sin (A * y)) (Set.Ioo s₁ s₂) x
    exact
      (((Real.hasDerivAt_sin (A * x)).comp x
        ((hasDerivAt_const x A).mul (hasDerivAt_id x))).differentiableAt.differentiableWithinAt)
  obtain ⟨c, hc, hcd⟩ :=
    exists_deriv_eq_slope (f := fun x : ℝ => Real.sin (A * x)) hlt hcont hdiff
  have hcIcc : c ∈ Set.Icc (-ρ) ρ := by
    refine ⟨?_, ?_⟩
    · linarith [hs₁.1, hs₂.1, hc.1, hc.2]
    · linarith [hs₁.2, hs₂.2, hc.1, hc.2]
  have hcmul_abs : |A * c| ≤ Real.pi / 3 := by
    calc
      |A * c| = A * |c| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ A * ρ := by
        gcongr
        exact abs_le.mpr hcIcc
      _ ≤ Real.pi / 3 := hρA
  have h_cos_bound : (1 / 2 : ℝ) ≤ Real.cos (A * c) :=
    cos_ge_half_of_abs_le' hcmul_abs
  have hderiv :
      deriv (fun x : ℝ => Real.sin (A * x)) c = A * Real.cos (A * c) := by
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_sin (A * c)).comp c
        ((hasDerivAt_const c A).mul (hasDerivAt_id c))).deriv)
  have hneq : s₂ - s₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
  have hratio :
      Real.sin (A * s₂) - Real.sin (A * s₁) =
        A * Real.cos (A * c) * (s₂ - s₁) := by
    rw [hderiv] at hcd
    field_simp [hneq] at hcd
    linarith
  have hsine_bound :
      A * (s₂ - s₁) / 2 ≤ Real.sin (A * s₂) - Real.sin (A * s₁) := by
    have hA_half : A / 2 ≤ A * Real.cos (A * c) := by
      have hA_nonneg : 0 ≤ A := by positivity
      nlinarith [h_cos_bound, hA_nonneg]
    have hdiff_nonneg : 0 ≤ s₂ - s₁ := le_of_lt (sub_pos.mpr hlt)
    calc
      A * (s₂ - s₁) / 2 = (A / 2) * (s₂ - s₁) := by ring
      _ ≤ (A * Real.cos (A * c)) * (s₂ - s₁) := by
        gcongr
      _ = Real.sin (A * s₂) - Real.sin (A * s₁) := by
        symm
        exact hratio
  have hfac_nonneg : 0 ≤ (-padePhiErrorConst n d) * ρ ^ (n + d + 1) := by
    have hnegC : 0 ≤ -padePhiErrorConst n d := by linarith
    exact mul_nonneg hnegC (pow_nonneg hρ.le _)
  simpa [A] using
    (calc
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
          (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₁) * I)) ^ (n + d + 1))) -
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
          (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₂) * I)) ^ (n + d + 1)))
          = (-padePhiErrorConst n d) * ρ ^ (n + d + 1) *
              (Real.sin (A * s₂) - Real.sin (A * s₁)) := by
                nlinarith [hmain₁, hmain₂]
      _ ≥ (-padePhiErrorConst n d) * ρ ^ (n + d + 1) * (A * (s₂ - s₁) / 2) := by
        gcongr
      _ = (-padePhiErrorConst n d) * A * ρ ^ (n + d + 1) * (s₂ - s₁) / 2 := by
        ring)

/-- Chord-length bound along the fixed-radius arc. -/
theorem arc_norm_sub_le_of_phase
    {ρ θ₀ s₁ s₂ : ℝ} (hρ : 0 ≤ ρ) :
    ‖(↑ρ : ℂ) * exp (↑(θ₀ + s₂) * I) - (↑ρ : ℂ) * exp (↑(θ₀ + s₁) * I)‖ ≤
      ρ * |s₂ - s₁| := by
  have h1 :
      (↑ρ : ℂ) * exp (↑(θ₀ + s₂) * I) - (↑ρ : ℂ) * exp (↑(θ₀ + s₁) * I) =
        (↑ρ : ℂ) * (exp (↑(θ₀ + s₂) * I) - exp (↑(θ₀ + s₁) * I)) := by
    ring
  rw [h1, norm_mul, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_nonneg hρ]
  apply mul_le_mul_of_nonneg_left _ hρ
  have h2 :
      exp (↑(θ₀ + s₂) * I) - exp (↑(θ₀ + s₁) * I) =
        exp (↑(θ₀ + s₁) * I) * (exp (↑(s₂ - s₁) * I) - 1) := by
    rw [show (↑(θ₀ + s₂) * I : ℂ) = ↑(θ₀ + s₁) * I + ↑(s₂ - s₁) * I by push_cast; ring]
    rw [exp_add]
    ring
  rw [h2, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  calc
    ‖exp (↑(s₂ - s₁) * I) - 1‖ = ‖exp (I * ↑(s₂ - s₁)) - 1‖ := by rw [mul_comm]
    _ ≤ ‖(s₂ - s₁ : ℝ)‖ := by
      simpa [mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s₂ - s₁))
    _ = |s₂ - s₁| := Real.norm_eq_abs _

/-- Cycle-345 topology seam sharpened to a fixed-radius uniqueness statement:
for sufficiently small radii, the odd down-arrow true slice has at most one zero. -/
private theorem oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
      ∀ s₁ ∈ Set.Icc (-ρ) ρ,
      ∀ s₂ ∈ Set.Icc (-ρ) ρ,
          oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
          oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
          s₁ = s₂ := by
  obtain ⟨K, δ₀, hK₀, hδ₀₀, hφ⟩ := padeR_exp_neg_local_bound n d
  obtain ⟨δQ, hδQ₀, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δmono, hδmono_pos, hδmono⟩ :
      ∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
        2 * ρ < δ₀ ∧ 2 * ρ < δQ ∧
        (n + d + 1 : ℝ) * ρ ≤ Real.pi / 3 ∧
        (-padePhiErrorConst n d) * (n + d + 1 : ℝ) >
          4 * K * (2 ^ (n + d + 2) + 1) * ρ := by
    let a : ℝ := δ₀ / 2
    let b : ℝ := δQ / 2
    let c : ℝ := (Real.pi / 3) / (n + d + 1 : ℝ)
    let d' : ℝ :=
      ((-padePhiErrorConst n d) * (n + d + 1 : ℝ)) /
        (4 * K * (2 ^ (n + d + 2) + 1))
    refine ⟨min a (min b (min c d')), ?_, ?_⟩
    · have hnegC : 0 < -padePhiErrorConst n d := by linarith
      dsimp [a, b, c, d']
      refine lt_min (half_pos hδ₀₀) ?_
      refine lt_min (half_pos hδQ₀) ?_
      refine lt_min ?_ ?_
      · positivity
      · exact div_pos (by positivity [hnegC]) (by positivity)
    · intro ρ hρ
      have hρa : ρ < a := lt_of_lt_of_le hρ.2 (min_le_left _ _)
      have hρb : ρ < b := lt_of_lt_of_le hρ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
      have hρc : ρ < c := lt_of_lt_of_le hρ.2
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hρd : ρ < d' := lt_of_lt_of_le hρ.2
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp [a] at hρa
        linarith
      · dsimp [b] at hρb
        linarith
      · dsimp [c] at hρc
        have hnd : 0 < (n + d + 1 : ℝ) := by positivity
        rw [lt_div_iff₀ hnd] at hρc
        linarith
      · dsimp [d'] at hρd
        have hden : 0 < 4 * K * (2 ^ (n + d + 2) + 1) := by positivity
        rw [lt_div_iff₀ hden] at hρd
        linarith
  refine ⟨δmono, hδmono_pos, ?_⟩
  intro ρ hρ s₁ hs₁ s₂ hs₂ hs₁_zero hs₂_zero
  by_cases h_eq : s₁ = s₂
  · exact h_eq
  have hρsmall' : (↑(n + d) + 1 : ℝ) * ρ ≤ Real.pi / 3 := by
    simpa using (hδmono ρ hρ).2.2.1
  have hcontra :
      ∀ {a b : ℝ}, a < b →
        a ∈ Set.Icc (-ρ) ρ →
        b ∈ Set.Icc (-ρ) ρ →
        oddDownArrowRadiusPhaseIm n d (ρ, a) = 0 →
        oddDownArrowRadiusPhaseIm n d (ρ, b) = 0 →
        False := by
    intro a b hab ha hb hza hzb
    have hmain :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
            ((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + a) * I)) ^ (n + d + 1)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
            ((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + b) * I)) ^ (n + d + 1)) ≥
          (-padePhiErrorConst n d) * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
      simpa using
        main_term_im_diff_bound_of_neg_errorConst
          n d hC hρ.1 hρsmall' ha hb hab
    let z₁ : ℂ := (↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + a) * I)
    let z₂ : ℂ := (↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + b) * I)
    let M₁ : ℂ := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₁ ^ (n + d + 1)
    let M₂ : ℂ := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₂ ^ (n + d + 1)
    let E₁ : ℂ := padeR n d z₁ * exp (-z₁) - M₁
    let E₂ : ℂ := padeR n d z₂ * exp (-z₂) - M₂
    have herr :
        ‖E₂ - E₁‖ ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      have hz₁mem : z₁ ∈ Metric.closedBall (0 : ℂ) ρ := by
        have hz₁norm : ‖z₁‖ = ρ := by
          simpa [z₁, oddDownArrowRadiusPhaseCenter] using
            norm_ofReal_mul_exp_I ρ (oddDownArrowRadiusPhaseCenter n d + a) hρ.1.le
        simpa [Metric.mem_closedBall, dist_eq_norm, hz₁norm]
      have hz₂mem : z₂ ∈ Metric.closedBall (0 : ℂ) ρ := by
        have hz₂norm : ‖z₂‖ = ρ := by
          simpa [z₂, oddDownArrowRadiusPhaseCenter] using
            norm_ofReal_mul_exp_I ρ (oddDownArrowRadiusPhaseCenter n d + b) hρ.1.le
        simpa [Metric.mem_closedBall, dist_eq_norm, hz₂norm]
      refine le_trans
        (error_lipschitz_on_ball_of_padeQ_ne_zero
          n d hK₀ hδ₀₀ hδQ₀ hρ.1 (hδmono ρ hρ).1 (hδmono ρ hρ).2.1 hQ hφ _ _
          hz₁mem hz₂mem)
        ?_
      have hcoeff_nonneg :
          0 ≤ K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) := by
        exact mul_nonneg (mul_nonneg hK₀.le (by positivity)) (pow_nonneg hρ.1.le _)
      refine le_trans
        (mul_le_mul_of_nonneg_left
          (arc_norm_sub_le_of_phase hρ.1.le)
          hcoeff_nonneg)
        ?_
      ring_nf
      gcongr
    have himerr :
        |Complex.im (E₂ - E₁)| ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      have himle : |Complex.im (E₂ - E₁)| ≤ ‖E₂ - E₁‖ := by
        simpa using Complex.abs_im_le_norm (E₂ - E₁)
      exact le_trans himle herr
    have hz₁ : Complex.im (M₁ + E₁) = 0 := by
      simpa [z₁, M₁, E₁, oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint] using hza
    have hz₂ : Complex.im (M₂ + E₂) = 0 := by
      simpa [z₂, M₂, E₂, oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint] using hzb
    have hmain_eq : Complex.im M₁ - Complex.im M₂ = Complex.im (E₂ - E₁) := by
      have hz₁' : Complex.im M₁ + Complex.im E₁ = 0 := by
        simpa using hz₁
      have hz₂' : Complex.im M₂ + Complex.im E₂ = 0 := by
        simpa using hz₂
      have himsub : Complex.im (E₂ - E₁) = Complex.im E₂ - Complex.im E₁ := by
        simp [sub_eq_add_neg]
      linarith
    have hmain_abs :
        |Complex.im M₁ - Complex.im M₂| ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      rw [hmain_eq]
      exact himerr
    have hsmall := (hδmono ρ hρ).2.2.2
    have hpow : 0 < ρ ^ (n + d + 1) := pow_pos hρ.1 _
    have hdist : 0 < b - a := sub_pos.mpr hab
    have hbound_pos :
        0 < K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      rw [abs_of_pos hdist]
      have htwo : 0 < (2 ^ (n + d + 2) + 1 : ℝ) := by positivity
      have hcoeff_pos : 0 < K * (2 ^ (n + d + 2) + 1 : ℝ) := by
        exact mul_pos hK₀ htwo
      exact mul_pos (mul_pos (mul_pos hcoeff_pos hpow) hρ.1) hdist
    have hsmall_mul :
        (-padePhiErrorConst n d * (↑(n + d) + 1 : ℝ)) * (ρ ^ (n + d + 1) * (b - a)) >
          (4 * (K * (2 ^ (n + d + 2) + 1) * ρ)) * (ρ ^ (n + d + 1) * (b - a)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_right hsmall (mul_pos hpow hdist))
    have hlead_gt :
        K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| <
          (-padePhiErrorConst n d) * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
      rw [abs_of_pos hdist]
      have htmp := hsmall_mul
      have hrew :
          (4 * (K * (2 ^ (n + d + 2) + 1) * ρ)) * (ρ ^ (n + d + 1) * (b - a)) =
            4 * (K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * (b - a)) := by
        ring
      rw [hrew] at htmp
      let B : ℝ := K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * (b - a)
      have hBpos : 0 < B := by
        simpa [B, abs_of_pos hdist] using hbound_pos
      have hBlt2B : B < 2 * B := by
        nlinarith [hBpos]
      have h2B : 2 * B <
          (-padePhiErrorConst n d) * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
        dsimp [B] at htmp ⊢
        nlinarith [htmp]
      exact lt_trans hBlt2B h2B
    have hlead_pos :
        K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| <
          Complex.im M₁ - Complex.im M₂ := by
      exact lt_of_lt_of_le hlead_gt hmain
    have hmain_nonneg : 0 ≤ Complex.im M₁ - Complex.im M₂ := by
      exact le_of_lt (lt_trans hbound_pos hlead_pos)
    rw [abs_of_nonneg hmain_nonneg] at hmain_abs
    linarith
  rcases lt_or_gt_of_ne h_eq with hlt | hgt
  · exact False.elim (hcontra hlt hs₁ hs₂ hs₁_zero hs₂_zero)
  · exact False.elim (hcontra hgt hs₂ hs₁ hs₂_zero hs₁_zero)

private theorem oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both_of_small_radius
    (n d : ℕ) {δ ρ δmono : ℝ}
    (hρsmall : ρ ∈ Set.Ioo (0 : ℝ) δmono)
    (hatMostOne :
      ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
        ∀ s₁ ∈ Set.Icc (-ρ) ρ,
        ∀ s₂ ∈ Set.Icc (-ρ) ρ,
          oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
          oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
          s₁ = s₂)
    (C : Set {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ})
    (_hCclopen : IsClopen C) :
    ∀ xL xR : {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ},
      xL ∈ C →
      xR ∈ Cᶜ →
      xL.1.1 = ρ →
      xR.1.1 = ρ →
      False := by
  intro xL xR hxLC hxRC hxLρ hxRρ
  rcases xL.2 with ⟨hxLw, hxLzero⟩
  rcases xR.2 with ⟨hxRw, hxRzero⟩
  let sL : ℝ := xL.1.2
  let sR : ℝ := xR.1.2
  have hxLpair : xL.1 = (ρ, sL) := by
    ext <;> simp [sL, hxLρ]
  have hxRpair : xR.1 = (ρ, sR) := by
    ext <;> simp [sR, hxRρ]
  have hsL : sL ∈ Set.Icc (-ρ) ρ := by
    simpa [sL, hxLρ] using hxLw.2
  have hsR : sR ∈ Set.Icc (-ρ) ρ := by
    simpa [sR, hxRρ] using hxRw.2
  have hsLzero : oddDownArrowRadiusPhaseIm n d (ρ, sL) = 0 := by
    simpa [hxLpair] using hxLzero
  have hsRzero : oddDownArrowRadiusPhaseIm n d (ρ, sR) = 0 := by
    simpa [hxRpair] using hxRzero
  have hsEq : sL = sR :=
    hatMostOne ρ hρsmall sL hsL sR hsR hsLzero hsRzero
  have hxEq_val : xL.1 = xR.1 := by
    apply Prod.ext
    · exact hxLρ.trans hxRρ.symm
    · simpa [sL, sR] using hsEq
  have hxEq : xL = xR := by
    apply Subtype.ext
    simpa using hxEq_val
  exact hxRC (hxEq ▸ hxLC)

theorem oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both
    (n d : ℕ) {δ ρ δmono : ℝ}
    (hρsmall : ρ ∈ Set.Ioo (0 : ℝ) δmono)
    (hatMostOne :
      ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
        ∀ s₁ ∈ Set.Icc (-ρ) ρ,
        ∀ s₂ ∈ Set.Icc (-ρ) ρ,
          oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
          oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
          s₁ = s₂)
    (C : Set {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ})
    (hCclopen : IsClopen C) :
    ∀ xL xR : {p // p ∈ oddDownArrowRadiusPhaseZeroSet n d δ},
      xL ∈ C →
      xR ∈ Cᶜ →
      xL.1.1 = ρ →
      xR.1.1 = ρ →
      False := by
  exact
    oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both_of_small_radius
      n d hρsmall hatMostOne C hCclopen

/-- Remaining no-stop seam: show that the connected component of `(0,0)` in the
compact odd-wedge zero set projects onto the full radius interval. The compact
zero-set and closed-projection infrastructure is now live above this theorem. -/
private theorem oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0,
      (∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p)) ∧
      Set.Icc (0 : ℝ) δ ⊆
        Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0) := by
  obtain ⟨δ0, hδ0, hre_wedge0, hsliceZero0⟩ :=
    oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst n d hC
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δmono, hδmono, hatMostOne⟩ :=
    oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst n d hC
  let δ : ℝ := min δ0 (min (δQ / 2) (δmono / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0 (lt_min (half_pos hδQ) (half_pos hδmono))
  have hδlt_Q : δ < δQ := by
    dsimp [δ]
    have hhalf : δQ / 2 < δQ := by linarith
    exact lt_of_le_of_lt
      (le_trans (min_le_right _ _) (min_le_left _ _))
      hhalf
  have hδlt_mono : δ < δmono := by
    dsimp [δ]
    have hhalf : δmono / 2 < δmono := by linarith
    exact lt_of_le_of_lt
      (le_trans (min_le_right _ _) (min_le_right _ _))
      hhalf
  have hre_wedge :
      ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p) :=
    by
      intro p hpw
      exact hre_wedge0 p
        ⟨⟨hpw.1.1, le_trans hpw.1.2 (min_le_left _ _)⟩, hpw.2⟩
  have hsliceZero :
      ∀ r ∈ Set.Icc (0 : ℝ) δ,
        ∃ s ∈ Set.Icc (-r) r,
          (r, s) ∈ oddDownArrowRadiusPhaseZeroSet n d δ := by
    intro r hr
    rcases hsliceZero0 r ⟨hr.1, le_trans hr.2 (min_le_left _ _)⟩ with
      ⟨s, hs, hslice⟩
    refine ⟨s, hs, ?_⟩
    rcases hslice with ⟨_, hsIm⟩
    exact ⟨⟨hr, hs⟩, hsIm⟩
  have hprojClosed :
      IsClosed
        (Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)) :=
    isClosed_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet
      n d hδ.le hQ hδlt_Q
  have hzero :
      (0, 0) ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
    mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  have hcompact :
      IsCompact (oddDownArrowRadiusPhaseZeroSet n d δ) :=
    isCompact_oddDownArrowRadiusPhaseZeroSet n d hQ hδlt_Q
  refine ⟨δ, hδ, hre_wedge, ?_⟩
  intro r hr
  by_contra hrmiss
  let K : Set (ℝ × ℝ) := oddDownArrowRadiusPhaseZeroSet n d δ
  let X := {p // p ∈ K}
  let x0 : X := ⟨(0, 0), hzero⟩
  rcases
      exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet
        n d hδ.le hQ hδlt_Q hrmiss with
    ⟨C, hCclopen, hx0C, hsliceC⟩
  have hprojClosed' :
      IsClosed (Prod.fst '' connectedComponentIn K (0, 0)) := by
    simpa [K] using hprojClosed
  have hcompact' : IsCompact K := by
    simpa [K] using hcompact
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hcompact'
  have hx0C' : x0 ∈ C := hx0C (by simp [x0])
  have hcoordCont : Continuous fun p : X => p.1.1 :=
    continuous_fst.comp continuous_subtype_val
  let L : Set ℝ := (fun p : X => p.1.1) '' C
  let R : Set ℝ := (fun p : X => p.1.1) '' Cᶜ
  have hLclosed : IsClosed L := by
    have hCcompact : IsCompact C := hCclopen.isClosed.isCompact
    simpa [L] using (hCcompact.image hcoordCont).isClosed
  have hRclosed : IsClosed R := by
    have hRcompact : IsCompact Cᶜ := hCclopen.compl.isClosed.isCompact
    simpa [R] using (hRcompact.image hcoordCont).isClosed
  have h0L : (0 : ℝ) ∈ L := by
    exact ⟨x0, hx0C', rfl⟩
  have hprojSubsetL : Prod.fst '' connectedComponentIn K (0, 0) ⊆ L := by
    intro ρ hρ
    rcases hρ with ⟨p, hpconn, rfl⟩
    let xp : X := ⟨p, connectedComponentIn_subset _ _ hpconn⟩
    have hxp_conn : xp ∈ connectedComponent x0 := by
      have hpimg : p ∈ Subtype.val '' connectedComponent x0 := by
        simpa [K, x0, connectedComponentIn_eq_image hzero] using hpconn
      rcases hpimg with ⟨y, hy, hyval⟩
      have hy_eq : y = xp := by
        apply Subtype.ext
        simpa using hyval
      exact hy_eq ▸ hy
    exact ⟨xp, hCclopen.connectedComponent_subset hx0C' hxp_conn, rfl⟩
  have hrR : r ∈ R := by
    rcases hsliceZero r hr with ⟨s, hs, hslice⟩
    let xr : X := ⟨(r, s), hslice⟩
    have hxrC : xr ∈ Cᶜ := hsliceC (by
      change ((⟨(r, s), hslice⟩ : X).1.1 = r)
      simp)
    exact ⟨xr, hxrC, rfl⟩
  have hcover : Set.Icc (0 : ℝ) δ ⊆ L ∪ R := by
    intro ρ hρ
    rcases hsliceZero ρ hρ with ⟨s, hs, hslice⟩
    let xρ : X := ⟨(ρ, s), hslice⟩
    by_cases hxρC : xρ ∈ C
    · exact Or.inl ⟨xρ, hxρC, rfl⟩
    · exact Or.inr ⟨xρ, by simpa using hxρC, rfl⟩
  have hLR :
      (Set.Icc (0 : ℝ) δ ∩ (L ∩ R)).Nonempty := by
    have hpre : IsPreconnected (Set.Icc (0 : ℝ) δ) := isPreconnected_Icc
    refine (isPreconnected_closed_iff.mp hpre) L R hLclosed hRclosed hcover ?_ ?_
    · exact ⟨0, by simp [hδ.le, h0L]⟩
    · exact ⟨r, by exact ⟨hr, hrR⟩⟩
  rcases hLR with ⟨ρ, hρIcc, hρL, hρR⟩
  rcases hρL with ⟨xρL, hxρLC, hρeqL⟩
  rcases hρR with ⟨xρR, hxρRC, hρeqR⟩
  have hρpos : 0 < ρ := by
    by_contra hρnpos
    have hρzero : ρ = 0 := by
      linarith [hρIcc.1]
    have hxρR_snd_zero : xρR.1.2 = 0 := by
      rcases xρR.2 with ⟨hxρRw, _hxρRzero⟩
      have hsρR : xρR.1.2 ∈ Set.Icc (-ρ) ρ := by
        simpa [hρeqR] using hxρRw.2
      have hs0 : xρR.1.2 ∈ Set.Icc (0 : ℝ) 0 := by
        simpa [hρzero] using hsρR
      rcases hs0 with ⟨hs0_lo, hs0_hi⟩
      linarith
    have hxρR_eq_x0 : xρR = x0 := by
      apply Subtype.ext
      show xρR.1 = x0.1
      apply Prod.ext
      · simpa [x0, hρzero] using hρeqR
      · simpa [x0] using hxρR_snd_zero
    exact hxρRC (hxρR_eq_x0.symm ▸ hx0C')
  have hρsmall : ρ ∈ Set.Ioo (0 : ℝ) δmono := by
    exact ⟨hρpos, lt_of_le_of_lt hρIcc.2 hδlt_mono⟩
  exact
    oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both
      n d hρsmall hatMostOne C hCclopen xρL xρR hxρLC hxρRC hρeqL hρeqR

/-- The remaining concrete continuation blocker after the cycle-335 refactor:
the odd down-arrow case still needs a genuine uniform strip / connected-support
construction near `θ = Real.pi / ((↑(n + d) + 1) : ℝ)`. -/
private theorem padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0, ∃ Z : Set (ℝ × ℝ),
      IsConnected Z ∧
        Z ⊆ {p : ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) δ ∧
            p.2 ∈ Set.Icc (-p.1) p.1 ∧
              let w : ℂ :=
                (↑p.1 : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + p.2) * I)
              Complex.im (padeR n d w * exp (-w)) = 0 ∧
                0 < Complex.re (padeR n d w * exp (-w))} ∧
        Set.Icc (0 : ℝ) δ ⊆ Prod.fst '' Z := by
  obtain ⟨δ, hδ, hre_wedge, hproj⟩ :=
    oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst n d hC
  let Z : Set (ℝ × ℝ) := connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)
  have hzero : (0, 0) ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
    mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  refine ⟨δ, hδ, Z, ?_, ?_, ?_⟩
  · exact isConnected_connectedComponentIn_iff.mpr hzero
  · intro p hpZ
    have hpK : p ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
      connectedComponentIn_subset _ _ hpZ
    rcases hpK with ⟨hpw, hpim⟩
    refine ⟨hpw.1, hpw.2, ?_, ?_⟩
    · simpa [oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter] using hpim
    · simpa [oddDownArrowRadiusPhaseValue, oddDownArrowRadiusPhasePoint,
        oddDownArrowRadiusPhaseCenter] using hre_wedge p hpw
  · simpa [Z] using hproj

/-- The remaining concrete continuation blocker after the cycle-335 refactor:
the odd down-arrow case still needs a genuine uniform strip / connected-support
construction near `θ = Real.pi / ((↑(n + d) + 1) : ℝ)`. -/
private theorem padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ z0 ∈ orderWeb (padeR n d), ∃ δ > 0,
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            ∃ s ∈ Set.Icc (-r) r,
              z =
                (↑r : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I) := by
  obtain ⟨δ, hδ, Z, hZconn, hZsub, hZproj⟩ :=
    padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst n d hC
  let θ0 : ℝ := Real.pi / ((↑(n + d) + 1) : ℝ)
  let f : ℝ × ℝ → ℂ := fun p =>
    (↑p.1 : ℂ) * exp (↑(θ0 + p.2) * I)
  let support : Set ℂ := f '' Z
  have hsupport_conn : IsConnected support := by
    refine hZconn.image f ?_
    exact Continuous.continuousOn (by
      continuity : Continuous f)
  have hsupport_web : support ⊆ orderWeb (padeR n d) := by
    intro z hz
    rcases hz with ⟨p, hpZ, rfl⟩
    rcases hZsub hpZ with ⟨_hp1, _hp2, him, hre⟩
    exact mem_orderWeb_of_im_zero_of_re_pos hre him
  have hzero_fst : (0 : ℝ) ∈ Prod.fst '' Z := by
    apply hZproj
    exact Set.left_mem_Icc.mpr hδ.le
  rcases hzero_fst with ⟨p0, hp0Z, hp0fst⟩
  have hp0r : p0.1 = 0 := by
    simpa using hp0fst
  have hzero_support : (0 : ℂ) ∈ support := by
    refine ⟨p0, hp0Z, ?_⟩
    simp [f, hp0r]
  have hsupport_comp :
      support ⊆ connectedComponentIn (orderWeb (padeR n d)) (0 : ℂ) :=
    hsupport_conn.2.subset_connectedComponentIn hzero_support hsupport_web
  refine ⟨0, padeR_mem_orderWeb_zero n d, δ, hδ, ?_⟩
  intro r hr
  have hr_mem : r ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  rcases hZproj hr_mem with ⟨p, hpZ, hpfst⟩
  have hpr : p.1 = r := by
    simpa using hpfst
  rcases hZsub hpZ with ⟨_hp1, hp2, _him, _hre⟩
  refine ⟨f p, hsupport_comp ⟨p, hpZ, rfl⟩, p.2, ?_, ?_⟩
  · simpa [hpr] using hp2
  · simp [f, θ0, hpr]

/-- The remaining concrete continuation blocker after the cycle-335 refactor:
the odd down-arrow case still needs a genuine uniform strip / connected-support
construction near `θ = Real.pi / ((↑(n + d) + 1) : ℝ)`. -/
private theorem padeR_odd_downArrowConnectedRayConeSupport_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    Nonempty
      (PadeRConnectedRayConeOrderWebSupport n d
        (Real.pi / ((↑(n + d) + 1) : ℝ))) := by
  obtain ⟨z0, hz0, δ, hδ, hcomponent⟩ :=
    padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst n d hC
  let θ0 : ℝ := Real.pi / ((↑(n + d) + 1) : ℝ)
  refine ⟨⟨connectedComponentIn (orderWeb (padeR n d)) z0,
    isConnected_connectedComponentIn_iff.mpr hz0,
    connectedComponentIn_subset _ _,
    ?_⟩⟩
  intro aperture haperture radius hradius
  let r : ℝ := min (δ / 2) (min (radius / 2) (aperture / 2))
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hδ) (lt_min (half_pos hradius) (half_pos haperture))
  have hr_lt_δ : r < δ := by
    dsimp [r]
    have hhalf : δ / 2 < δ := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hr_lt_radius : r < radius := by
    dsimp [r]
    have hhalf : radius / 2 < radius := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) hhalf
  have hr_lt_aperture : r < aperture := by
    dsimp [r]
    have hhalf : aperture / 2 < aperture := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hhalf
  rcases hcomponent r ⟨hr_pos, hr_lt_δ⟩ with
    ⟨z, hzcomp, s, hs, rfl⟩
  refine ⟨_, hzcomp, ?_⟩
  simpa [θ0] using
    exact_angle_arc_mem_rayConeNearOrigin θ0 aperture radius r r haperture
      ⟨hr_pos, hr_lt_radius⟩ hr_lt_aperture s hs

/-- The remaining concrete continuation blocker after the cycle-335 refactor:
the odd down-arrow case still needs a genuine uniform strip / connected-support
construction near `θ = Real.pi / ((↑(n + d) + 1) : ℝ)`. -/
theorem padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin
              (Real.pi / ((↑(n + d) + 1) : ℝ)) aperture radius := by
  obtain ⟨support⟩ :=
    padeR_odd_downArrowConnectedRayConeSupport_of_neg_errorConst n d hC
  obtain ⟨z0, hz0support, _hz0cone⟩ :=
    support.meets_rayConeNearOrigin 1 zero_lt_one 1 zero_lt_one
  have hz0 : z0 ∈ orderWeb (padeR n d) := support.support_subset_orderWeb hz0support
  have hsubset_comp :
      support.support ⊆ connectedComponentIn (orderWeb (padeR n d)) z0 :=
    support.support_connected.2.subset_connectedComponentIn
      hz0support support.support_subset_orderWeb
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  obtain ⟨z, hzsupport, hzcone⟩ :=
    support.meets_rayConeNearOrigin aperture haperture radius hradius
  exact ⟨z, hsubset_comp hzsupport, hzcone⟩

theorem padeR_even_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d 0 := by
  rcases
      padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeR_odd_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d
      (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  rcases
      padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeRDownArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨0, ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_pos_errorConst n d 0 hC
  · simpa using
      padeR_even_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
        n d hC

theorem padeRDownArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨Real.pi / ((↑(n + d) + 1) : ℝ), ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_neg_errorConst_oddAngle n d 0 hC
  · simpa using
      padeR_odd_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
        n d hC

theorem padeRDownArrowConnectedRayConeSupportInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowConnectedRayConeSupportInput n d data := by
  exact
    (padeRDownArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst n d data hC).toConnectedRayConeSupportInput

theorem padeRDownArrowConnectedRayConeSupportInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowConnectedRayConeSupportInput n d data := by
  exact
    (padeRDownArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst n d data hC).toConnectedRayConeSupportInput

theorem padeRDownArrowRayTrackingSupportInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowRayTrackingSupportInput n d data := by
  exact
    (padeRDownArrowConnectedRayConeSupportInput_of_pos_errorConst n d data hC).toRayTrackingSupportInput

theorem padeRDownArrowRayTrackingSupportInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowRayTrackingSupportInput n d data := by
  exact
    (padeRDownArrowConnectedRayConeSupportInput_of_neg_errorConst n d data hC).toRayTrackingSupportInput

theorem padeRDownArrowBranchTrackingInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowBranchTrackingInput n d data := by
  exact
    (padeRDownArrowRayTrackingSupportInput_of_pos_errorConst n d data hC).toTrackingInput

theorem padeRDownArrowBranchTrackingInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowBranchTrackingInput n d data := by
  exact
    (padeRDownArrowRayTrackingSupportInput_of_neg_errorConst n d data hC).toTrackingInput

theorem padeRDownArrowBranchTrackingInput_of_even_or_odd
    (n d : ℕ) (data : OrderArrowTerminationData) :
    PadeRDownArrowBranchTrackingInput n d data := by
  rcases Nat.even_or_odd d with hd | hd
  · exact
      padeRDownArrowBranchTrackingInput_of_pos_errorConst n d data
        (padePhiErrorConst_pos_of_even n d hd)
  · exact
      padeRDownArrowBranchTrackingInput_of_neg_errorConst n d data
        (padePhiErrorConst_neg_of_odd n d hd)
