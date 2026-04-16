import Mathlib

/-!
# Spectral bound for power-bounded operators

This file proves that a linear operator on a finite-dimensional complex vector space
has uniformly bounded iterates when all eigenvalues have norm ≤ 1 and all unit-circle
eigenvalues are semisimple (i.e., the maximal generalized eigenspace equals the eigenspace).

The proof proceeds by decomposing the space into generalized eigenspaces
(via `Module.End.iSup_maxGenEigenspace_eq_top`) and bounding T^n on each piece.
-/

open Polynomial Module.End

noncomputable section

variable {s : ℕ}

/-! ## Polynomial × geometric decay bound -/

/-- For |r| < 1 and fixed k, the sequence n^k * r^n is bounded. -/
lemma exists_bound_poly_geom (r : ℝ) (hr : r ∈ Set.Ico 0 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k * r ^ n ≤ C := by
  have h_test : Summable (fun n : ℕ => (n^k : ℝ) * r^n) := by
    refine' summable_of_ratio_norm_eventually_le _ _
    exact ( r + ( 1 - r ) / 2 )
    · linarith [ hr.2 ]
    · have h_ratio : ∃ N : ℕ, ∀ n ≥ N, |r| * (n + 1)^k / n^k ≤ r + (1 - r) / 2 := by
        have h_limit : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)^k / n^k) Filter.atTop (nhds 1) := by
          have h_limit : Filter.Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ))^k) Filter.atTop (nhds 1) := by
            convert Filter.Tendsto.pow ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) k
            · norm_num
            all_goals infer_instance
          refine h_limit.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ one_add_div ( by positivity ), div_pow ] )
        have := h_limit.const_mul r
        simpa [ abs_of_nonneg hr.1, mul_div_assoc ] using this.eventually ( ge_mem_nhds <| by linarith [ hr.2 ] )
      obtain ⟨ N, hN ⟩ := h_ratio
      filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0 ] with n hn hn'
      specialize hN n hn
      simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm, div_le_iff₀ ]
      convert mul_le_mul_of_nonneg_left hN ( pow_nonneg ( abs_nonneg r ) n ) using 1
      norm_cast; ring
  exact ⟨ ∑' n : ℕ, ( n ^ k : ℝ ) * r ^ n, tsum_nonneg fun n => mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( pow_nonneg hr.1 _ ), fun n => Summable.le_tsum h_test n fun _ _ => mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( pow_nonneg hr.1 _ ) ⟩

/-- For |μ| < 1 and fixed k, ∑_{j=0}^{k-1} C(n,j) * |μ|^{n-j} is bounded. -/
lemma exists_bound_binom_geom (μ : ℂ) (hμ : ‖μ‖ < 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∑ j ∈ Finset.range k,
      (n.choose j : ℝ) * ‖μ‖ ^ (n - j) ≤ C := by
  have h_bounded : ∀ j < k, ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ n : ℕ, (n.choose j : ℝ) * ‖μ‖^(n - j) ≤ Cj := by
    intro j hj
    obtain ⟨Cj, hCj⟩ : ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ n : ℕ, (n.choose j : ℝ) * ‖μ‖ ^ n ≤ Cj := by
      have h_bound : ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ n : ℕ, (n ^ j : ℝ) * ‖μ‖ ^ n ≤ Cj :=
        exists_bound_poly_geom ‖μ‖ ⟨ norm_nonneg μ, hμ ⟩ j
      refine' ⟨ h_bound.choose, h_bound.choose_spec.1, fun n => le_trans _ ( h_bound.choose_spec.2 n ) ⟩
      gcongr; norm_cast; exact Nat.choose_le_pow n j
    by_cases hμ_zero : μ = 0
    · use 1; simp [hμ_zero]
      intro n; by_cases h : n - j = 0 <;> simp +decide [ h ]
      cases le_total n j <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ]
      · cases eq_or_lt_of_le ‹_› <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ]
      · rw [ Nat.sub_eq_iff_eq_add ] at h <;> aesop
    · use Cj / ‖μ‖^j
      exact ⟨ div_nonneg hCj.1 ( pow_nonneg ( norm_nonneg μ ) _ ), fun n => if hn : n < j then by rw [ Nat.choose_eq_zero_of_lt hn ]; norm_num; exact div_nonneg hCj.1 ( pow_nonneg ( norm_nonneg μ ) _ ) else by rw [ le_div_iff₀ ( pow_pos ( norm_pos_iff.mpr hμ_zero ) _ ) ]; convert hCj.2 n using 1; rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( le_of_not_gt hn ) ] ⟩
  choose! C hC₁ hC₂ using h_bounded
  exact ⟨ ∑ j ∈ Finset.range k, C j, Finset.sum_nonneg fun _ _ => hC₁ _ ( Finset.mem_range.mp ‹_› ), fun n => Finset.sum_le_sum fun _ _ => hC₂ _ ( Finset.mem_range.mp ‹_› ) _ ⟩

/-! ## Binomial expansion for commuting operators -/

set_option maxHeartbeats 800000 in
/-- If (T - μ)^k v = 0, then T^n v = ∑_{j<k} C(n,j) μ^{n-j} (T-μ)^j v. -/
lemma pow_apply_eq_sum_of_genEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (μ : ℂ) (k : ℕ) (v : V)
    (hv : v ∈ (T.genEigenspace μ) (k : ℕ∞)) :
    ∀ n : ℕ, (T ^ n) v = ∑ j ∈ Finset.range k,
      (n.choose j : ℂ) • μ ^ (n - j) • ((T - μ • 1) ^ j) v := by
  introv
  induction' n with n ih generalizing v
  · cases k <;> simp_all +decide [ Finset.sum_range_succ' ]
  · have h_expand_step : T (∑ j ∈ Finset.range k, ((Nat.choose n j) : ℂ) • μ ^ (n - j) • ((T - μ • 1) ^ j) v) = ∑ j ∈ Finset.range k, ((Nat.choose n j) : ℂ) • μ ^ (n + 1 - j) • ((T - μ • 1) ^ j) v + ∑ j ∈ Finset.range k, ((Nat.choose n j) : ℂ) • μ ^ (n - j) • ((T - μ • 1) ^ (j + 1)) v := by
      simp +decide [ pow_succ', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, sub_smul, smul_sub ]
      simp +decide [ sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Finset.sum_add_distrib, smul_smul, pow_succ' ]
      rw [ neg_add_eq_zero ]
      refine' Finset.sum_congr rfl fun x hx => _
      by_cases h : n < x <;> simp_all +decide [ Nat.succ_sub, pow_succ, mul_assoc ]
      simp +decide [ Nat.choose_eq_zero_of_lt h ]
    have h_expand_step : ∑ j ∈ Finset.range k, ((Nat.choose n j) : ℂ) • μ ^ (n + 1 - j) • ((T - μ • 1) ^ j) v + ∑ j ∈ Finset.range k, ((Nat.choose n j) : ℂ) • μ ^ (n - j) • ((T - μ • 1) ^ (j + 1)) v = ∑ j ∈ Finset.range (k + 1), ((Nat.choose (n + 1) j) : ℂ) • μ ^ (n + 1 - j) • ((T - μ • 1) ^ j) v - ((Nat.choose n k) : ℂ) • μ ^ (n + 1 - k) • ((T - μ • 1) ^ k) v := by
      simp +decide [ Finset.sum_range_succ', Nat.choose_succ_succ ]
      have := Finset.sum_range_sub ( fun x => ( n.choose x : ℂ ) • μ ^ ( n + 1 - x ) • ( ( T - μ • 1 ) ^ x ) v ) k
      simp_all +decide [ add_smul, Finset.sum_add_distrib, pow_succ, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]
      grind
    simp_all +decide [ pow_succ', mul_assoc, mul_left_comm, Finset.sum_range_succ ]
    simp_all +decide [ Module.End.mem_genEigenspace_nat ]

/-! ## Norm bound on generalized eigenspaces -/

/-- On a generalized eigenspace for |μ| ≤ 1, the iterates T^n are bounded. -/
lemma norm_pow_le_on_maxGenEigenspace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : Module.End ℂ V) (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (k : ℕ) (v : V) (hv : v ∈ (T.genEigenspace μ) (k : ℕ∞))
    (h_simple : ‖μ‖ = 1 → k ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖(T ^ n) v‖ ≤ C * ‖v‖ := by
  by_cases h_case : ‖μ‖ < 1 ∨ k ≤ 1
  · cases' h_case with h_case h_case <;> simp_all +decide [ Module.End.genEigenspace ]
    · obtain ⟨C_binom, hC_binom⟩ : ∃ C_binom : ℝ, 0 ≤ C_binom ∧ ∀ n : ℕ, ∑ j ∈ Finset.range k, (Nat.choose n j : ℝ) * ‖μ‖ ^ (n - j) ≤ C_binom :=
        exists_bound_binom_geom μ h_case k
      have h_term_bound : ∀ n : ℕ, ‖(T ^ n) v‖ ≤ ∑ j ∈ Finset.range k, (Nat.choose n j : ℝ) * ‖μ‖ ^ (n - j) * ‖((T - μ • 1) ^ j) v‖ := by
        intro n
        have h_term_bound : ‖(T ^ n) v‖ ≤ ‖∑ j ∈ Finset.range k, (Nat.choose n j : ℂ) • μ ^ (n - j) • ((T - μ • 1) ^ j) v‖ := by
          rw [ pow_apply_eq_sum_of_genEigenspace ]
          simp_all +decide [ Module.End.genEigenspace ]
        refine' le_trans h_term_bound ( le_trans ( norm_sum_le _ _ ) _ )
        simp +decide [ norm_smul, mul_assoc ]
      obtain ⟨D, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ j < k, ‖((T - μ • 1) ^ j) v‖ ≤ D * ‖v‖ := by
        by_cases hv_zero : v = 0 <;> simp_all +decide [ Norm.norm ]
        · exact ⟨ 0, le_rfl ⟩
        · exact ⟨ ( ∑ j ∈ Finset.range k, ‖ ( ( T - μ • 1 ) ^ j ) v‖ ) / ‖v‖, div_nonneg ( Finset.sum_nonneg fun _ _ => norm_nonneg _ ) ( norm_nonneg _ ), fun j hj => by rw [ div_mul_cancel₀ _ ( norm_ne_zero_iff.mpr hv_zero ) ]; exact Finset.single_le_sum ( fun i _ => norm_nonneg ( ( ( T - μ • 1 ) ^ i ) v ) ) ( Finset.mem_range.mpr hj ) ⟩
      refine' ⟨ C_binom * D, mul_nonneg hC_binom.1 hD.1, fun n => le_trans ( h_term_bound n ) _ ⟩
      refine' le_trans ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( hD.2 j ( Finset.mem_range.mp hj ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( norm_nonneg _ ) _ ) ) ) _
      simpa only [ mul_assoc, Finset.sum_mul _ _ _ ] using mul_le_mul_of_nonneg_right ( hC_binom.2 n ) ( mul_nonneg hD.1 ( norm_nonneg v ) )
    · interval_cases k <;> simp_all +decide [ Module.End.mem_genEigenspace ]
      · exact ⟨ 0, le_rfl ⟩
      · have hv_ker : v ∈ (T - μ • 1).ker := by
          rw [ Submodule.mem_iSup_iff_exists_finsupp ] at hv
          obtain ⟨ f, hf, rfl ⟩ := hv; simp_all +decide [ Finsupp.sum ]
          rw [ ← Finset.sum_sub_distrib ]; refine' Finset.sum_eq_zero fun i hi => _; specialize hf i; rcases i with ( _ | _ | i ) <;> simp_all +decide [ pow_succ, sub_eq_iff_eq_add ]
        have hv_T : ∀ n : ℕ, (T ^ n) v = μ ^ n • v := by
          intro n; induction n <;> simp_all +decide [ pow_succ', mul_assoc, smul_smul ]
          rw [ sub_eq_zero.mp hv_ker, smul_smul, mul_comm ]
        exact ⟨ 1, zero_le_one, fun n => by rw [ hv_T n, norm_smul, norm_pow ]; exact mul_le_mul_of_nonneg_right ( pow_le_one₀ ( norm_nonneg _ ) hμ ) ( norm_nonneg _ ) ⟩
  · exact False.elim ( h_case <| Or.inl <| lt_of_le_of_ne hμ fun h => h_case <| Or.inr <| h_simple h )

/-! ## Connection to zero-stability -/

/-- The characteristic polynomial of a linear recurrence is nonzero. -/
lemma charPoly_ne_zero (E : LinearRecurrence ℂ) : E.charPoly ≠ 0 :=
  Polynomial.Monic.ne_zero E.charPoly_monic

/-- If μ is a root and the derivative doesn't vanish, rootMultiplicity = 1. -/
lemma rootMultiplicity_eq_one_of_root_deriv_ne_zero
    (p : ℂ[X]) (μ : ℂ) (hp : p ≠ 0)
    (hroot : p.IsRoot μ) (hderiv : p.derivative.eval μ ≠ 0) :
    p.rootMultiplicity μ = 1 := by
  have h1 : 0 < p.rootMultiplicity μ := (Polynomial.rootMultiplicity_pos hp).mpr hroot
  have h2 : ¬ (1 < p.rootMultiplicity μ) := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hp]
    exact fun ⟨_, h⟩ => hderiv h
  omega

/-! ## Maximal generalized eigenspace index bound -/

/-- If `p(T) = 0` and rootMultiplicity μ p = 1, then maxGenEigenspace μ = eigenspace μ. -/
lemma maxGenEigenspace_le_one_of_charPoly_simple
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (p : ℂ[X]) (hp : Polynomial.aeval T p = 0)
    (μ : ℂ) (hroot : p.rootMultiplicity μ = 1)
    (v : V) (hv : v ∈ T.maxGenEigenspace μ) :
    v ∈ T.eigenspace μ := by
  have h_zero : (T - μ • 1) ∘ₗ (aeval T (p /ₘ (X - C μ))) = 0 := by
    have h_div : p = (X - C μ) * (p /ₘ (X - C μ)) := by
      rw [ Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ]
      exact not_not.mp fun h => by rw [ Polynomial.rootMultiplicity_eq_zero ] at hroot <;> aesop
    rw [ h_div ] at hp
    simpa [ Polynomial.aeval_def ] using hp
  have h_inj : ∀ (N : ℕ), ∀ (v : V), v ∈ (T.genEigenspace μ) N → v ∈ LinearMap.range (aeval T (p /ₘ (X - C μ))) := by
    intro N v hv
    have h_inv : ∃ q : Polynomial ℂ, (p /ₘ (X - C μ)) * q - 1 ∈ Ideal.span { (X - C μ) ^ N } := by
      obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, p = (X - C μ) * q ∧ ¬(X - C μ) ∣ q := by
        have h_div : (X - C μ) ^ 1 ∣ p ∧ ¬(X - C μ) ^ 2 ∣ p :=
          ⟨ by simpa [ hroot ] using Polynomial.pow_rootMultiplicity_dvd p μ, by simpa [ hroot ] using fun h => absurd ( Polynomial.pow_rootMultiplicity_not_dvd ( show p ≠ 0 from by aesop_cat ) μ ) ( by aesop_cat ) ⟩
        obtain ⟨ q, rfl ⟩ := h_div.1
        exact ⟨ q, by ring, fun h => h_div.2 <| by simpa only [ pow_one, pow_two, mul_assoc ] using mul_dvd_mul_left _ h ⟩
      obtain ⟨r, hr⟩ : ∃ r : Polynomial ℂ, q * r - 1 ∈ Ideal.span { (X - C μ) ^ N } := by
        have h_inv : IsCoprime q ((X - C μ) ^ N) :=
          IsCoprime.pow_right ( IsCoprime.symm <| Polynomial.irreducible_X_sub_C μ |> fun h => h.coprime_iff_not_dvd.mpr hq.2 )
        rcases h_inv with ⟨ a, b, h ⟩
        exact ⟨ a, by rw [ Ideal.mem_span_singleton ]; exact ⟨ -b, by linear_combination' h ⟩ ⟩
      use r
      rw [ hq.1, Polynomial.divByMonic_eq_div _ ( Polynomial.monic_X_sub_C μ ) ]
      rwa [ mul_div_cancel_left₀ _ ( Polynomial.X_sub_C_ne_zero μ ) ]
    obtain ⟨ q, hq ⟩ := h_inv
    have h_inv_map : (aeval T ((p /ₘ (X - C μ)) * q - 1)) v = 0 := by
      rw [ Ideal.mem_span_singleton ] at hq
      obtain ⟨ r, hr ⟩ := hq
      simp_all +decide [ pow_add, mul_assoc, mul_left_comm, mul_comm ]
      have h_inv_map : ((T - (algebraMap ℂ (Module.End ℂ V)) μ) ^ N) v = 0 := by
        rw [ Module.End.mem_genEigenspace_nat ] at hv; aesop
      aesop
    simp_all +decide [ sub_eq_iff_eq_add ]
    exact ⟨ _, h_inv_map ⟩
  simp_all +decide [ Module.End.mem_genEigenspace, LinearMap.ext_iff ]
  obtain ⟨ l, hl ⟩ := hv; specialize h_inj l v l le_rfl hl; aesop

/-! ## Main spectral bound theorem -/

/-
On a finite-dimensional complex normed space, if every eigenvalue of T has
    ‖μ‖ ≤ 1 and every eigenvalue with ‖μ‖ = 1 has maxGenEigenspace = eigenspace,
    then T has uniformly bounded iterates.
-/
set_option maxHeartbeats 1600000 in
lemma uniformly_bounded_iterates_of_spectral_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V)
    (h_norm : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1)
    (h_simple : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ = 1 →
      T.maxGenEigenspace μ = T.eigenspace μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : V), ‖(T ^ n) v‖ ≤ M * ‖v‖ := by
  -- Let's choose any basis for V.
  obtain ⟨basis, hbasis⟩ : ∃ basis : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V, True := by
    exact ⟨ Module.finBasis ℂ V, trivial ⟩;
  -- For each basis vector $b_i$, we have $\|T^n b_i\| \leq C_i$ for some constant $C_i$.
  have h_bound_basis : ∀ i : Fin (Module.finrank ℂ V), ∃ C_i : ℝ, 0 ≤ C_i ∧ ∀ n : ℕ, ‖(T ^ n) (basis i)‖ ≤ C_i := by
    intro i
    have h_decomp : ∃ (μs : Finset ℂ) (v : ℂ → V), basis i = ∑ μ ∈ μs, v μ ∧ ∀ μ ∈ μs, v μ ∈ T.maxGenEigenspace μ := by
      have h_decomp : basis i ∈ ⨆ μ, T.maxGenEigenspace μ := by
        rw [ Module.End.iSup_maxGenEigenspace_eq_top ] ; aesop;
      rw [ Submodule.mem_iSup_iff_exists_finsupp ] at h_decomp;
      obtain ⟨ f, hf₁, hf₂ ⟩ := h_decomp; exact ⟨ f.support, fun μ => f μ, hf₂.symm, fun μ hμ => hf₁ μ ⟩ ;
    obtain ⟨ μs, v, hv₁, hv₂ ⟩ := h_decomp
    have h_bound_v : ∀ μ ∈ μs, ∃ C_μ : ℝ, 0 ≤ C_μ ∧ ∀ n : ℕ, ‖(T ^ n) (v μ)‖ ≤ C_μ * ‖v μ‖ := by
      intro μ hμ
      by_cases hμ_eigen : T.HasEigenvalue μ
      generalize_proofs at *; (
      by_cases hμ_norm : ‖μ‖ = 1 <;> simp_all +decide [ Module.End.HasUnifEigenvector ];
      · have h_eigenspace : v μ ∈ T.eigenspace μ := by
          have heq := h_simple μ hμ_eigen hμ_norm
          have h_in_max : v μ ∈ T.maxGenEigenspace μ :=
            (Module.End.mem_maxGenEigenspace T μ (v μ)).mpr (hv₂ μ hμ)
          rw [heq] at h_in_max
          exact h_in_max
        generalize_proofs at *; (
        use 1; simp [h_eigenspace];
        intro n; induction' n with n ih <;> simp_all +decide [ pow_succ', Module.End.mem_eigenspace_iff ] ;
        -- Since $T$ is linear, we have $T((T^n)(v μ)) = (T^n)(T(v μ))$.
        have h_linear : T ((T ^ n) (v μ)) = (T ^ n) (T (v μ)) := by
          exact Nat.recOn n ( by simp +decide ) fun n ihn => by simp +decide [ *, pow_succ' ] ;
        generalize_proofs at *; (
        simp_all +decide [ norm_smul ]));
      · have := norm_pow_le_on_maxGenEigenspace T μ ( h_norm μ hμ_eigen ) ( Classical.choose ( hv₂ μ hμ ) ) ( v μ ) ( by
          have := Classical.choose_spec ( hv₂ μ hμ ) ; simp_all +decide [ Module.End.genEigenspace ] ;
          exact Submodule.mem_iSup_of_mem ( Classical.choose ( hv₂ μ hμ ) ) ( Submodule.mem_iSup_of_mem le_rfl this ) ) ( by
          intro h_eq; exfalso; exact hμ_norm h_eq )
        generalize_proofs at *; (
        exact this));
      simp_all +decide [ Module.End.HasUnifEigenvector ];
      obtain ⟨ k, hk ⟩ := hv₂ μ hμ
      have h_zero : v μ = 0 := by
        contrapose! hμ_eigen; simp_all +decide [ Module.End.HasUnifEigenvalue ] ;
        simp_all +decide [ Submodule.eq_bot_iff ];
        induction' k with k ih generalizing v <;> simp_all +decide [ pow_succ', sub_smul ];
        grind
      use 0
      simp [h_zero]
    generalize_proofs at *; (
    choose! C hC₁ hC₂ using h_bound_v; use ∑ μ ∈ μs, C μ * ‖v μ‖; simp_all +decide [ Finset.sum_mul _ _ _ ] ;
    exact ⟨ Finset.sum_nonneg fun μ hμ => mul_nonneg ( hC₁ μ hμ ) ( norm_nonneg _ ), fun n => le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun μ hμ => hC₂ μ hμ n ) ⟩);
  choose C hC_nonneg hC_bound using h_bound_basis;
  -- By the properties of the norm, we can bound the norm of $T^n v$ by the sum of the norms of $T^n b_i$.
  have h_norm_bound : ∀ n : ℕ, ∀ v : V, ‖(T ^ n) v‖ ≤ ∑ i : Fin (Module.finrank ℂ V), ‖(basis.repr v) i‖ * C i := by
    intro n v
    have h_decomp : (T ^ n) v = ∑ i : Fin (Module.finrank ℂ V), (basis.repr v) i • (T ^ n) (basis i) := by
      induction' n with n ih <;> simp_all +decide [ pow_succ', map_sum, map_smul ];
    exact h_decomp.symm ▸ le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun i _ => by simpa [ norm_smul ] using mul_le_mul_of_nonneg_left ( hC_bound i n ) ( norm_nonneg _ ) );
  -- By the properties of the norm, we can bound the norm of $v$ by the sum of the norms of its components.
  have h_norm_v_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ v : V, ∑ i : Fin (Module.finrank ℂ V), ‖(basis.repr v) i‖ ≤ D * ‖v‖ := by
    have h_norm_v_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ v : V, ∑ i : Fin (Module.finrank ℂ V), ‖(basis.repr v) i‖ ≤ D * ‖v‖ := by
      have h_linear_map : ∃ f : V →L[ℂ] Fin (Module.finrank ℂ V) → ℂ, ∀ v : V, f v = basis.repr v := by
        exact ⟨ basis.equivFun.toContinuousLinearMap, fun v => rfl ⟩
      obtain ⟨ f, hf ⟩ := h_linear_map;
      have := f.bound;
      obtain ⟨ C, hC₀, hC ⟩ := this; use C * ( Module.finrank ℂ V ) ; refine' ⟨ mul_nonneg hC₀.le ( Nat.cast_nonneg _ ), fun v => _ ⟩ ; specialize hC v; simp_all +decide [ Norm.norm ] ;
      refine' le_trans ( Finset.sum_le_sum fun i _ => show Real.sqrt ( Complex.normSq ( basis.repr v i ) ) ≤ C * ‖v‖ from _ ) _;
      · refine' le_trans _ hC;
        exact le_trans ( by simp +decide [ Complex.normSq_eq_norm_sq ] ) ( Finset.le_sup ( f := fun b => ‖basis.repr v b‖₊ ) ( Finset.mem_univ i ) );
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact h_norm_v_bound;
  obtain ⟨ D, hD_nonneg, hD_bound ⟩ := h_norm_v_bound;
  refine' ⟨ D * ∑ i, C i, mul_nonneg hD_nonneg ( Finset.sum_nonneg fun _ _ => hC_nonneg _ ), fun n v => le_trans ( h_norm_bound n v ) _ ⟩;
  rw [ mul_right_comm, Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( hD_bound v |> le_trans ( Finset.single_le_sum ( fun i _ => norm_nonneg ( basis.repr v i ) ) ( Finset.mem_univ i ) ) ) ( hC_nonneg i )

end
