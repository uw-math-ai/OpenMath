import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Order

/-!
# Butcher §142 — Powers of matrices

This file collects the entities of subsection 142 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

So far this file contains Definitions 142A (power-boundedness) and 142B
(convergent matrix), plus the (i) ⇔ (ii) fragment of Theorem 142D —
the equivalence of convergence with all roots of the minimal polynomial
lying in the open unit disc.  The reverse direction (ii) ⇒ (i) routes
through Mathlib's spectral-radius and Gelfand-formula API.  Mathlib (as
of `v4.28.0`) does not provide Jordan canonical form or a Schur
upper-triangular decomposition, so the (ii) ⇒ (iii), (iii) ⇒ (iv), and
the standalone (i) ⇒ (iv), (ii) ⇒ (iv) directions are deferred — see
`.prover-state/issues/jordan_canonical_form_missing.md`.
-/

namespace OpenMath.Chapter1.Section142

open Filter Topology

/-- Butcher §142, Definition 142A — *power-boundedness* (a.k.a. *stable* matrix).

The textbook statement (Butcher 2008, p. 67):

> A square matrix `A` is *stable* if there exists a constant `C` such that for
> all `n = 0, 1, 2, …`, `‖A^n‖ ≤ C`.
>
> This property is often referred to as *power-boundedness*.

We follow the convention from `def:110A` and expose Butcher's "there exists a
constant `C`" as a *parameter* `M : ℝ`; the existential variant
`∃ M, PowerBounded M a` is recoverable downstream when needed.

The carrier is generalised from "square matrix" to an arbitrary
`SeminormedRing`. The Butcher instance is recovered by choosing
`A := Matrix n n ℝ` (or `Matrix n n ℂ`) with any submultiplicative matrix
norm — e.g. `Matrix.linftyOpNormedRing` from `Mathlib.Analysis.Matrix.Normed`,
or the Frobenius / spectral-radius-induced norm. The textbook is silent on
which matrix norm to use, and the predicate is norm-equivalence-invariant up
to changing the bound `M` (matrix norms on a finite-dimensional space are
all equivalent), so generalising the carrier rather than committing to a
specific matrix-norm definition is faithful to the textbook.

We deliberately do **not** define power-boundedness via spectral radius,
minimal polynomial, or Jordan normal form — those are characterization
*theorems* (`thm:142C`, `thm:142D`, `thm:142E`), not the definition. -/
def PowerBounded {A : Type*} [SeminormedRing A] (M : ℝ) (a : A) : Prop :=
  ∀ k : ℕ, ‖a ^ k‖ ≤ M

/-- Butcher §142, Definition 142B — *convergent* matrix.

The textbook statement (Butcher 2008, p. 67):

> A square matrix `A` is *convergent* if `lim_{n → ∞} A^n = 0`.

We use `Filter.Tendsto … atTop (𝓝 0)` — Mathlib's canonical spelling of
"the sequence has limit zero". The carrier is generalised from "square
matrix" to a `SeminormedRing`, matching `def:142A`'s carrier so that the
two definitions interoperate with the same matrix-norm instances. The
Butcher textbook instance is recovered exactly as for `PowerBounded`.

We deliberately do **not** define `Convergent` via spectral radius < 1,
the minimal polynomial having all roots in the open unit disc, the
Jordan form having diagonal entries in the open unit disc, or the
existence of a similarity making the operator norm strictly less than 1.
Each of those is one of the *equivalent characterizations* of
convergence (Butcher's Theorem 142D); encoding any of them as the
definition would make 142D a tautology. The definition must remain
`lim_{n → ∞} a^n = 0` verbatim. -/
def Convergent {A : Type*} [SeminormedRing A] (a : A) : Prop :=
  Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)

/-! ### Theorem 142D — directional characterizations of convergence

Butcher's Theorem 142D (Butcher 2008, p. 68) states the equivalence of
four conditions for an `m × m` matrix `A`:

> (i)   `A` is convergent.
> (ii)  The minimal polynomial of `A` has all its zeros in the open
>       unit disc.
> (iii) The Jordan canonical form of `A` has all its diagonal elements
>       in the open unit disc.
> (iv)  There exists a non-singular matrix `S` such that
>       `‖S⁻¹ A S‖_∞ < 1`.

Mathlib (as of `v4.28.0`) does not yet provide Jordan canonical form,
nor a Schur upper-triangular decomposition.  Butcher's proof goes
(i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i); the first and last steps avoid
Jordan/Schur structure but the middle steps do not.  We instead close
the (ii) ⇒ (i) gap directly through Mathlib's spectral-radius / Gelfand-
formula API, packaging the four reachable items:

* `convergent_imp_minpoly_roots_lt_one`     — (i) ⇒ (ii)
* `minpoly_roots_lt_one_imp_convergent`     — (ii) ⇒ (i)
* `convergent_iff_minpoly_roots_lt_one`     — (i) ⇔ (ii) packaging
* `similar_norm_lt_one_imp_convergent`      — (iv) ⇒ (i)

The Jordan-form clause (iii) and the directions (ii) ⇒ (iv) and
(i) ⇒ (iv) are tracked in
`.prover-state/issues/jordan_canonical_form_missing.md`. -/

section ConvergenceCharacterizations

open scoped Matrix.Norms.Operator
open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Helper bridge: a root of the minimal polynomial of a matrix `A` is
an *eigenvalue* of `A` in the matrix-vector sense — there is a nonzero
vector `v` such that `A *ᵥ v = μ • v`.

This bridges `Polynomial.IsRoot (minpoly ℂ A) μ` (a polynomial
property) to the matrix-vector equation Butcher uses informally. The
bridge runs through `Matrix.toLin'` and `Mathlib`'s
`Module.End.HasEigenvalue` API. -/
theorem matrix_minpoly_root_is_eigenvalue
    (A : Matrix m m ℂ) {μ : ℂ}
    (hμ : (minpoly ℂ A).IsRoot μ) :
    ∃ v : m → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  have h_eigenvalue : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    convert Module.End.hasEigenvalue_of_isRoot _;
    · infer_instance;
    · infer_instance;
    · convert hμ using 1;
      exact minpoly_toLin' A;
  obtain ⟨ v, hv ⟩ := h_eigenvalue.exists_hasEigenvector;
  exact ⟨ v, hv.2, by simpa [ funext_iff ] using hv.1 ⟩

/-- Helper: matrix powers act on an eigenvector by the corresponding
power of the eigenvalue, `A^n *ᵥ v = μ^n • v`.

This is the matrix analogue of `Module.End.HasEigenvector.pow_apply`. -/
theorem matrix_pow_mulVec_of_eigenvector
    (A : Matrix m m ℂ) {μ : ℂ} {v : m → ℂ}
    (hv : A *ᵥ v = μ • v) (n : ℕ) :
    (A ^ n) *ᵥ v = (μ ^ n) • v := by
  induction n <;> simp_all +decide [ pow_succ' ];
  simp_all +decide [ ← Matrix.mulVec_mulVec ];
  rw [ Matrix.mulVec_smul, hv, smul_smul, mul_comm ]

/-- Butcher §142, Theorem 142D — direction (i) ⇒ (ii).

If the matrix `A` is convergent (`A^n → 0` in the operator norm),
then every root of its minimal polynomial lies in the open unit disc.

Butcher's argument: an eigenvector `v` for an eigenvalue `μ` with
`|μ| ≥ 1` would force `‖A^n‖ · ‖v‖ ≥ ‖A^n *ᵥ v‖ = |μ|^n · ‖v‖ ≥ ‖v‖`,
contradicting `A^n → 0`. -/
theorem convergent_imp_minpoly_roots_lt_one
    (A : Matrix m m ℂ) (hA : Convergent A) :
    ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1 := by
  intro μ hμ;
  obtain ⟨v, hv_ne_zero, hv_eigen⟩ : ∃ v : m → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v :=
    matrix_minpoly_root_is_eigenvalue A ( by aesop );
  have h_pow_mulVec : ∀ n : ℕ, (A ^ n) *ᵥ v = (μ ^ n) • v :=
    fun n => matrix_pow_mulVec_of_eigenvector A hv_eigen n;
  have h_pow_mulVec_zero : Filter.Tendsto (fun n : ℕ => (A ^ n) *ᵥ v) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.comp ( show Filter.Tendsto ( fun x : Matrix m m ℂ => x *ᵥ v ) ( nhds 0 ) ( nhds 0 ) from ?_ ) hA using 1;
    exact Continuous.tendsto' ( continuous_id.matrix_mulVec continuous_const ) _ _ ( by simp +decide );
  contrapose! h_pow_mulVec_zero;
  simp_all +decide [ Metric.tendsto_nhds ];
  exact ⟨ ‖v‖, norm_pos_iff.mpr hv_ne_zero, fun n => ⟨ n, le_rfl, by rw [ norm_smul, norm_pow ] ; exact le_mul_of_one_le_left ( norm_nonneg _ ) ( one_le_pow₀ h_pow_mulVec_zero ) ⟩ ⟩

/-- Helper: the conjugation identity `A^n = S * (S⁻¹ A S)^n * S⁻¹`,
phrased as `S * B^n * S⁻¹ = A^n` where `B = S⁻¹ A S`. -/
theorem mul_pow_conj_eq_pow
    (A : Matrix m m ℂ) (S : (Matrix m m ℂ)ˣ) (n : ℕ) :
    (S : Matrix m m ℂ) *
        ((((S⁻¹ : (Matrix m m ℂ)ˣ) : Matrix m m ℂ) * A * (S : Matrix m m ℂ)) ^ n) *
        ((S⁻¹ : (Matrix m m ℂ)ˣ) : Matrix m m ℂ) = A ^ n := by
  induction n <;> simp +decide [ *, pow_succ, mul_assoc ];
  simp_all +decide [ ← mul_assoc, ← ‹_› ]

/-- Butcher §142, Theorem 142D — direction (iv) ⇒ (i).

If there exists a non-singular matrix `S` such that `‖S⁻¹ A S‖_∞ < 1`,
then `A` is convergent.  Butcher's argument: for `B = S⁻¹ A S`,
`A^n = S B^n S⁻¹` so `‖A^n‖ ≤ ‖S‖ ‖S⁻¹‖ ‖B‖^n → 0`. -/
theorem similar_norm_lt_one_imp_convergent
    (A : Matrix m m ℂ)
    (h : ∃ S : (Matrix m m ℂ)ˣ,
        ‖((S⁻¹ : (Matrix m m ℂ)ˣ) : Matrix m m ℂ) * A * (S : Matrix m m ℂ)‖ < 1) :
    Convergent A := by
  revert h;
  simp +decide only [Convergent];
  rintro ⟨ S, hS ⟩;
  have h_lim : Filter.Tendsto (fun n => (S⁻¹ * A * S : Matrix m m ℂ) ^ n) Filter.atTop (nhds 0) := by
    convert tendsto_pow_atTop_nhds_zero_of_norm_lt_one hS;
  convert Tendsto.const_mul ( S : Matrix m m ℂ ) ( h_lim.mul_const ( S⁻¹ : Matrix m m ℂ ) ) using 2;
  · induction ‹_› <;> simp_all +decide [ pow_succ, mul_assoc ];
  · simp +decide

/-! ### Direction (ii) ⇒ (i) via the Gelfand formula

Butcher's direction (ii) ⇒ (i) goes through (iii) ⇒ (iv) which we cannot
formalise yet (no Jordan form in Mathlib).  We instead route (ii) ⇒ (i)
directly via Mathlib's spectral-radius API:

* every spectrum element of `A` is a root of `minpoly ℂ A`
  (`Matrix.minpoly_dvd_charpoly` + `Matrix.mem_spectrum_iff_isRoot_charpoly`),
* hence `‖z‖ < 1` for every `z ∈ spectrum ℂ A`,
* hence `spectralRadius ℂ A < 1` (`spectrum.spectralRadius_lt_of_forall_lt`),
* hence `‖A^n‖ → 0` via Gelfand's formula
  (`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`),
* hence `A^n → 0`.

The bridges all live in `Mathlib.Analysis.Normed.Algebra.GelfandFormula`
and require `Matrix.Norms.Operator` to expose the `linftyOpNormedRing` /
`linftyOpNormedAlgebra` instances on `Matrix m m ℂ`. -/

/-- Spectrum elements of a square matrix `A` over a field are roots of
`minpoly K A`.

Proof: `μ ∈ spectrum K A ↔ A.charpoly.IsRoot μ` over a field
(`Matrix.mem_spectrum_iff_isRoot_charpoly`); we then go through the
End-side `hasEigenvalue_iff_isRoot` (using `minpoly_toLin'`) by way of
the eigenvector bridge already established in
`matrix_minpoly_root_is_eigenvalue`'s proof.  More directly, every
spectrum element is an eigenvalue, hence a root of `minpoly`. -/
private theorem matrix_mem_spectrum_imp_isRoot_minpoly
    (A : Matrix m m ℂ) {μ : ℂ}
    (h : μ ∈ spectrum ℂ A) : (minpoly ℂ A).IsRoot μ := by
  have h1 : μ ∈ spectrum ℂ (Matrix.toLinAlgEquiv' (R := ℂ) A) := by
    rwa [AlgEquiv.spectrum_eq]
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at h1
  rw [Module.End.hasEigenvalue_iff_isRoot] at h1
  convert h1 using 1
  exact (Matrix.minpoly_toLin' A).symm

/-- Spectral-radius bound from a uniform bound on minimal-polynomial roots.

If every root of `minpoly ℂ A` lies in the open unit disc, then
`spectralRadius ℂ A < 1`.  This combines
`matrix_mem_spectrum_imp_isRoot_minpoly` with
`spectrum.spectralRadius_lt_of_forall_lt` (which requires
`Matrix m m ℂ` to be `Nontrivial`, equivalently `[Nonempty m]`). -/
private theorem matrix_spectralRadius_lt_one_of_minpoly_roots
    [Nonempty m]
    (A : Matrix m m ℂ)
    (h : ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1) :
    spectralRadius ℂ A < 1 := by
  convert spectrum.spectralRadius_lt_of_forall_lt A _;
  exact fun z hz => by
    simpa [← NNReal.coe_lt_coe] using
      h z (Polynomial.mem_roots (minpoly.ne_zero (Matrix.isIntegral A)) |>.2 <|
        matrix_mem_spectrum_imp_isRoot_minpoly A hz)

/-- Gelfand corollary: `spectralRadius ℂ A < 1` implies `A` is convergent.

Pick `r ∈ (spectralRadius A, 1)`; Gelfand's formula yields
`‖A^n‖^(1/n) → spectralRadius A < r`, so `‖A^n‖ ≤ r^n` eventually,
hence `‖A^n‖ → 0`, hence `A^n → 0`. -/
private theorem matrix_convergent_of_spectralRadius_lt_one
    [Nonempty m]
    (A : Matrix m m ℂ) (h : spectralRadius ℂ A < 1) :
    Convergent A := by
  have := @spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius;
  convert this A using 1;
  constructor <;> intro h <;>
    rw [← ENNReal.tendsto_toReal_iff] at * <;> simp_all +decide [Convergent];
  · convert ENNReal.tendsto_toReal (show (spectralRadius ℂ A) ≠ ⊤ from ?_) |>
      Filter.Tendsto.comp <| this A using 1;
    exact ne_of_lt (lt_of_lt_of_le ‹_› (by norm_num));
  · exact ne_of_lt (lt_of_lt_of_le ‹_› (by norm_num));
  · have h_lim_zero : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ᶠ n in Filter.atTop, ‖A ^ n‖ ≤ r ^ n := by
      obtain ⟨r, hr₀, hr₁⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (spectralRadius ℂ A).toReal < r := by
        by_cases h₂ : (spectralRadius ℂ A).toReal < 1;
        · exact ⟨(spectralRadius ℂ A |> ENNReal.toReal) / 2 + 1 / 2,
            by linarith [show 0 ≤ (spectralRadius ℂ A |> ENNReal.toReal) by positivity],
            by linarith, by linarith⟩;
        · cases h : spectralRadius ℂ A <;> simp_all +decide [ENNReal.toReal];
      have := h.eventually (gt_mem_nhds hr₁.2);
      refine' ⟨r, hr₀, hr₁.1, this.mono fun n hn => _⟩;
      rcases eq_or_ne n 0 with rfl | hn' <;> simp_all +decide;
      convert pow_le_pow_left₀ (by positivity) hn.le n using 1;
      rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        inv_mul_cancel₀ (by positivity), ENNReal.rpow_one];
      norm_num;
    exact squeeze_zero_norm'
      (by filter_upwards [h_lim_zero.choose_spec.2.2] with n hn; simpa using hn)
      (tendsto_pow_atTop_nhds_zero_of_lt_one h_lim_zero.choose_spec.1.le
        h_lim_zero.choose_spec.2.1);
  · exact ne_of_lt (lt_of_lt_of_le h le_top)

/-- Butcher §142, Theorem 142D — direction (ii) ⇒ (i).

If every root of the minimal polynomial of `A` lies in the open unit
disc, then `A` is convergent.

The proof routes through Mathlib's spectral-radius API: the spectrum of
`A` is contained in the roots of `minpoly ℂ A`
(`matrix_mem_spectrum_imp_isRoot_minpoly`), so a strict bound on the
roots gives `spectralRadius ℂ A < 1`, and Gelfand's formula then forces
`‖A^n‖ → 0`.

The empty-`m` case is handled separately because Mathlib's
`spectrum.spectralRadius_lt_of_forall_lt` requires `[Nontrivial A]`,
which fails for the trivial matrix algebra over an empty index. -/
theorem minpoly_roots_lt_one_imp_convergent
    (A : Matrix m m ℂ)
    (h : ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1) :
    Convergent A := by
  cases isEmpty_or_nonempty m;
  · exact tendsto_const_nhds.congr fun n => by ext i; exact isEmptyElim i;
  · exact matrix_convergent_of_spectralRadius_lt_one A
      (matrix_spectralRadius_lt_one_of_minpoly_roots A h)

/-- Butcher §142, Theorem 142D — clauses (i) ⇔ (ii).

A square complex matrix `A` is convergent (`A^n → 0`) if and only if
every root of its minimal polynomial lies in the open unit disc.

This packages cycle 005's `convergent_imp_minpoly_roots_lt_one`
((i) ⇒ (ii), via the eigenvector growth argument) with the
spectral-radius / Gelfand route for the converse
(`minpoly_roots_lt_one_imp_convergent`, (ii) ⇒ (i)).

The full 4-way TFAE of Butcher's Theorem 142D is still blocked on
Jordan canonical form and Schur triangularization; see
`.prover-state/issues/jordan_canonical_form_missing.md`. -/
theorem convergent_iff_minpoly_roots_lt_one
    (A : Matrix m m ℂ) :
    Convergent A ↔ ∀ μ : ℂ, μ ∈ (minpoly ℂ A).roots → ‖μ‖ < 1 :=
  ⟨convergent_imp_minpoly_roots_lt_one A,
   minpoly_roots_lt_one_imp_convergent A⟩

end ConvergenceCharacterizations

end OpenMath.Chapter1.Section142
