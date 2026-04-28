import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Order

/-!
# Butcher §142 — Powers of matrices

This file collects the entities of subsection 142 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

So far this file contains Definitions 142A (power-boundedness) and 142B
(convergent matrix), plus the directional fragments of Theorem 142D
that are reachable in current Mathlib. Mathlib (as of `v4.28.0`) does
not provide Jordan canonical form or a Schur upper-triangular
decomposition, so the (ii) ⇒ (iii), (iii) ⇒ (iv), and the standalone
(i) ⇒ (iv) and (ii) ⇒ (iv) directions are deferred — see
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
Jordan/Schur structure but the middle steps do not.  In this file we
formalise the two directions that are reachable without that
infrastructure:

* `convergent_imp_minpoly_roots_lt_one`  — (i) ⇒ (ii)
* `similar_norm_lt_one_imp_convergent`   — (iv) ⇒ (i)

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

end ConvergenceCharacterizations

end OpenMath.Chapter1.Section142
