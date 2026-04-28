# Issue: Mathlib lacks Jordan canonical form for `thm:142D`

## Blocker

Butcher's Theorem 142D (Numerical Methods for ODEs, 3rd ed., p. 68)
asserts the equivalence of four conditions for an `m × m` matrix `A`:

> (i)   `A` is convergent.
> (ii)  The minimal polynomial of `A` has all its zeros in the open
>       unit disc.
> (iii) The Jordan canonical form of `A` has all its diagonal elements
>       in the open unit disc.
> (iv)  There exists a non-singular matrix `S` such that
>       `‖S⁻¹ A S‖_∞ < 1`.

Butcher's proof goes (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i).  The first and
last steps avoid Jordan / Schur structure, but the middle steps —
(ii) ⇒ (iii) and (iii) ⇒ (iv) — are precisely the "diagonalise modulo
nilpotent" content that *requires* Jordan canonical form (or, as a
weaker substitute, a Schur upper-triangular decomposition with arbitrary
off-diagonal scaling).

In Mathlib `v4.28.0` (as pinned by `lakefile.toml`):

- `Mathlib/LinearAlgebra/JordanChevalley.lean` provides only the
  *Jordan-Chevalley-Dunford* decomposition (`f = s + n` with `s`
  semisimple and `n` nilpotent commuting), **not** the Jordan canonical
  form (block-diagonal with explicit Jordan blocks).
- A search for `Schur` in `Mathlib/LinearAlgebra/` only turns up
  `SchurComplement` (a 2×2 block-matrix lemma, unrelated to spectral
  triangularization).
- `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` contains
  `iSup_genEigenspace_eq_top` ("the generalised eigenspaces span the
  whole space" over an algebraically closed field with finite
  dimension), which is a precursor to Jordan form but does not give a
  basis in which the matrix is upper triangular with eigenvalues on
  the diagonal.

Consequently, none of the directions
`(ii) ⇒ (iii)`, `(iii) ⇒ (iv)`, `(ii) ⇒ (iv)`, or `(i) ⇒ (iv)` can
currently be discharged in Lean without first building substantial
upstream infrastructure.

## Context

`OpenMath/Chapter1/Section142.lean` formalises a *partial* version of
Theorem 142D: only the two directions that avoid Jordan/Schur
structure.  The committed deliverables are:

- `convergent_imp_minpoly_roots_lt_one` — Butcher 142D (i) ⇒ (ii).
- `similar_norm_lt_one_imp_convergent` — Butcher 142D (iv) ⇒ (i).

Together these imply
`(iv) ⇒ (i) ⇒ (ii)`, but not `(i) ↔ (ii)` and not `(i) ↔ (iv)`.  No
`TFAE` / `Iff` packaging the four (or three) clauses is shipped, since
that would require at least one of the missing directions back from
(ii) to (i) or (iv).

Clause (iii) — "the Jordan canonical form of `A` has all its diagonal
elements in the open unit disc" — is **not stated at all** in the Lean
file, because Mathlib has no Jordan-canonical-form predicate to
restrict; encoding it as `True` would be a faithfulness failure (a
`True ↔ True` placeholder in an `Iff` is what the cycle-005 strategy
explicitly flags as a "tautology check failure").

## What was tried

Mathlib search results captured during the cycle-005 search round:

- `find Mathlib -iname '*jordan*'` returns five files: only
  `LinearAlgebra/JordanChevalley.lean` is matrix-relevant, and it
  provides Jordan-Chevalley (semisimple + nilpotent), not Jordan
  canonical form.
- `grep -rn 'isUnitarilyEquivalent\|Triangularizable\|upper.*triangular.*similar'`
  in `Mathlib/LinearAlgebra/` returns the Lie-algebra
  `IsTriangularizable` class and the
  `Module.End.iSup_genEigenspace_eq_top` lemma — neither gives an
  upper-triangular *basis*.
- `grep -rn 'Schur'` in `Mathlib/LinearAlgebra/` returns only
  `SchurComplement` (a 2×2 block-matrix lemma).
- `grep -rn 'spectralRadius'` in `Mathlib/Analysis/` shows that Gelfand's
  formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`)
  is available, but Mathlib does not provide a direct
  "spectralRadius < 1 ⇒ Tendsto pow zero" wrapper, nor a direct bridge
  from "all minpoly roots in open unit disc" to `spectralRadius < 1`
  for matrices.  Closing (ii) ⇒ (i) via Gelfand would require
  building both bridges, and even then the result would not give
  (ii) ⇒ (iv) (since (iv) is about a particular similarity, not a
  norm fact).

Working bridges that *were* used in the cycle-005 deliverable:

- `Module.End.hasEigenvalue_of_isRoot` + `Matrix.minpoly_toLin'` for
  bridging minpoly roots of a matrix to eigenvectors of `Matrix.toLin'`.
- `Units.conj_pow'` for the conjugation identity
  `(↑u⁻¹ * x * ↑u)^n = ↑u⁻¹ * x^n * ↑u`.
- `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` for the (iv) ⇒ (i)
  closer.
- `linfty_opNorm_mulVec` for `‖A *ᵥ v‖ ≤ ‖A‖ ‖v‖` in the eigenvector
  argument.

## Possible solutions

(a) **Wait for upstream Mathlib.** Jordan canonical form has been
    discussed on Zulip multiple times; an implementation is in the
    queue but not yet merged.  The cleanest long-term option.

(b) **Build a minimal Schur decomposition in `OpenMath/`.**  Schur is
    weaker than full Jordan and is sufficient for both (ii) ⇒ (iv)
    (rescale off-diagonals to make `‖S⁻¹ A S‖ < 1`) and (iii) ⇒ (iv)
    (in fact, with Schur, (iii) becomes "diagonal of upper-triangular
    similarity"). The argument is constructive over an algebraically
    closed field via Gram-Schmidt + induction on dimension.  Estimated
    cost: 3–5 cycles of focused infrastructure work.

(c) **Build (ii) ⇒ (i) via Gelfand's formula.**  This closes
    `(i) ↔ (ii)` without Jordan/Schur, but does *not* recover (iv) and
    therefore does not produce the textbook 4-way TFAE.  Estimated
    cost: 1 cycle, requires the bridges
    `(minpoly ℂ A).IsRoot μ → μ ∈ spectrum ℂ A` and
    `spectralRadius A = sSup (Norm.norm '' spectrum ℂ A)` for matrices,
    plus `spectralRadius A < 1 → Tendsto (A^·) atTop (𝓝 0)` via
    Gelfand.  This would give a strict superset of the cycle-005
    deliverable.

(d) **Accept the partial 142D as the project's deliverable.** Cite the
    Mathlib gap in the docstring (already done in the committed file)
    and move on.  Recommended at least until option (c) is attempted.

## Recommended next step

Option (c) is the right next move whenever the planner returns to
Section 142.  It strictly extends the cycle-005 deliverable, costs
~1 cycle, and unblocks the (i) ↔ (ii) Iff statement.  Option (b) is
the right move only once Section 142 becomes blocking for downstream
work that needs the full TFAE (e.g. `thm:142E`'s perturbation bounds).
