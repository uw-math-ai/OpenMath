# Cycle 009 Results

## Worked on

`thm:111A` — Butcher §111 Theorem 111A, *superposition principle for
linear ODE systems*. New file `OpenMath/Chapter1/Section111.lean`,
new theorem `OpenMath.Chapter1.Section111.solution_superposition`.

The cycle-8 strategy note had suggested treating `thm:111A` as a
Picard–Lindelöf existence wrapper for `f(x, y) = A(x) y + b(x)`. The
cycle-9 planner correctly flagged that as a misreading — the actual
textbook statement is the linearity-of-derivative *superposition
principle*. This cycle implemented the superposition reading.

## Approach

1. Loaded `extraction/formalization_data/entities/thm_111A.json` and
   quoted the textbook `statement_latex` in the new theorem's
   docstring.

2. Created `OpenMath/Chapter1/Section111.lean` with the planner's
   recommended signature:

   ```lean
   theorem solution_superposition
       {N k : ℕ}
       (s : Set ℝ)
       (A : ℝ → Matrix (Fin N) (Fin N) ℝ)
       (φ : ℝ → (Fin N → ℝ))
       (ŷ : ℝ → (Fin N → ℝ))
       (y : Fin k → ℝ → (Fin N → ℝ))
       (α : Fin k → ℝ)
       (hŷ : ∀ x ∈ s, HasDerivAt ŷ (A x *ᵥ ŷ x + φ x) x)
       (hy : ∀ i, ∀ x ∈ s, HasDerivAt (y i) (A x *ᵥ (y i) x) x) :
       ∀ x ∈ s, HasDerivAt
         (fun x => ŷ x + ∑ i, α i • y i x)
         (A x *ᵥ (ŷ x + ∑ i, α i • y i x) + φ x) x
   ```

3. Proof outline (no `sorry`s):
   * `HasDerivAt.const_smul` to scale each `y i` by `α i`.
   * `HasDerivAt.sum` over `Finset.univ : Finset (Fin k)` to get
     the derivative of the linear combination.
   * `Finset.sum_apply` (via `funext`/`simp`) to swap the
     `∑ ... fun t => ...` and `fun t => ∑ ...` shapes Mathlib produces.
   * `HasDerivAt.add` to combine `ŷ`'s derivative with the sum.
   * For the equality of the target and computed derivatives, used
     `Matrix.mulVec_add` plus the linear-map version
     `Matrix.mulVecLin` (with `map_sum` and `mulVecLin.map_smul`) to
     distribute `A x *ᵥ` over `Σ αᵢ • yᵢ x` and pull out the `αᵢ`
     scalars. Final reassociation by `abel`.

4. Wired the new file into `OpenMath/Chapter1.lean`:
   `import OpenMath.Chapter1.Section111`.

5. Updated `extraction/formalization_data/lean_status.json` for
   `thm:111A` to `formalized` with file/symbol pointers.

## Result

SUCCESS — compiled clean on first pass with no `sorry`.

* `lake env lean OpenMath/Chapter1/Section111.lean` — exit 0, silent.
* `lake build` — exit 0; `Build completed successfully (2815 jobs)`.
* `#print axioms OpenMath.Chapter1.Section111.solution_superposition`
  reports `[propext, Classical.choice, Quot.sound]` (the standard
  Mathlib base; no introduced axioms).

Aristotle was not invoked — the strategy explicitly says it is not
needed if the proof closes by hand on the first pass without `sorry`,
which is what happened here.

## Faithfulness check

For `thm:111A` (only new theorem this cycle):

* **Entity ID and textbook statement** (quoted from
  `extraction/formalization_data/entities/thm_111A.json`):

  > If $\hat{y}$ is a solution to (111a) and $y_1, y_2, \dots, y_k$
  > are solutions to (111b), then for any constants
  > $\alpha_1, \alpha_2, \dots, \alpha_k$, the function $y$ given by
  > $y(x) = \hat{y}(x) + \sum_{i=1}^{k} \alpha_i y_i(x)$ is a solution
  > to (111a).

  Where (111a) is $\frac{dy}{dx} = A(x) y + \phi(x)$ and (111b) is
  $\frac{dy}{dx} = A(x) y$.

* **Lean statement captures**: same content. `HasDerivAt ŷ (A x *ᵥ ŷ x
  + φ x) x` is the pointwise version of "ŷ solves (111a)", and the
  parallel form for `y i` matches (111b). The conclusion encodes
  exactly Butcher's `y(x) = ŷ(x) + Σᵢ αᵢ yᵢ(x)` solves (111a).

* **Tautology check**: conclusion is `HasDerivAt (ŷ + Σ αᵢ yᵢ)
  (A *ᵥ (ŷ + Σ αᵢ yᵢ) + φ) x`. Hypotheses are derivatives of `ŷ` and
  each `y i` separately. The conclusion is not among the hypotheses
  verbatim — it is genuinely the linear combination's derivative.
  Pass.

* **Identity check**: proof is not `exact h`. It uses
  `HasDerivAt.add`, `HasDerivAt.sum`, `HasDerivAt.const_smul`,
  `Matrix.mulVec_add`, `Matrix.mulVecLin`'s linearity, and an `abel`
  reassociation. Real mathematical work. Pass.

* **Hypothesis-strength check**: hypotheses use `HasDerivAt` (not
  `HasDerivWithinAt`) — equivalent to Butcher's "is a solution" in
  the open / set sense. No spurious extra hypotheses
  (continuity-on-set, Lipschitz, bounds, …) — the planner's signature
  is minimal. The choice of `Set ℝ` (instead of `Icc a b`) and
  `Fin N → ℝ` (instead of `EuclideanSpace ℝ (Fin N)`) are
  generality-increasing and were explicitly flagged by the planner;
  the textbook instance `s = Icc a b` is recoverable. Pass.

* **Definition smuggling check**: no new `def`/`structure` introduced
  this cycle, only a `theorem`. N/A.

* **Absent theorem check**: no comments promise content not present.
  Pass.

## Dead ends

None encountered. The first proof pass closed clean. One minor wrinkle
was that `HasDerivAt.sum` returns the derivative of `∑ i ∈ u, fun t =>
α i • y i t` (a sum of functions), which Lean does not automatically
identify with `fun t => ∑ i, α i • y i t` (the function returning
sums); resolved with a one-line `funext` + `simp [Finset.sum_apply]`
rewrite.

## Discovery

* `Matrix.mulVecLin (A : Matrix m n R) : (n → R) →ₗ[R] m → R` is the
  linear-map version of `Matrix.mulVec` and is the cleanest tool for
  proving `A *ᵥ ∑ i, vᵢ = ∑ i, A *ᵥ vᵢ`. Just `map_sum
  (A x).mulVecLin _ Finset.univ` plus `Matrix.mulVecLin_apply` to
  unfold. Mathlib does not appear to expose a direct `mulVec_sum`
  lemma — `mulVecLin` is the path.
* `HasDerivAt.const_smul` (Mathlib `Analysis.Calculus.Deriv.Mul`)
  takes scalar first, derivative second:
  `HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
   HasDerivAt (c • f) (c • f') x`.
* The planner's prediction that the cycle would close without
  Aristotle was correct. For purely linear / formal derivative
  manipulations on Mathlib's `HasDerivAt`, hand proofs are usually
  faster than batch-submitting.

## Suggested next approach

* **§111 sequel — high-order single-variable case.** Butcher 111A's
  full statement also describes the companion-matrix reduction of an
  `m`-th order scalar equation to a first-order system, plus the
  generalized-eigenvector solution structure for constant-`A` case.
  Those are arguably *separate* statements and good candidates for
  follow-up entities (extension `aux:` IDs would be appropriate; per
  `extraction/EXTENSIBILITY.md`).
* **Next §1 target: `thm:112B`** — One-sided Lipschitz uniqueness /
  contraction-of-trajectories. `def:112A` is already formalized
  (`OneSidedLipschitzInSecond`); `thm:112B` is the natural next
  target. The
  `picard_lindelof_bound_strengthening.md` issue may also touch
  `thm:112B`'s existence half — worth a re-read of the open issues
  list before picking it up.
* **Status sanity**: `thm:142D` is `in_progress` (Jordan/Schur gap),
  `thm:140A`, `thm:141A`, `thm:142C/E/F` all `unformalized`. Ch.1
  has a clear runway after §112.
