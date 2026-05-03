# Cycle 090 Results

## Worked on

Formalized `def:521A` ("stability order" of a general linear method).

* New definition `OpenMath.Chapter5.Section510.GeneralLinearMethod.HasStabilityOrder`
  in `OpenMath/Chapter5/Section520.lean`.
* Closed-form lemma `explicitEulerGLM_stabilityFunction` (1×1
  determinant collapse: `Φ(w, z) = w − 1 − z` for explicit Euler).
* Non-vacuity witness `explicitEulerGLM_hasStabilityOrder_one`
  (explicit Euler has stability order `p = 1`).

No new sorry's. No infrastructure changes. All three additions
landed in the existing `Section520.lean` file (no new `Section521.lean`
spun up — see strategy §"File placement").

## Approach

Followed the planner strategy verbatim.

1. Added explicit `import Mathlib.Analysis.SpecialFunctions.Exp` to
   `Section520.lean` (was transitively pulled in via
   `Mathlib.Analysis.Normed.Algebra.Spectrum`, but explicit is
   robust against future Mathlib refactors).
2. Encoded `HasStabilityOrder M p` as `Asymptotics.IsBigO (nhds 0)
   (fun z => M.stabilityFunction (Complex.exp z) z) (fun z => z^(p+1))`
   — a literal restatement of the textbook's `Φ(exp(z), z) = O(z^{p*+1})`.
3. Proved `explicitEulerGLM_stabilityFunction (w z : ℂ) :
   explicitEulerGLM.stabilityFunction w z = w - 1 - z` by unfolding
   `stabilityFunction`, rewriting with `explicitEulerGLM_stabilityMatrix`
   (cycle 086), and a 1×1 `Matrix.det_fin_one` plus `simp; ring`.
4. Proved `explicitEulerGLM_hasStabilityOrder_one` by rewriting
   `Φ(exp z, z) = exp z − 1 − z = exp z − ∑_{i<2} z^i / i!` and
   citing `Complex.exp_sub_sum_range_isBigO_pow 2`.

The `funext`/`hΦ` step needed an explicit
`rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]`
+ `simp [Nat.factorial]; ring` because the planner's chained
`simp [Finset.sum_range_succ, ...]` did not automatically expand the
sum into the right form for `ring`. Direct sum-expansion handled it.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter5/Section520.lean` — clean
  (no errors, no warnings).
* `lake build OpenMath.Chapter5.Section520` — `Build completed
  successfully (2772 jobs).`
* `#print axioms explicitEulerGLM_hasStabilityOrder_one` —
  `[propext, Classical.choice, Quot.sound]` (standard Lean kernel
  axioms only).
* `#print axioms GeneralLinearMethod.HasStabilityOrder` — same.
* `#print axioms explicitEulerGLM_stabilityFunction` — same.

## Faithfulness check

### `def:521A` — `GeneralLinearMethod.HasStabilityOrder`

* Entity ID: `def:521A`. Textbook statement (quoted from
  `extraction/formalization_data/entities/def_521A.json`):
  > A method with stability function `Φ(w, z)` has 'stability
  > order' `p*` if `Φ(exp(z), z) = O(z^{p*+1})`.
* Lean statement:
  ```lean
  def GeneralLinearMethod.HasStabilityOrder {s r : ℕ}
      (M : GeneralLinearMethod s r) (p : ℕ) : Prop :=
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ => M.stabilityFunction (Complex.exp z) z)
      (fun z : ℂ => z ^ (p + 1))
  ```
* Captures: **same content**. With `p* = p` and Big-O at `nhds 0`,
  this is the literal predicate of §521A first sentence.
* **Definition smuggling check**: the textbook §521A also introduces
  a *complexity sequence* `ν = [ν_0, …, ν_k]` from the bivariate
  polynomial representation
  `Φ(w,z) = Σ_j w^{k-j} Σ_l α_{jl} z^j`. This is auxiliary
  apparatus used **only** to set up `thm:521B`; it is separately
  introduced by the textbook's "Suppose the stability function is
  given by …" sentence. Idea (1) — the asymptotic predicate — is
  what the textbook calls "stability order"; idea (2) — the
  complexity sequence — is a representation device. Encoding (2)
  here would require re-encoding `stabilityFunction` as a
  `Polynomial (Polynomial ℂ)` (currently it is a function `ℂ → ℂ → ℂ`).
  The deferral is documented in the docstring. **No definition
  smuggling.**
* Tautology / identity / hypothesis-strength concerns: none. The
  definition has no hypotheses; it is an `IsBigO` predicate.
* **No maximality clause** — the textbook says "*has stability
  order p* if* …" without demanding that `p` is the largest such
  integer. Adding maximality would be over-specification (and would
  block the explicit-Euler witness without a non-vanishing
  argument that Mathlib does not provide directly). Documented in
  docstring.

### `explicitEulerGLM_stabilityFunction` (helper lemma — closed form)

* Statement: `explicitEulerGLM.stabilityFunction w z = w - 1 - z`.
* Real work: this is `det(wI − !![1+z]) = w − (1+z) = w − 1 − z`,
  i.e. the 1×1 determinant collapse. Not a re-export of any
  hypothesis. Not vacuous.
* No textbook entity ID — this is a derived computational lemma,
  not a Butcher-named statement.

### `explicitEulerGLM_hasStabilityOrder_one` (non-vacuity witness)

* Statement: `explicitEulerGLM.HasStabilityOrder 1`.
* Real work: rewrites `Φ(exp z, z) = exp z − 1 − z = exp z − ∑_{i<2} z^i/i!`,
  then cites `Complex.exp_sub_sum_range_isBigO_pow 2` from
  `Mathlib/Analysis/SpecialFunctions/Exp.lean:77`. The Mathlib
  lemma does the genuine asymptotic work; the rewrite glue is
  honest.
* Not a re-export of any hypothesis. Not vacuous.

## Dead ends

* The planner's `simp [Finset.sum_range_succ, Finset.sum_range_zero,
  Nat.factorial]; ring` recipe for the `funext` step left the goal
  in a partially-expanded state (sums not fully unfolded). Switched
  to explicit `rw [Finset.sum_range_succ, Finset.sum_range_succ,
  Finset.sum_range_zero]` followed by `simp [Nat.factorial]; ring`,
  which closes cleanly. Recorded as Discovery below.
* Initial `simp [Matrix.smul_apply, Matrix.one_apply]; ring` in
  `explicitEulerGLM_stabilityFunction` produced an "unused simp arg"
  linter warning on `Matrix.one_apply`; removed it. (`Matrix.smul_apply`
  alone suffices because the `1` is the matrix one which `simp`
  unfolds automatically.)

## Discovery

* `simp [Finset.sum_range_succ, Finset.sum_range_zero]` on a goal
  involving `∑ i ∈ Finset.range 2, ...` does **not** always fully
  expand the sum to `f 0 + f 1` form usable by `ring`. Prefer
  explicit `rw [Finset.sum_range_succ, Finset.sum_range_succ,
  Finset.sum_range_zero]` (= unfold `range (n+1) = range n ∪ {n}`
  twice, then `range 0 = ∅`) when subsequent `ring` is needed.
* `Complex.exp_sub_sum_range_isBigO_pow n : (fun x => exp x − ∑_{i<n} x^i/i!) =O[𝓝 0] (· ^ n)`
  is the definitive Mathlib hook for stability-order witnesses on
  any method whose `Φ(exp z, z)` admits a closed-form Taylor
  remainder. Useful for future GLM stability-order calculations.
* The cycle 089 cache-staleness pattern (`#print axioms` failing
  unless preceded by `lake build OpenMath.Chapter5.SectionXXX`)
  reproduced cleanly: ran `lake build` first, then `#print axioms`,
  no issues. Pattern is reliable.

## Suggested next approach

Several reasonable follow-ups for the planner:

1. **`thm:521B`** (the dependent of `def:521A`): "for a given complexity
   sequence ν, the maximal stability order…". This is the natural
   continuation but requires a polynomial encoding of
   `stabilityFunction` to even *state* — a multi-cycle infrastructure
   investment. The planner should weigh whether to (a) introduce a
   separate `stabilityFunction_poly : Polynomial (Polynomial ℂ)` and
   prove it agrees with the existing function form on the
   invertibility domain, or (b) defer §521B and pivot to other §52x
   targets.

2. **`def:525A`** or other §525/§550 definitions: continue the §52x
   stability theory build-out without taking on the polynomial-encoding
   debt of §521B.

3. **§514 / §515 thread** (`thm:514A`, `lem:515A`,
   `thm:515D`): the consistency/stability/convergence theorems sit
   on already-formalized §510 infrastructure (`IsConsistent`,
   `IsStable`, `IsConvergent`) and would build out the convergence
   side rather than the stability side. Probably higher leverage
   per cycle than the §521B polynomial detour.

4. **Stronger `IsAStable` non-vacuity**: the current witness
   `trivialZeroGLM_isAStable` is degenerate (zero method). A
   non-trivial witness (e.g. backward Euler as a 1×1 GLM) would
   exercise the `(1 − z·A)⁻¹` resolvent and stress-test the
   stability-region machinery against a standard textbook example
   before §521B's polynomial work piles on. Could be a one-cycle
   "sanity infrastructure" detour.

My weak recommendation: tackle the **§514/§515 convergence thread
next** — it leverages already-mature infrastructure, has no
polynomial-encoding tax, and would balance the stability-heavy
cycles 086–090.
