# Cycle 090 Strategy — formalize `def:521A` (stability order)

## What landed last cycle

Cycle 089 closed `def:520F` (L-stable GLM) with witness
`trivialZeroGLM_isLStable`. `OpenMath/Chapter5/Section520.lean` now
holds the full §520 stack: `M(z)` (520A), `Φ(w,z)` and the
`stabilityRegion` / `instabilityRegion` (520C), `IsAStable` (520E),
`IsLStable` (520F). Progress: 60/175.

There are zero pending Aristotle results and no open sorry's anywhere
in `OpenMath/`. The repo state is clean.

## Target this cycle: `def:521A` — stability order

Entity file: `extraction/formalization_data/entities/def_521A.json`.

### Textbook statement (quote from JSON)

> A method with stability function `Φ(w, z)` has 'stability order'
> `p*` if `Φ(exp(z), z) = O(z^{p*+1})`.
>
> [Then introduces a complexity sequence `ν = [ν_0, …, ν_k]` for the
> bivariate polynomial representation of `Φ`, used as setup for
> `thm:521B`.]

### Lean encoding

The primary content is a single condition on `Φ(exp z, z)` as
`z → 0`. Encode as `Asymptotics.IsBigO` at `nhds 0`:

```lean
def GeneralLinearMethod.HasStabilityOrder {s r : ℕ}
    (M : GeneralLinearMethod s r) (p : ℕ) : Prop :=
  Asymptotics.IsBigO (nhds (0 : ℂ))
    (fun z : ℂ => M.stabilityFunction (Complex.exp z) z)
    (fun z : ℂ => z ^ (p + 1))
```

This uses the existing `M.stabilityFunction` from cycle 087
(`OpenMath/Chapter5/Section520.lean:147`), so no new infrastructure
on top of §520 is needed.

### Faithfulness: definition smuggling check

The textbook bundles **two** ideas in §521A:

1. *The stability-order predicate* `Φ(exp z, z) = O(z^{p*+1})` — this
   is the load-bearing definition.
2. *The complexity sequence* `ν = [ν_0, …, ν_k]` representing
   `Φ(w, z)` in the bivariate polynomial form
   `Σ_j w^{k-j} Σ_l α_{jl} z^j`. Constraints `ν_j ≥ −1` with strict
   inequality at `j = 0, k`.

Idea (2) is auxiliary representation/setup for `thm:521B` ("for a
given ν, what is the highest possible stability order?"). It plays
no role in the primary `def:521A` predicate; the textbook only uses
it to *frame* the stability-order question.

**Decision**: formalize idea (1) only this cycle. The complexity
sequence ν is a derived representation that cannot even be defined
in our current encoding (`stabilityFunction : ℂ → ℂ → ℂ` is a
function, not a `Polynomial` — extracting bivariate coefficients
requires a separate polynomial encoding). Defer ν to whenever
`thm:521B` is tackled, with a docstring note recording the
deferral.

This is **not** definition smuggling: idea (1) IS the definition of
"stability order p*" — the textbook literally says
"has stability order p* **if** Φ(exp(z), z) = O(z^{p*+1})". Idea (2)
is auxiliary apparatus, separately introduced under "Suppose the
stability function is given by …".

### Non-vacuity witness

Use `explicitEulerGLM` (already in `Section510`, `Section520`).

* From cycle 086 `explicitEulerGLM_stabilityMatrix`:
  `M(z) = !![1 + z]`.
* So `Φ(w, z) = det(w·I − M(z)) = w − 1 − z` (1×1 determinant).
* Therefore `Φ(exp z, z) = exp z − 1 − z`.
* Mathlib lemma **`Complex.exp_sub_sum_range_isBigO_pow`**
  (`.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:77`):
  ```
  (fun x ↦ exp x − ∑ i ∈ Finset.range n, x^i / i!) =O[𝓝 0] (· ^ n)
  ```
* With `n := 2`: `Σ_{i<2} x^i/i! = 1 + x`, so
  `exp z − (1 + z) =O[𝓝 0] (· ^ 2)`. Exactly what we need for
  `p + 1 = 2`, i.e. `p = 1`.

Hence: `explicitEulerGLM.HasStabilityOrder 1`.

### File placement

Add to `OpenMath/Chapter5/Section520.lean` (NOT a new file). The
definition depends only on `stabilityFunction` (520C) and a separate
`Section521.lean` for one definition would be wasteful. If/when
`thm:521B` is tackled, that cycle can pull this into a new
`Section521.lean` as part of a real §521 build-out.

Place inside `namespace OpenMath.Chapter5.Section510` (so dot
notation `M.HasStabilityOrder p` works on `GeneralLinearMethod`
values), immediately after the `IsLStable` block (line ~322).

The needed import is `Mathlib.Analysis.SpecialFunctions.Exp` —
verify it's already transitively pulled in via the existing
`Mathlib.Analysis.Normed.Algebra.Spectrum` import. If `lean_build`
errors with `unknown constant Complex.exp_sub_sum_range_isBigO_pow`,
add the explicit import line at the top of `Section520.lean`.

### Proof skeleton

```lean
def GeneralLinearMethod.HasStabilityOrder {s r : ℕ}
    (M : GeneralLinearMethod s r) (p : ℕ) : Prop :=
  Asymptotics.IsBigO (nhds (0 : ℂ))
    (fun z : ℂ => M.stabilityFunction (Complex.exp z) z)
    (fun z : ℂ => z ^ (p + 1))

/-- Closed-form: explicit Euler has `Φ(w, z) = w − 1 − z`. -/
theorem explicitEulerGLM_stabilityFunction (w z : ℂ) :
    explicitEulerGLM.stabilityFunction w z = w - 1 - z := by
  unfold GeneralLinearMethod.stabilityFunction
  rw [explicitEulerGLM_stabilityMatrix]
  rw [Matrix.det_fin_one]
  simp; ring

theorem explicitEulerGLM_hasStabilityOrder_one :
    explicitEulerGLM.HasStabilityOrder 1 := by
  unfold GeneralLinearMethod.HasStabilityOrder
  -- Rewrite Φ(exp z, z) into exp z − ∑_{i<2} z^i/i! = exp z − (1 + z).
  have hΦ : (fun z : ℂ => explicitEulerGLM.stabilityFunction
                            (Complex.exp z) z)
            = (fun z : ℂ => Complex.exp z
                - ∑ i ∈ Finset.range 2, z ^ i / (i.factorial : ℂ)) := by
    funext z
    rw [explicitEulerGLM_stabilityFunction]
    simp [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    ring
  rw [hΦ]
  exact Complex.exp_sub_sum_range_isBigO_pow 2
```

If `simp; ring` in `explicitEulerGLM_stabilityFunction` doesn't close
(the determinant expression may need help to unfold `w • 1` and the
1×1 matrix subtraction), use `lean_multi_attempt` with these candidates
in order:

```text
[ "simp [explicitEulerGLM_stabilityMatrix, Matrix.det_fin_one,
       Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]; ring",
  "rw [explicitEulerGLM_stabilityMatrix]; simp [Matrix.det_fin_one]; ring",
  "rw [explicitEulerGLM_stabilityMatrix];
   rw [show (w • (1 : Matrix (Fin 1) (Fin 1) ℂ) - !![1 + z])
         = !![w - (1 + z)] from by ext i j; fin_cases i; fin_cases j; simp];
   rw [Matrix.det_fin_one]; simp; ring" ]
```

For the `hΦ` step: if the chained `simp` doesn't close, do the sum
expansion manually:
```lean
have h0 : (∑ i ∈ Finset.range 2, z ^ i / (i.factorial : ℂ)) = 1 + z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.factorial]
  ring
rw [h0]
ring
```

For the final `exact`: `(p + 1)` with `p := 1` reduces to `1 + 1 = 2`
which is definitionally `Nat.succ 1 = 2`. The exact line should
typecheck without massaging; if it doesn't, insert
`change (fun z : ℂ => Complex.exp z - _) =O[nhds 0] (fun z : ℂ => z ^ 2)`
or `show _ =O[nhds (0:ℂ)] (· ^ 2)` to nudge unification.

### Build / verification

After editing, run:

```bash
lake env lean OpenMath/Chapter5/Section520.lean
lake build OpenMath.Chapter5.Section520
```

Then verify axioms via the standard pattern (the `lake build` step
above is mandatory before `#print axioms`, otherwise the .olean cache
is stale per cycle 089's discovery):

```bash
echo '
import OpenMath.Chapter5.Section520
open OpenMath.Chapter5.Section510
#print axioms explicitEulerGLM_hasStabilityOrder_one
' > /tmp/check_521A.lean
lake env lean /tmp/check_521A.lean
```

Expected: clean build; axioms = `[propext, Classical.choice, Quot.sound]`.

### Faithfulness checklist

- [ ] Open `extraction/formalization_data/entities/def_521A.json` and
      quote the textbook statement in the docstring of
      `HasStabilityOrder`.
- [ ] Confirm `HasStabilityOrder M p` matches the textbook's
      `Φ(exp(z), z) = O(z^{p*+1})` literally (with `p* = p` and
      Big-O at `nhds 0`).
- [ ] Document in the docstring why the **complexity sequence ν is
      deferred** (it's a separate representation device used only by
      `thm:521B`; not part of the primary "stability order"
      definition).
- [ ] No tautology / identity / hypothesis-strength concerns
      (definition has no hypotheses; non-vacuity proof is genuine
      Mathlib citation).
- [ ] Confirm `explicitEulerGLM_hasStabilityOrder_one` is *not*
      vacuous: it uses a concrete witness method, and the
      `Complex.exp_sub_sum_range_isBigO_pow` citation does real
      work (asymptotic bound on `exp z − 1 − z`).

### Bookkeeping

- Update `extraction/formalization_data/lean_status.json` for
  `def:521A`: status `formalized`, `lean_file` set to
  `OpenMath/Chapter5/Section520.lean`, `lean_symbol` set to
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.HasStabilityOrder`.
- Update `plan.md`: tick `def:521A`, bump `60 → 61`.
- Write `.prover-state/task_results/cycle_090.md` per the CLAUDE.md
  template.

## Aristotle policy

**Do NOT submit** to Aristotle this cycle. The proof is small (~40
LOC), depends on a single named Mathlib lemma
(`Complex.exp_sub_sum_range_isBigO_pow`), and direct manual proof is
faster than a 30-minute round-trip. This matches the cycle 086–089
pattern (definition + small witness; no Aristotle).

## What NOT to do

- **Do NOT** formalize the complexity sequence ν or the bivariate
  polynomial decomposition `Φ(w,z) = Σ_j w^{k-j} Σ_l α_{jl} z^j`
  this cycle. Our `stabilityFunction : ℂ → ℂ → ℂ` is a function, not
  a `Polynomial ℂ`, so extracting `α_{jl}` requires either re-encoding
  `stabilityFunction` as a `Polynomial (Polynomial ℂ)` or introducing
  a parallel polynomial representation. That's a multi-cycle
  infrastructure investment, justified only when `thm:521B` is
  tackled. See the §"Faithfulness: definition smuggling check"
  decision above.

- **Do NOT** strengthen `HasStabilityOrder` with a "maximal p*"
  clause (i.e. demanding that `Φ(exp z, z)` is *not* `O(z^{p+2})`).
  The textbook says "*has stability order p* if* …" without the
  maximality clause; the upper bound is implicit in downstream
  results. Adding maximality would be over-specification and would
  require a *non-vanishing* argument (i.e. `¬ IsBigO _ _ (· ^ 3)`)
  for the explicit-Euler witness, which Mathlib does not provide
  out of the box.

- **Do NOT** try to define `HasStabilityOrder` over `ℝ` or with a
  filter other than `nhds 0`. The textbook's `O(z^{p*+1})` is at
  `z → 0` in `ℂ` (since `Φ` is bivariate complex). `nhdsWithin 0
  ({0}ᶜ)` would be over-cautious — `Φ(exp 0, 0) = 1 − 1 − 0 = 0`
  for explicit Euler (and indeed for any consistent method, since
  `det(I − V) = 0` follows from `V·u = u`), so both functions are
  defined and continuous at 0; plain `nhds 0` is correct.

- **Do NOT** spawn a new file `OpenMath/Chapter5/Section521.lean`
  for a single definition. Add to `Section520.lean` per §"File
  placement" above.

- **Do NOT** introduce `axiom`/`constant`. Manual proof using
  `Complex.exp_sub_sum_range_isBigO_pow` closes the witness cleanly.

- **Do NOT** raise `maxHeartbeats`. The proof is small.

- **Do NOT** modify `scripts/autonomous_loop.py`. Standing rule
  per `tautology_scanner_false_positives.md`.

- **Do NOT** chase any "stuck on" / "commits not reaching repo"
  framing if the supervisor's prompt-builder propagates one. Per
  `consultant_advice_cycle_009.md` / `_014.md` / `_015.md`, those
  are stale `attempts.md` artifacts; verify with
  `git log -1 origin/Main/Experiments` and proceed.

## Quick-reference: relevant Mathlib lemmas

| Goal | Lemma | File |
|---|---|---|
| `exp z − Σ_{i<n} z^i/i! = O(z^n)` near 0 | `Complex.exp_sub_sum_range_isBigO_pow` | `Mathlib/Analysis/SpecialFunctions/Exp.lean:77` |
| Big-O notation / typeclass | `Asymptotics.IsBigO` | `Mathlib/Analysis/Asymptotics/...` |
| 1×1 determinant | `Matrix.det_fin_one` | std |
| `(Finset.range (n+1)).sum f = (range n).sum f + f n` | `Finset.sum_range_succ` | std |
| `(Finset.range 0).sum f = 0` | `Finset.sum_range_zero` | std |
| `(Finset.range 1).sum f = f 0` | `Finset.sum_range_one` | std |
