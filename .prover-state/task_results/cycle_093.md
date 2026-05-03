# Cycle 093 Results

## Worked on
The 3 sorries in `OpenMath/Chapter5/Section513.lean` left over from cycle 092:

1. Helper 2 — `GeneralLinearMethod.unit_vector_witness_of_not_stable` (line 222 of cycle 092 file)
2. Helper 5 — `GeneralLinearMethod.unbounded_zero_iterate_contra` (line 248)
3. Main theorem — `GeneralLinearMethod.convergent_isStable` (line 285)

## Approach

### Priority 0 — Aristotle status check (immediate)

Aristotle project `82f24aa0-e3e9-457c-9bea-3aede964de8e` from cycle 092 was
**COMPLETE** (100%). I extracted the result tarball (`/tmp/aristotle_cycle092_results/`)
and inspected `glm_513_helpers_aristotle/glm_513_helpers.lean`. Aristotle had
solved all 8 sorries in the self-contained submission (already-closed helpers
1/3/4 plus the two open ones). I ported Helper 2 and Helper 5 (the ones that
were still `sorry` in `Section513.lean`); Helpers 1/3/4 were left as my
manual cycle-092 proofs (they were already closed and there was no reason to
destabilise working code).

### Helper 5 — `unbounded_zero_iterate_contra`

Direct port of Aristotle's record-index argument, adapted from the
self-contained file's signature (which had the matrix `attribute [local instance]` opens) into Section513's style:
- Get arbitrarily large record indices via `runningMaxNorm_record_above`.
- Combine with the convergence-to-zero threshold (`Metric.tendsto_atTop`) to find an `n` where the ratio `z n / runningMaxNorm z n < 1/2`.
- Show `runningMaxNorm z n > 0` past a threshold (using `runningMaxNorm_ge` + `runningMaxNorm_monotone` from a witness of `‖V^n *ᵥ w n‖ > 0`).
- Substitute `z n = runningMaxNorm z n` to get ratio = 1, contradicting `< 1/2`.

One subtle bridge: `set z := fun n => ‖M.V ^ n *ᵥ w n‖` did NOT fold the
expression `‖M.V ^ n *ᵥ w n‖` (a single application) back to `z n` inside
`hN₁` (still showed the unfolded form). Worked around with an explicit
`have hzn : z n = ‖M.V ^ n *ᵥ w n‖ := rfl` and `rw [← hzn]`.

### Helper 2 — `unit_vector_witness_of_not_stable`

I started from Aristotle's contrapositive structure, but Aristotle's terse
form (`convert h_ns _ _; norm_num [Norm.norm]; exact fun j => by split_ifs <;> norm_num`) had unification
issues in the Section513 namespace (different scoped instances). Rewrote as
a structured proof:

1. Convert `¬ M.IsStable` to `∀ C, ∃ n, C < ‖V^n‖` via `by_contra; push_neg`.
2. Contrapose the goal to obtain a hypothesis of the form
   `∀ w, (∀ n, ‖w n‖ ≤ 1) → ∃ C, ∀ n, ‖V^n *ᵥ w n‖ ≤ C`.
3. For each basis vector `e_i = fun j => if j = i then 1 else 0`, apply
   the hypothesis to the constant sequence `fun _ => e_i` to get a per-`i`
   bound `C i`.
4. Use `pi_norm_le_iff_of_nonneg` + `split_ifs` to verify `‖e_i‖ ≤ 1` (only
   challenge: Lean didn't beta-reduce the lambda inside `pi_norm_le`, so I
   added an explicit `show`).
5. Bound `‖V^n‖₊ ≤ ∑ i, ‖V^n *ᵥ e_i‖₊` at the NNReal level via:
   - `Matrix.linfty_opNNNorm_def` rewrites `‖V^n‖₊` as
     `univ.sup (fun b => ∑ j, ‖V^n b j‖₊)`.
   - `Finset.sup_le` + `Finset.sum_le_sum` reduces to per-entry bound.
   - `nnnorm_le_pi_nnnorm` plus `(V^n *ᵥ e_i) b = V^n b i` gives the entry bound.
6. Cast NNReal bound to ℝ via `NNReal.coe_le_coe` + `push_cast`.

This required adding `open scoped Matrix.Norms.Operator` at the top of
Section513.lean (it was missing — only Section510 had it, and scoped
opens don't propagate through imports).

### Main theorem — `convergent_isStable`

Mirror of `LinearMultistepMethod.convergent_isStable` from
`Section405.lean:101–227`. Key differences from the LMM template:

- **Simpler `IsConvergent` predicate**: GLM's def has no joint-Lipschitz
  / `ContDiff` / uniform-`M_bound` clauses (cycle 091/092 deliberately
  used the textbook-faithful version). So `hConv f 0 hf_lip 0 0 yex
  hyex_x₀ hyex_ode` returns `⟨u, hu_ne, hConv'⟩` with `hConv'`
  having only `start hstart_tendsto 1 hxx Y hY_props` as remaining args.
- **Vector-valued numerator**: starting procedure is
  `start h i := (1/ζ ⌈1/h⌉₊) * w ⌈1/h⌉₊ i` where `w` itself depends on
  `h` via the ceiling. The LMM template used `Tendsto.const_div_atTop`
  (constant numerator); here I had to use `squeeze_zero_norm'` with
  bound `‖start h i‖ ≤ 1/ζ ⌈1/h⌉₊` (using `|w ⌈1/h⌉₊ i| ≤ ‖w ⌈1/h⌉₊‖ ≤ 1`
  via `norm_le_pi_norm` + `hw_unit`).
- **Initial value**: `Y m 0 i = (1/ζ m) * (V^0 *ᵥ w m) i = (1/ζ m) * w m i`,
  matched against `start (1/m)` using `pow_zero` + `Matrix.one_mulVec`
  + the standard `1/(1/m) = m` ceiling chain.
- **Recurrence discharge**: applied `glmZeroIterate_const_smul M (1/m)
  (w m) (1/ζ m)`, which directly gives the predicate after a `funext`
  alignment with `Y m`.
- **Final contradiction**: convert `Tendsto Y atTop (nhds (fun i => u i * 0))`
  to `Tendsto ‖Y n n‖ atTop (nhds 0)` via `Tendsto.norm` and the fact
  that `(fun i => u i * yex 1) = (fun _ => 0)` (since `yex ≡ 0`). Then
  `‖Y n n‖ = z n / ζ n` via `norm_smul` (since `Y n n = (1/ζ n) • (V^n *ᵥ w n)`
  pointwise and `1/ζ n ≥ 0` because `ζ n ≥ 0`). Apply
  `unbounded_zero_iterate_contra`.

## Result

**SUCCESS — sorry count went from 3 → 0.**

`lake env lean OpenMath/Chapter5/Section513.lean` clean (no errors,
no warnings). `lake build OpenMath.Chapter5.Section513` succeeds.
`#print axioms` confirms axiom-clean for all three new closed
declarations:

```
'GeneralLinearMethod.convergent_isStable'             depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralLinearMethod.unit_vector_witness_of_not_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralLinearMethod.unbounded_zero_iterate_contra'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

(Initially the axiom check showed `sorryAx` even after the file
compiled — this was stale `.olean` from the cycle-092 commit. After
removing `Section513.olean` and rebuilding, the axiom-cleanness was
confirmed.)

## Faithfulness check

### `thm:513A` — `convergent_isStable`
- **Entity ID**: `thm:513A`. Textbook quote (from `entities/thm_513A.json`):
  > "A general linear method `(A, U, B, V)` is convergent only if it is stable."
- **Lean statement**: `M.IsConvergent → M.IsStable`. **Same content.**
- **Tautology check**: `M.IsStable` is the conclusion, only `M.IsConvergent` is a hypothesis. ✓
- **Identity check**: the proof body is ~150 lines of nontrivial work
  (witness extraction, trivial-IVP setup, convergence → contradiction).
  Not a re-export. ✓
- **Hypothesis-strength check**: only `M.IsConvergent`. No extra clauses. ✓
- **Absent theorem check**: every helper invoked exists with a
  non-`sorry` body in this file or `Section512.lean`. ✓

### Helper 2 — `unit_vector_witness_of_not_stable`
- Genuine extracted lemma from §513 proof (constructs the witness
  sequence `w n`). Not a re-export. ✓
- Hypothesis: `¬ M.IsStable`. Conclusion: `∃ w, …`. No tautology. ✓

### Helper 5 — `unbounded_zero_iterate_contra`
- Genuine extracted lemma (vector-valued analog of LMM's
  `unbounded_homogeneous_contra`). Not a re-export. ✓
- Three hypotheses (unit-bound, unboundedness, ratio-tendsto-zero) ⇒
  `False`. No tautology. ✓

## Dead ends

1. **Aristotle's terse form for Helper 2**: copying the line
   `convert h_ns _ _; norm_num [Norm.norm]; exact fun j => by split_ifs <;> norm_num`
   verbatim into Section513 produced unification errors (the `convert`
   couldn't bridge `Norm.norm` for the indicator vector). Rewrote as
   structured proof with explicit `show`.

2. **`squeeze_zero_norm` (without `'`)**: my first try used the
   absolute-bound version, but I needed the eventual-bound (`∀ᶠ`)
   version which is named `squeeze_zero_norm'`. Quick fix once I checked
   `Mathlib/Analysis/Normed/Group/Continuity.lean:82`.

3. **`set` not folding singleton applications**: `set z := fun n => …`
   does not always replace `f n` with `z n` in subsequent hypotheses
   (it folds the lambda but not all applications). Worked around with
   explicit `have z_eq : z n = … := rfl; rw [← z_eq]`.

4. **Stale `.olean` masking axiom-cleanness**: when I first ran
   `#print axioms`, the result still showed `sorryAx` because the
   `.olean` from the cycle-092 commit was reused. `rm
   .lake/build/lib/lean/OpenMath/Chapter5/Section513.olean` and
   rebuilding fixed this. Worth flagging for future cycles: `lake env
   lean <file>` does NOT always rebuild the cached `.olean` when the
   source has changed but trace says fresh.

## Discovery

1. **Linfty operator norm row-bound trick**: the inequality
   `‖A‖_{linfty op} ≤ ∑_i ‖A · e_i‖_{linfty}` follows from
   `sup_b ∑_j ≤ ∑_j sup_b` (Finset.sup_le + Finset.sum_le_sum +
   Finset.le_sup), and is the cleanest way to bound the matrix norm by
   per-column-application norms in Lean. Useful for any future GLM
   stability work.

2. **Pi-norm vs matrix-norm in `Fin r → ℝ`**: when w is `Fin r → ℝ`,
   `‖w‖` is the Pi linfty norm (`sup_i |w i|`), accessed via
   `norm_le_pi_norm` and `pi_norm_le_iff_of_nonneg`. Distinct from the
   matrix linfty operator norm. Mixing them up was a non-issue here but
   could trip up future cycles working with `V^n *ᵥ w` expressions.

3. **`squeeze_zero_norm'` vs `squeeze_zero_norm`**: the `'` version
   takes `∀ᶠ x in l, ‖f x‖ ≤ a x`; the non-`'` version takes
   `∀ x, ‖f x‖ ≤ a x`. Filter-aware proofs in nhds-style situations
   need `'`.

4. **Aristotle Helper 4 quality check**: Aristotle's
   `glmZeroIterate_const_smul` body uses `convert M.glmZeroIterate_isGLMSolution h (fun i => c * y₀ i) using 1; ext n i; simp [...]; simp [...]` —
   different from my cycle-092 manual proof (which used
   `isGLMSolution_zero_iff` directly). Both are correct; I kept my
   version since it was already integrated.

## Suggested next approach

Now that `thm:513A` is closed, the natural next §5 targets are:

- **`thm:514A`** — convergent ⇒ consistent. Butcher §514 (p. 410).
  Uses a slightly different starting procedure (the textbook constructs
  `φ` from a single basis vector `e_1` rather than a sequence of unit
  vectors); the non-vacuity argument differs from §513 but both build
  on the same `IsConvergent` machinery.
- **`thm:515D`** — stability + consistency ⇒ convergence. Butcher
  §515 (p. 412). The forward direction; significantly heavier than
  §513/§514 (uses Lipschitz iteration + induction on step count).
  Likely needs a multi-cycle build.

I recommend cycle 094 attempts `thm:514A` (smaller, mirrors §513
structure) before tackling `thm:515D`. The Aristotle-first workflow
should batch ~5 sorries from the §514 scaffold once it lands.

(Per planner instruction: I did NOT submit a cycle-094 Aristotle batch
this cycle — cycle 093 ended cleanly without time to scaffold §514.)
