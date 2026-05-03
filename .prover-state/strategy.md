# Cycle 092 Strategy — repair `def:512A` φ-encoding, then sorry-first scaffold `thm:513A`

## Decision (one sentence)

**Two deliverables this cycle, in this order.** First, repair a
faithfulness oversight in cycle 091's `def:512A` (the φ
quantification is `∃` but should be `∀`); then sorry-first scaffold
`thm:513A` (`M.IsConvergent → M.IsStable`) and close the
infrastructure helpers.

## Target

* **Priority 0 (faithfulness fix)** — `def:512A`'s `∃ φ` must
  become `∀ φ`. See §A below.
* **Priority 1 (next-up entity)** — `thm:513A` (Butcher §513,
  p. 409) — *"A general linear method (A, U, B, V) is convergent
  only if it is stable."* New file
  `OpenMath/Chapter5/Section513.lean`. See §B below.
* **Priority 2 (Aristotle batch)** — five infrastructure helpers
  needed by §B. Submit at cycle start, sleep 30 min per CLAUDE.md.
  See §C below.

## A. Priority 0 — repair `def:512A` (Section512.lean:132)

### Diagnosis

Cycle 091's `IsConvergent` (`Section512.lean:132–148`) reads:

```lean
def GeneralLinearMethod.IsConvergent ... :=
  ∀ f L (hL : LipschitzWith L f) ∀ x₀ y₀ yex (hy0 : yex x₀ = y₀)
    (hode : ∀ x, HasDerivAt yex (f (yex x)) x),
  ∃ u : Fin r → ℝ, u ≠ 0 ∧
    ∃ φ : ℝ → Fin r → ℝ,
    (∀ i, Filter.Tendsto (fun h => φ h i) (nhds 0) (nhds (u i * y₀))) ∧
    ∀ x, x₀ < x → ∀ Y, (...iteration with Y n 0 = φ ((x-x₀)/n)...) →
      Filter.Tendsto (fun n => Y n n) atTop (nhds (fun i => u i * yex x))
```

The LMM analog at `OpenMath/Chapter4/Section404.lean:333–354` uses
**`∀ start`**, not `∃ start`. The cycle-072 LMM `convergent_isStable`
proof (`OpenMath/Chapter4/Section405.lean:101–227`) **constructs** its
own `start` (line 124) and plugs it into the universal slot. Under
cycle 091's existential encoding, the worker cannot do this — they
only get the φ that `IsConvergent`'s existential hands them, which
they cannot direct.

The textbook proof of `thm:513A` (Butcher §513, p. 409) **picks**
its own bad starting procedure
`φ(1/n) = (1/max_{i≤n} ‖V^i w_i‖) w_n` to derive a contradiction.
This is incompatible with the existential encoding.

The `∃ u` is correct (`u` is a *property of the method*, like a
preconsistency vector, not a free choice of the user). Only the φ
encoding is wrong.

### Fix

Edit `OpenMath/Chapter5/Section512.lean:132–148` from

```lean
∃ u : Fin r → ℝ, u ≠ 0 ∧
  ∃ φ : ℝ → Fin r → ℝ,
  (∀ i, Filter.Tendsto (fun h => φ h i) (nhds 0) (nhds (u i * y₀))) ∧
  ∀ x, x₀ < x → ∀ Y, (...) → ...
```

to

```lean
∃ u : Fin r → ℝ, u ≠ 0 ∧
  ∀ φ : ℝ → Fin r → ℝ,
    (∀ i, Filter.Tendsto (fun h => φ h i) (nhds 0) (nhds (u i * y₀))) →
  ∀ x, x₀ < x → ∀ Y, (...) → ...
```

(The conjunction `∧` becomes implication `→` after the `∀ φ`.)

### Verify

* `lake env lean OpenMath/Chapter5/Section512.lean` clean.
* `#print axioms` for `IsConvergent` shows
  `[propext, Classical.choice, Quot.sound]`.
* The two cycle-091 helpers (`isGLMSolution_zero_iff`,
  `zero_isGLMSolution_zero`, `zero_seq_homogeneous_V`) are
  unaffected — they don't reference `IsConvergent`.
* Update the docstring on `IsConvergent` to remove "existential" and
  add a note "see also `is_convergent_strengthened.md`'s LMM
  precedent — we deliberately do not preemptively apply joint-Lipschitz
  / C¹ / M_bound strengthenings; if a future §515 proof requires
  them, file a parallel issue at that point."
* Update `.prover-state/issues/glm_convergence_witness_deferred.md`
  with a one-line note: "Cycle 092 repaired the φ existential to
  universal; the deferral remains in force."

This is a 5-minute edit + 1-minute axiom check. Do this **before**
beginning §B.

## B. Priority 1 — sorry-first scaffold `thm:513A`

### Statement

```lean
theorem GeneralLinearMethod.convergent_isStable
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) : M.IsStable
```

In a new file `OpenMath/Chapter5/Section513.lean`, namespace
`OpenMath.Chapter5.Section510` (matching Section512.lean's choice).

### Textbook proof transcribed

> Suppose, on the contrary, that `{V^n : n = 1, 2, 3, …}` is
> unbounded. Then there exists a sequence of vectors `w_1, w_2, …`
> with `‖w_n‖ = 1` and such that `{V^n w_n}` is unbounded. Consider
> the trivial IVP `y'(x) = 0, y(0) = 0` with `n` steps of stepsize
> `h = 1/n`, approximating at `x = 1`. Convergence forces the
> approximations to converge to `u·0 = 0` (irrespective of `u`).
> Use the starting approximation
> `φ(1/n) = (1/max_{i ≤ n} ‖V^i w_i‖) w_n`. Then `‖φ(1/n)‖ → 0`
> (denominator → ∞). The result after n steps is
> `V^n φ(1/n) = (1/max...) V^n w_n`, with norm
> `‖V^n φ(1/n)‖ = ‖V^n w_n‖ / max_{i ≤ n} ‖V^i w_i‖`.
> Infinitely many `n` make this ratio = 1 (whenever
> `‖V^n w_n‖ = max_{i ≤ n} ‖V^i w_i‖`), contradicting convergence
> to 0.

### Lean strategy

Mirror `OpenMath/Chapter4/Section405.lean:101–227` (cycle 072's LMM
`convergent_isStable`) line-for-line, with the substitutions:

| LMM (cycle 072) | GLM (cycle 092/093) |
|---|---|
| `y : ℕ → ℝ` (unbounded homogeneous) | `w : ℕ → Fin r → ℝ` (unit-norm, with `‖V^n w n‖` unbounded) |
| `runningMaxAbs y n` | `runningMaxNorm (fun i => V^i *ᵥ w i) n` |
| `start h i := y i.val / ζ ⌈1/h⌉` | `start h i := w ⌈1/h⌉ i / ζ ⌈1/h⌉` |
| `Y m n := y n / ζ m` | `Y m n i := (V^n *ᵥ w m) i / ζ m` |
| `IsHomogeneousSolution.const_smul` | `glmZeroIterate_isGLMSolution` (sub-lemma) |
| Final contradiction via `unbounded_homogeneous_contra` | Vector analog (sub-lemma) |

### Sorry-first scaffold (write this verbatim, then attempt closure)

```lean
import OpenMath.Chapter5.Section512

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators Topology

/-- **Butcher Theorem 513A** (p. 409) — A convergent general linear
method is stable. -/
theorem GeneralLinearMethod.convergent_isStable
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) : M.IsStable := by
  by_contra h_ns
  -- Step 1: extract unit-vector witness sequence with unbounded V^n action.
  obtain ⟨w, hw_unit, hw_unbd⟩ :=
    GeneralLinearMethod.unit_vector_witness_of_not_stable h_ns
  -- Step 2: trivial IVP setup (f ≡ 0, x₀ = 0, y₀ = 0, yex ≡ 0).
  set f : ℝ → ℝ := fun _ => 0 with hf_def
  set yex : ℝ → ℝ := fun _ => 0 with hyex_def
  -- Step 3: extract u from hConv (applied to trivial IVP).
  -- u is some non-zero vector that the method's convergence is "scaled by".
  -- Discharge the existential to get u, hu_ne, and the universal-φ
  -- statement.
  obtain ⟨u, hu_ne, hConv'⟩ :=
    hConv f 0 (by rw [hf_def]; exact LipschitzWith.const _) 0 0 yex rfl
      (fun x => by rw [hyex_def, hf_def]; exact hasDerivAt_const x 0)
  sorry -- ← cycle 093 closes this from here using the LMM template
        --   (build runningMaxNorm, start, Y, derive contradiction)

end OpenMath.Chapter5.Section510
```

The `sorry` is the cycle-093 deliverable. The cycle-092 deliverable
is everything *above* it — the imports, namespace, scaffold, and
the *signature* of `unit_vector_witness_of_not_stable`. It must
compile.

If Aristotle returns clean proofs of all five §C helpers within the
30-minute window, the worker MAY attempt to close the main `sorry`
this cycle as a stretch goal; otherwise it stays as scaffold and
cycle 093 picks it up. **Do not force.**

## C. Priority 2 — Aristotle batch (submit at cycle start)

Submit a single Aristotle project containing the five helpers below,
with sorry bodies. Sleep 30 minutes; check once.

### Helper 1 — `runningMaxNorm` family

Direct port of `OpenMath/Chapter4/Section404.lean:5651–5691` with
`|·|` → `‖·‖` and `ℕ → ℝ` → `ℕ → Fin r → ℝ` (or `ℕ → ℝ` if you
specialise to `‖V^n *ᵥ w n‖` directly — preferred, simpler).

```lean
def runningMaxNorm (z : ℕ → ℝ) : ℕ → ℝ
  | 0     => z 0
  | n + 1 => max (runningMaxNorm z n) (z (n + 1))

theorem runningMaxNorm_monotone (z : ℕ → ℝ) :
    Monotone (runningMaxNorm z) := by sorry

theorem runningMaxNorm_ge (z : ℕ → ℝ) (n : ℕ) :
    z n ≤ runningMaxNorm z n := by sorry

theorem runningMaxNorm_atTop_of_unbounded
    {z : ℕ → ℝ} (hz : ∀ C : ℝ, ∃ n, C < z n) :
    Filter.Tendsto (runningMaxNorm z) Filter.atTop Filter.atTop := by sorry

theorem runningMaxNorm_record_above
    {z : ℕ → ℝ} (hz : ∀ C : ℝ, ∃ n, C < z n) (N : ℕ) :
    ∃ n, N ≤ n ∧ z n = runningMaxNorm z n := by sorry
```

These four mirror `runningMaxAbs_*` line-for-line. Aristotle should
close all four within minutes; if the manual port from
Section404.lean takes < 30 min, **prefer the manual port** (faster
than waiting on Aristotle).

### Helper 2 — `unit_vector_witness_of_not_stable`

This is the mathematically loaded one — extracts the witness
sequence from `¬ M.IsStable` (cycle 084).

```lean
theorem GeneralLinearMethod.unit_vector_witness_of_not_stable
    {s r : ℕ} {M : GeneralLinearMethod s r} (h_ns : ¬ M.IsStable) :
    ∃ w : ℕ → Fin r → ℝ,
      (∀ n, ‖w n‖ ≤ 1) ∧
      (∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖) := by sorry
```

Construction (when Aristotle fails, do this manually in cycle 093):

1. `¬ M.IsStable` unfolds to `∀ C, ¬ PowerBounded C M.V`, i.e.
   `∀ C, ∃ n, C < ‖M.V ^ n‖`.
2. For each `n`, the linfty operator norm `‖M.V ^ n‖` (which is
   `Matrix.linftyOpNorm`) equals `Finset.univ.sup' ⟨0, …⟩
   (fun i => ∑ j, |((M.V ^ n) i j)|)`.
3. Pick `i_n : Fin r` realising the row sup; set
   `w n j := SignType.sign ((M.V ^ n) i_n j)` (cast to ℝ as
   `±1`).
4. Then `((M.V ^ n) *ᵥ w n) i_n = ∑_j (M.V ^ n) i_n j · sign(...)
   = ∑_j |(M.V ^ n) i_n j| = ‖M.V ^ n‖`.
5. So `‖(M.V ^ n) *ᵥ w n‖ ≥ |((M.V ^ n) *ᵥ w n) i_n| = ‖M.V ^ n‖`,
   which is unbounded.

The `‖w n‖ ≤ 1` part: `w n` has entries in `{-1, 0, +1}`, so
`‖w n‖_∞ = max_j |w n j| ≤ 1`.

If this proves too heavy for cycle 092 (it likely is — Aristotle is
unlikely to find the row-realiser construction), **defer to cycle
093** and leave the helper as a `sorry` with a TODO comment
referring to this strategy section.

### Helper 3 — `glmZeroIterate` and `glmZeroIterate_isGLMSolution`

```lean
def GeneralLinearMethod.glmZeroIterate {s r : ℕ}
    (M : GeneralLinearMethod s r) (y₀ : Fin r → ℝ) (n : ℕ) : Fin r → ℝ :=
  (M.V ^ n) *ᵥ y₀

theorem GeneralLinearMethod.glmZeroIterate_isGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) (M.glmZeroIterate y₀) := by sorry
```

Proof sketch: use `isGLMSolution_zero_iff` (cycle 091) to reduce to
the homogeneous V-recurrence
`y_seq (n+1) i = ∑_j V_{ij} · y_seq n j`, which under
`y_seq n := V^n *ᵥ y₀` becomes
`(V^(n+1) *ᵥ y₀) i = ∑_j V_{ij} · (V^n *ᵥ y₀) j`. RHS is
`(V *ᵥ (V^n *ᵥ y₀)) i = (V * V^n *ᵥ y₀) i = (V^(n+1) *ᵥ y₀) i`,
the LHS. Closes via `Matrix.mulVec_mulVec` and `pow_succ`.

This is Aristotle-friendly (clean algebra, all named Mathlib
lemmas).

### Helper 4 — `glmZeroIterate.const_smul`

```lean
theorem GeneralLinearMethod.glmZeroIterate_const_smul {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) (c : ℝ) :
    M.IsGLMSolution h (fun _ => 0) (fun n i => c * (M.glmZeroIterate y₀ n) i) := by
  sorry
```

Proof: `M.V^n *ᵥ (c • y₀) = c • (M.V^n *ᵥ y₀)` via
`Matrix.mulVec_smul` (or `smul_mulVec`); then apply
`glmZeroIterate_isGLMSolution` with `y₀ ↦ c • y₀` and unfold
`glmZeroIterate`. Should be a 5-line proof. Aristotle-friendly.

### Helper 5 — vector contradiction extractor

Vector analog of `unbounded_homogeneous_contra`
(`Section404.lean`). Submit:

```lean
theorem GeneralLinearMethod.unbounded_zero_iterate_contra
    {s r : ℕ} {M : GeneralLinearMethod s r}
    {w : ℕ → Fin r → ℝ}
    (hw_unit : ∀ n, ‖w n‖ ≤ 1)
    (hw_unbd : ∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖)
    (hY : Filter.Tendsto
            (fun n : ℕ => ‖(M.V ^ n) *ᵥ w n‖ /
                            runningMaxNorm (fun i => ‖(M.V ^ i) *ᵥ w i‖) n)
            Filter.atTop (nhds 0)) :
    False := by sorry
```

Proof sketch: by `runningMaxNorm_record_above` applied to
`(fun n => ‖V^n *ᵥ w n‖)`, there are infinitely many record indices
`n` where the running max equals the current value, giving
`‖V^n *ᵥ w n‖ / runningMaxNorm ... n = 1`. The ratio sequence is
not eventually < 1, contradicting `hY`. Aristotle should handle
this — it's a `Tendsto.atTop_basis` argument.

## What NOT to try

* **Do NOT attempt `thm:513A` without first repairing `def:512A`.**
  The repair is a 5-minute edit and is mandatory for the proof
  template to apply. Skipping it means cycle 092 is wasted.
* **Do NOT introduce `axiom` / `constant`** for any helper. The
  `unit_vector_witness_of_not_stable` construction is genuinely
  concrete (sign-of-row-of-V^n).
* **Do NOT raise `maxHeartbeats` above 200000.** If
  `glmZeroIterate_isGLMSolution`'s `Matrix.mulVec_mulVec` rewriting
  is slow, decompose; do not raise the ceiling.
* **Do NOT poll Aristotle more than once** (CLAUDE.md;
  `consultant_advice_cycle_040.md` §C).
* **Do NOT cherry-pick `def:530A` or `def:530B` or any of the
  unstarted Ch.5 definitions over `thm:513A`.** A pure-definition
  cycle would be lower value than exercising the cycle-091
  predicate against its first dependent.
* **Do NOT generalise `f : ℝ → ℝ` to vector-valued
  `f : ℝ → Fin N → ℝ`.** Cycle 091 committed to scalar `f`; preserve
  that.
* **Do NOT preemptively apply the LMM `is_convergent_strengthened`
  conditions** (joint-Lipschitz, ContDiff ℝ 1, M_bound) to GLM
  `IsConvergent`. The trivial-IVP proofs for §513/§514 don't
  trigger any of those; defer the question to whenever a §515
  helper actually fails. (When that happens, file a parallel issue
  to `is_convergent_strengthened.md`.)
* **Do NOT close `lem:515B` or `thm:515D` "while you're there".**
  Those are 3+ cycle efforts and out of scope.
* **Do NOT modify `scripts/autonomous_loop.py`** (per CLAUDE.md and
  the standing `tautology_scanner_false_positives.md`).
* **Do NOT skip the cycle-091 docstring update on `IsConvergent`**
  after the φ-fix. The docstring currently says "encoding choices:
  existential `u, φ`"; this becomes false after Priority 0.
* **Do NOT attempt to replace `Matrix.linftyOpNorm` with
  Frobenius / l2.** All matrix norms on a finite-dimensional space
  are equivalent up to constants, but the witness construction in
  Helper 2 is *much* cleaner with linfty. Cycle 084 already chose
  linfty for `IsStable`; stick with it.

## Pre-commit faithfulness checklist

For the `def:512A` repair (Priority 0):

- [ ] Quote textbook (entities/def_512A.json) in the docstring.
- [ ] Confirm: `∃ u, u ≠ 0 ∧ ∀ φ, ...` matches Butcher's "there
      exist a non-zero vector u, and a starting procedure φ such
      that..." under the standard reading where φ is a *parameter*
      of the convergence claim, not a method-level data.
- [ ] **Definition smuggling check**: the new `IsConvergent` does
      not embed `IsStable` or `IsConsistent` as conclusions; it
      remains the convergence predicate proper.

For `thm:513A` scaffold (Priority 1):

- [ ] Entity ID `thm:513A`. Quote: *"A general linear method (A, U,
      B, V) is convergent only if it is stable."*
- [ ] Lean statement `M.IsConvergent → M.IsStable` matches **same
      content**.
- [ ] **Tautology check**: `M.IsStable` is not a hypothesis. Pass.
- [ ] **Identity check**: scaffold's only sorry is the contradiction
      assembly; not `exact hConv`. Pass.
- [ ] **Hypothesis-strength check**: only `M.IsConvergent`. No
      strengthening.
- [ ] **Absent theorem check**: any sub-sorry has a TODO comment
      pointing to the strategy section that closes it (cycle 093 +
      this strategy's §C).

For each new helper (Priority 2):

- [ ] Comment explaining role and which textbook step.
- [ ] No tautology / identity / smuggling.
- [ ] Hypotheses minimal (`runningMaxNorm` is a pure
      sequence-of-reals helper; no `M : GeneralLinearMethod`
      dependency).

## Build steps (post-edit)

1. `lake env lean OpenMath/Chapter5/Section512.lean` (after Priority 0).
2. `lake env lean OpenMath/Chapter5/Section513.lean` (after Priority 1).
3. `lake build OpenMath.Chapter5.Section512 OpenMath.Chapter5.Section513`.
4. Axiom check on `convergent_isStable` and helpers: only
   `propext, Classical.choice, Quot.sound`.
5. Update `extraction/formalization_data/lean_status.json`:
   * `def:512A` — keep as `formalized`, add note
     "cycle 092 repaired φ to universal".
   * `thm:513A` — set to `partial` with file pointer
     `OpenMath/Chapter5/Section513.lean`.
6. Update `plan.md` Chapter 5 — `thm:513A` row gets `[~]` (in
   progress) and a note pointing to `Section513.lean`. The
   `Progress: N / 175` counter does NOT advance (only `[x]` rows
   count).
7. Commit message:
   `Cycle 092 — repair def:512A φ encoding + scaffold thm:513A
   (convergent ⇒ stable)`.

## If Aristotle returns nothing useful

Fallback: the manual ports of the `runningMaxNorm` family
(Helper 1) and the `glmZeroIterate` definition + lemma (Helper 3,
Helper 4) are short enough to land in 30–60 minutes of manual work.
Helper 2 (`unit_vector_witness_of_not_stable`) and Helper 5 (the
contradiction extractor) are the genuinely-loaded helpers; if
Aristotle fails on those, **leave them as `sorry`** with the
strategy-section TODO and proceed to commit. Cycle 093 picks them
up.

A cycle 092 with **just** the Priority 0 fix + Priority 1 scaffold
+ Helpers 1, 3, 4 closed manually + Helpers 2, 5 as `sorry`s is a
**successful** cycle. Do not over-extend.

## If reconciliation goes sideways

If the worker discovers during Priority 0 that the repair is
larger than 5 minutes (e.g. the cycle-091 helpers DO reference the
`∃ φ` encoding indirectly), file an issue
`.prover-state/issues/glm_is_convergent_phi_repair.md` documenting
the dependency, then **revert to scaffold-only mode**: leave
`def:512A` as-is, write `Section513.lean` with a single `sorry` for
the entire main theorem, document the φ-encoding blocker. Cycle 093
becomes a dedicated repair cycle.

## Cross-references

* `OpenMath/Chapter5/Section512.lean:132–148` — `IsConvergent`
  predicate to repair (Priority 0).
* `OpenMath/Chapter4/Section404.lean:333–354` — LMM `IsConvergent`,
  the canonical `∀ start` template.
* `OpenMath/Chapter4/Section405.lean:101–227` — LMM
  `convergent_isStable` (cycle 072), the line-by-line model for §B.
* `OpenMath/Chapter4/Section404.lean:5642–5719` — LMM
  `runningMaxAbs` family, the port target for Helper 1.
* `OpenMath/Chapter5/Section510.lean:105–107` — GLM `IsStable`
  (cycle 084) using `PowerBounded C M.V`.
* `extraction/formalization_data/entities/thm_513A.json` —
  textbook statement and proof for `thm:513A`.
* `extraction/formalization_data/entities/def_512A.json` —
  textbook for `def:512A` (used to confirm φ-encoding).
* `.prover-state/issues/glm_convergence_witness_deferred.md` —
  cycle-091 deferral note (update with φ-repair note).
* `.prover-state/issues/is_convergent_strengthened.md` — LMM
  precedent for hypothesis strengthening (do NOT preemptively
  apply here).
* `.prover-state/issues/consultant_advice_cycle_040.md` §A — the
  "scanner / prompt-builder phantom" pattern; if next cycle's
  prompt claims commit/work failure but `git log` shows cycle 092's
  commit landed, ignore the phantom.
