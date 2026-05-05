# Cycle 114 Results

## Worked on

`aux_515D_construct_ell_U_phi_A` — the M-matrix-based constructor for
the vectors `ell_U, phi_A` consumed as side-condition data by
`aux_515B_eta_contraction` and `GeneralLinearMethod.localStepError_bound`.
Cycle 113 drafted but reverted this helper unverified due to the
2300-line Section515.lean compile hanging past 20 minutes. Cycle 114
follows the strategy's scratch-file-first development workflow.

## Approach

1. Read existing `test_aux_515D.lean` (untracked scratch sandbox from
   cycle 112/113 work on sub-lemmas A/B) and the
   `OpenMath/Chapter5/MMatrix.lean` infrastructure (cycles 105–106).
2. Read `aux_515B_eta_contraction` (cycle 107) for the `Mpos` /
   `hMpos_nn` / `hMpos_mulVec` plumbing pattern — this canonical
   reuse pattern was followed exactly.
3. Constructed the helper as follows (in `test_aux_515D.lean` first,
   then transplanted into `Section515.lean`):
   - Set `Mpos := (h₀ * L) • A.map (fun a => |a|)`.
   - Establish `Mpos.EntrywiseNonneg` from `0 ≤ h₀ * L` and
     `0 ≤ |A i j|`.
   - Derive `(Mpos *ᵥ v) i = h₀ L Σ_k |A i k| · v k` (matches the
     equation form needed by the existential conclusion).
   - Define right-hand sides
     `bU i := Σ_j |U i j|` and
     `bA i := ½ (c i)² + Σ_j |A i j · c j|`. Both pointwise non-neg.
   - Apply `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
     (cycle 106) to get inverse positivity of `(I − Mpos)⁻¹`.
   - Define `ell_U := (Ring.inverse (1 - Mpos)) *ᵥ bU` and
     `phi_A := (Ring.inverse (1 - Mpos)) *ᵥ bA`. Non-negativity
     follows from `EntrywiseNonneg.mulVec_nonneg`.
   - The defining equation is verified as
     `(1 - Mpos) *ᵥ ell_U = bU` via
     `Matrix.mulVec_mulVec` + `Ring.mul_inverse_cancel` +
     `Matrix.one_mulVec`, then unfolded via
     `Matrix.sub_mulVec` + `hMpos_mulVec` + `linarith`.
4. After scratch-file verification, transplanted the helper between
   `aux_515B_eta_contraction` and `GeneralLinearMethod.localStepError_bound`
   in `OpenMath/Chapter5/Section515.lean`.

## Result

**SUCCESS** — `aux_515D_construct_ell_U_phi_A` landed in
`OpenMath/Chapter5/Section515.lean` between
`aux_515B_eta_contraction` and the `localStepError_bound` docstring.
The proof uses only standard Mathlib + the cycle 106 M-matrix
inversion infrastructure.

Verification path:
1. Scratch-file compile: `lake env lean test_aux_515D.lean` exited
   with code 0 after ~21 minutes (slow due to `import Mathlib` on
   GPFS-backed olean cache and high system load avg ~60). No
   errors emitted.
2. Section515.lean integration: `lake env lean
   OpenMath/Chapter5/Section515.lean` exited 0 with no errors,
   only the expected `aux_515D_output_tendsto` sorry warning at
   line 1770 plus a few unused-simp-arg lints.

**Tooling fix as part of this cycle**: discovered that
`/tmp/lean4-toolchain/bin/lake` had been overwritten with a
recursive wrapper script that `exec`'d itself (causing every
`lake` invocation, including the cycle 113 attempt, to hang
silently). Fixed by:
- Copying the toolchain's actual `lake` binary from
  `/mmfs1/home/jamesgsy/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lake`
  to `/tmp/lean4-toolchain/bin/lake-real`.
- Updating the wrapper to `exec /tmp/lean4-toolchain/bin/lake-real
  "$@"`.
This unblocks not just cycle 114 but also the cycle 113 attempt
(which the task results record as "lake env lean ... hung past 20
minutes" — that was the wrapper recursing, not lean elaborating).

**Cycle 113 regressions exposed and repaired** (side effect of
restoring the build): once `lake env lean` works again, the
cycle 113 commit's two Aristotle-supplied proofs were exposed
as never-verified:
- `aux_515D_per_step_recurrence`: used `induction'` (from
  `Mathlib.Tactic.Cases`) which Section515.lean's import set
  did not transitively bring in. Fix: added
  `import Mathlib.Tactic.Cases`. The proof's final `ring` step
  also failed because `simp_all +decide` left a residual goal
  with un-distributed sums; fixed by inserting
  `simp only [Finset.mul_sum, mul_add, mul_left_comm]` before
  the `ring`.
- `aux_515D_discrete_gronwall_raw`: shared the `induction'`
  import problem with the above; the import fix alone resolved
  it. The proof's `simp_all +decide` set has an unused
  `Finset.sum_Ico_succ_top` lemma (a Lean linter warning) but
  this is non-fatal.

These fixes are bundled into cycle 114 because (a) they are
necessary for Section515.lean to compile at all, (b) the cycle
114 deliverable's verification depends on Section515.lean
compiling, and (c) leaving the broken proofs unrepaired would
leave the codebase with hidden semantic regressions (cycle 113
"closed" 2 sorry-equivalents that did not actually close).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

- **Entity ID**: not a Butcher entity. `aux_515D_construct_ell_U_phi_A`
  is internal infrastructure — an existential constructor for the
  `ell_U, phi_A` data vectors that satisfy the linear-system side
  conditions of `localStepError_bound` (Section515.lean:1183).
  Butcher §515 uses the analog `ϕ` vector defined by
  `Σ_j (δ_{ij} − h₀ L |a_{ij}|) ϕ_j = ½ c_i² + Σ_j |a_{ij} c_j|`
  (quoted from `entities/lem_515A.json`), and an analogous `ℓ` for
  the `Σ_j |U_{ij}|` right-hand side. The textbook tacitly invokes
  these vectors' existence (under "h₀ L ‖A‖_∞ < 1"); our helper
  closes the existential using cycle 105–107's M-matrix
  infrastructure with the Frobenius-norm contraction hypothesis
  (a faithfulness divergence already documented at
  `aux_515B_eta_contraction` and inherited here).
- **Lean statement captures**: same content as the textbook's two
  linear-system definitions, packaged as an existential. The
  Frobenius-norm hypothesis `h_norm` is strictly stronger than the
  textbook's `h₀ L ‖A‖_∞ < 1`; this is the same divergence as in
  `aux_515B_eta_contraction` (cycle 107 documented).
- **Tautology / identity / definition-smuggling checks**: PASSED.
  No conclusion appears verbatim in the hypotheses; the proof is
  not `exact h`; this is a forward existential construction, not a
  vacuous re-export.
- **Hypothesis strength**: `h₀_pos`, `hL`, and `h_norm` are
  precisely the conditions needed for inverse positivity of
  `I − h₀L|A|`. `_hc_nonneg` is unused inside the proof but kept
  as a safety hypothesis matching the textbook context (the
  consumer sites also assume `c ≥ 0`).

## Dead ends

- **Lake wrapper recursion**: ~20 min wasted before realizing
  `lake env lean` was hanging because the toolchain's lake binary
  had been replaced with a wrapper script that exec'd itself.
  Diagnosed via `ps auxf` showing `lake` processes with no `lean`
  child and ~25% CPU (one core busy reparsing the wrapper script).
  Fix: copy the elan toolchain's actual lake binary to a sibling
  location and update the wrapper to call it.
- **High system load (~60 average) made the scratch-file
  Mathlib import compile take 21 minutes** rather than the
  typical 5–10 min. Not actionable from the worker side; just a
  cluster-shared-resource note for future cycles.

## Discovery

- The cycle 107 plumbing pattern in `aux_515B_eta_contraction`
  (lines 1001–1030 of Section515.lean) is the canonical template
  for any future M-matrix-driven helper: define `Mpos`, prove
  `hMpos_nn`, derive `hMpos_mulVec` once, then proceed. This
  pattern was reused verbatim and worked cleanly.
- `Matrix.mulVec_mulVec` rewrites `M *ᵥ (N *ᵥ v)` to `(M * N) *ᵥ v`
  (left-to-right), which is the direction needed when reducing
  `(1 - M) *ᵥ (M⁻¹ *ᵥ b)` to `b` via `Ring.mul_inverse_cancel`.

## Suggested next approach

**Cycle 115** should pursue Solution A from
`cycle_113_isconvergent_strengthening_514_blocker.md`:
1. Refactor `localStepError_bound` (and its helpers
   `localStageError_bound_a/b`, `aux_T3_bound`, `aux_T4_bound`) to
   accept a *compact-interval* boundedness hypothesis
   `∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound` rather than the global
   form `∀ t, |yex t| ≤ M_bound`.
2. Strengthen `GeneralLinearMethod.IsConvergent` with the
   localized version of the five hypotheses required by
   `localStepError_bound` (per `aux_515D_output_tendsto_hypotheses.md`).
3. Verify §513 (`yex = 0, M_bound := 0`) and §514
   (`yex = id, M_bound := |x|` on `Set.Icc 0 x`) still build.
4. With the cycle-114 `aux_515D_construct_ell_U_phi_A` available,
   compose the body of `aux_515D_output_tendsto` using sub-lemmas
   A/B/C plus `localStepError_bound` plus the constructor.

The constructor helper landed cycle 114 is the load-bearing
primitive: it produces the `ell_U, phi_A` witness that
`localStepError_bound`'s side conditions consume.
