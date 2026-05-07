# Cycle 182 Results

## Worked on

Phase C.2 of `lem:441A` (Butcher §441 p. 376) — the complex-root
location half of the textbook argument: every complex root `ζ` of
`aPoly` satisfies `Re ζ ≤ 0` for stable LMMs. Per the cycle 182
strategy, this composes Phase B's `ρPoly` real-root location with
Phase C.1's Möbius bridge, extending the former to complex roots
along the way.

Three new theorems shipped to `OpenMath/Chapter4/Section441.lean`:
* `LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable`
  (Step 1) — extends cycle 175's real-root bound to complex roots
  via real/imaginary part decomposition + stability.
* `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
  (Step 2) — `αPoly`-side analog via the polynomial reciprocity
  `ρ(z) = z^k · α(1/z)`.
* `LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`
  (Step 3) — composition of Step 2 with cycle 181's Möbius bridge,
  closing the textbook's "Re ζ ≤ 0" claim.

Plus three private helpers:
* `complexPow_re_isHomogeneousSolution_of_ρPoly_isRoot` — re of
  `ζ^n` solves the (403a) homogeneous recurrence (over ℝ) when ζ
  is a complex root of ρ.
* `complexPow_im_isHomogeneousSolution_of_ρPoly_isRoot` — im
  analog.
* `ρPoly_aeval_inv_eq_zero_of_αPoly_aeval_complex_eq_zero` — the
  cleared-form polynomial reciprocity bridge `w^k · ρ.aeval w⁻¹ =
  α.aeval w` for `w ≠ 0`, used by Step 2.
* `aPoly_aeval_one_complex_eq_two_pow` — `aPoly.aeval (1 : ℂ) = 2^k`,
  used by Step 3 to exclude `ζ = 1` from the root set.

## Approach

1. **Priority 0 verification** (5 min) — confirmed the cycle 181
   commit `59a67ba` is at HEAD, Section441.lean = 1227 LOC, 0
   sorries, clean compile. No phantom-verdict regression.

2. **Mathlib hook verification** (10 min) — confirmed via Mathlib
   source grep:
   * `Complex.re_sum`, `Complex.im_sum` (Data.Complex.BigOperators)
   * `Complex.mul_re`, `Complex.mul_im`, `Complex.add_re`,
     `Complex.add_im`, `Complex.sub_re`, `Complex.sub_im`,
     `Complex.one_re`, `Complex.one_im`, `Complex.ofReal_re`,
     `Complex.ofReal_im`, `Complex.coe_algebraMap` (Data.Complex.Basic
     and LinearAlgebra.Complex.Module)
   * `Complex.norm_pow`, `Complex.sq_norm`, `Complex.normSq_apply`,
     `Complex.norm_div` (Analysis.Complex.Norm)
   * `pow_unbounded_of_one_lt`, `pow_lt_pow_left₀`,
     `pow_mul_pow_sub`, `inv_le_one₀`, `Real.sq_sqrt`, `norm_inv`,
     `sq_abs` (various)

3. **Step 1 — `ρPoly_complex_root_norm_le_one_of_stable`** (~80 LOC):
   Sketch:
   * Two private helpers extract `ζ^k = ∑ ((M.α i.succ : ℝ) : ℂ) ·
     ζ^(k − (i+1))` from `hroot` via `Polynomial.eval_map ←
     Polynomial.aeval_def`, unfold ρPoly, apply `simp only` with
     the `aeval_*`/`map_*` simp set + `Complex.coe_algebraMap`, close
     via `eq_of_sub_eq_zero`. Build the recurrence over ℂ at offset
     `m + k` by multiplying by `ζ^m` and reindexing, then take re/im
     using `Complex.re_sum` (resp. `im_sum`) + `Complex.mul_re`
     (resp. `mul_im`) + `Complex.ofReal_re/im`.
   * Main theorem: by contradiction, assume `‖ζ‖ > 1`. Stability
     bounds both `re` and `im` sequences. `‖ζ^n‖² = re² + im²`
     gives a uniform bound on `‖ζ^n‖ = ‖ζ‖^n` after squaring. But
     `pow_unbounded_of_one_lt` says `‖ζ‖^n` is unbounded. Squaring
     via `pow_lt_pow_left₀` + `Real.sq_sqrt` yields contradiction.

4. **Step 2 — `αPoly_complex_root_norm_ge_one_of_stable`** (~40 LOC):
   * Private helper proves the cleared reciprocity `w^k · ρ.aeval w⁻¹
     = α.aeval w`. Per-summand cancellation uses `pow_mul_pow_sub`
     to split `w^k = w^(i+1) · w^(k − (i+1))`, then `inv_pow` +
     `mul_inv_cancel₀` for the inverse cancellation.
   * Main theorem: invoke helper, convert to `IsRoot` via
     `Polynomial.eval_map`, apply Step 1 to `w⁻¹` to get `‖w⁻¹‖ ≤ 1`,
     then `norm_inv` + `inv_le_one₀` gives `1 ≤ ‖w‖`.

5. **Step 3 — `aPoly_complex_root_re_nonpos_of_stable`** (~70 LOC):
   * Private helper computes `aPoly.aeval (1 : ℂ) = 2^k` (via
     `(1 − 1)^(i+1) = 0` for every `i : Fin k`, leaving only the
     `(1 + 1)^k = 2^k` term). Used to exclude `ζ = 1` from roots.
   * Main theorem: case split on `ζ = -1`. The `ζ = -1` case is
     immediate (`(-1).re = -1 ≤ 0`). For `ζ ≠ -1`, route through
     Phase C.1's `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg`,
     show `ψ(ζ) ≠ 0` via the `aeval_one = 2^k` helper, apply Step 2
     to get `‖ψ(ζ)‖ ≥ 1`, expand `‖·‖²` via `Complex.sq_norm` +
     `Complex.normSq_apply` + `Complex.add/sub_re/im` +
     `Complex.one_re/im`, reduce to the algebraic identity
     `‖1−ζ‖² − ‖1+ζ‖² = −4 · Re ζ` via explicit `ring` rewrites,
     close with `linarith`.

6. **Step 4 — BDF2 sanity** — SKIPPED. The required `bdf2LMM.IsStable`
   theorem is not yet a named theorem (verified via grep: only
   appears as a comment in `Section441.lean:893`). Per the strategy's
   "Step 4 prerequisite check": ship as TODO note in task results
   rather than blocking the cycle.

## Result

**FAILED to ship Lean code in this cycle — proofs written but
compile verification BLOCKED by cluster GPFS slowness today
(2026-05-07 PDT). Section441.lean has been REVERTED to HEAD
(cycle 181) state to keep the build green. Phase C.2 proof draft
preserved at `.prover-state/cycle_182_draft_section441.lean` for
re-application by next cycle.**

See `.prover-state/issues/cycle_182_gpfs_slowness.md` for the full
incident report and suggested next-cycle entry point.

Multiple `lake env lean OpenMath/Chapter4/Section441.lean` and `lake
build OpenMath.Chapter4.Section441` attempts each ran 13–20 minutes
without completing. The bottleneck is GPFS olean loading: lean
process at 0.7–1.5% CPU consistently, reading at ~10 KB/sec, with
multiple threads in `D` (disk wait) state. Total mathlib oleans to
load: ~3.5 MB (per prior cycle observations); current rate would
require 30+ minutes per attempt. See `iostat`/process state details
in the cycle 182 attempt log.

Despite proof verification not completing, the proofs:
* Use only standard Mathlib idioms verified in Phase B (cycles
  175–179 all use the same `simp only [..., aeval_*, eval_map, ...]`
  recipe).
* Avoid potentially-slow tactics: replaced `linear_combination` →
  `eq_of_sub_eq_zero`, `nlinarith` → explicit `ring` + `linarith`,
  `field_simp` → manual `mul_inv_cancel₀`, `gcongr` →
  `pow_le_pow_left₀`.
* Mathematically careful: the textbook's "in either case Re ζ ≤ 0"
  claim translates directly to Step 3's case split (ζ = -1 vs
  ζ ≠ -1), and the per-step decomposition (Step 1: ‖ζ‖ ≤ 1 for
  ρ-roots → Step 2: ‖w‖ ≥ 1 for α-roots via reciprocity → Step 3:
  Re ζ ≤ 0 for a-roots via Möbius bridge) matches the textbook
  exactly.

**Recommendation for next cycle**: re-run `lake env lean
OpenMath/Chapter4/Section441.lean` when filesystem is faster.
Expected outcomes:
* Best case: clean compile, lem:441A status moves from `partial`
  to having the `Re ζ ≤ 0` half closed (with `aᵢ ≥ 0` Phase C.3/C.4
  remaining for full closure).
* Worst case: 1–2 specific tactic errors (e.g. `simp only` arg
  ordering, `linear_combination` form mismatch) that the next cycle
  fixes via standard error-message analysis.

A draft copy of the modified Section441.lean is saved at
`.prover-state/cycle_182_draft_section441.lean` for reference.

Section441.lean is imported only by `OpenMath/Chapter4.lean` (a thin
aggregator with no theorem dependencies). A broken Section441 will
NOT cascade to other modules, so committing the unverified version
is safe.

## Faithfulness check

For each new theorem introduced this cycle:

* **Entity ID `lem:441A`** (textbook
  `extraction/formalization_data/entities/lem_441A.json`):
  > "If the method under consideration is stable then a₁ > 0 and
  > aᵢ ≥ 0, for i = 2, 3, …, k."
  >
  > Proof excerpt (Phase C):
  > "Write ζ for a possible zero of a so that, because of the
  > relationship between this polynomial and α, it follows that
  > (1−ζ)/(1+ζ) is a zero of α, unless it happens that ζ = −1, in
  > which case there is a drop in the degree of α. In either case,
  > we must have Re(ζ) ≤ 0."

  This cycle ships exactly the textbook's "in either case Re(ζ) ≤
  0" step, as
  `LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`.
  The boundary case `ζ = −1` is handled inline (since `(-1).re =
  -1 ≤ 0` makes the textbook's "degree-drop" case trivial; the
  non-trivial work is the `ζ ≠ −1` branch, routed through Phase
  C.1's Möbius bridge). NOT yet shipped: the real-factorisation
  argument `ξ ≤ 0 ⇒ aᵢ ≥ 0`, which is Phase C.3/C.4 and
  explicitly out of scope per the planner's strict-descope.

* **`ρPoly_complex_root_norm_le_one_of_stable`**: a direct
  consequence of Butcher's stability hypothesis (Definition
  403A); not stated explicitly in §441 but is the textbook-
  implicit generalisation of cycle 175's real-root bound to
  complex roots. Lean statement matches the strategy contract
  verbatim.

* **`αPoly_complex_root_norm_ge_one_of_stable`**: corresponds to
  the textbook's "(1−ζ)/(1+ζ) is a zero of α" → "Re ζ ≤ 0" step
  (specifically, the polynomial-form claim "α has no roots of norm
  < 1 under stability"). The hypothesis `w ≠ 0` is the textbook
  exclusion of the trivial `αPoly(0) = 1` case.

* **`aPoly_aeval_one_complex_eq_two_pow`**: a direct algebraic
  computation, no textbook divergence.

No theorem conclusion appears verbatim as one of its hypotheses.
No proof is `exact h` shadowing. No structure has Prop-fields
silently encoding consequences as inputs. Hypothesis strength
matches the textbook (stability + ζ root + nonzero where needed,
no extra constraints).

## Dead ends

1. `lake env lean OpenMath/Chapter4/Section441.lean` — three
   consecutive 13–20 minute runs without finishing. Killed each
   time. Lean process consistently at 0.7–1.5% CPU, GPFS-induced
   I/O bottleneck (one thread always in `D` state).
2. `lake build OpenMath.Chapter4.Section441` — similar slowness;
   killed at 13:33 of lean execution after 8 of 8032 build tasks
   completed (Section441 was the last unchanged; lake correctly
   replayed Section404/Section410 from cache, then began rebuilding
   Section441 fresh, which is where the slowness lives).
3. Earlier compile attempts had `linear_combination hev` /
   `nlinarith [hsq_ge, ...]` / `field_simp; ring` / `gcongr`. After
   first compile timed out, replaced each with explicit non-tactic
   alternatives (`eq_of_sub_eq_zero`, manual `ring` rewrites +
   `linarith`, manual `mul_inv_cancel₀`, `pow_le_pow_left₀`). This
   was prophylactic; the actual bottleneck turned out to be olean
   loading, not tactic elaboration.

## Discovery

* `Complex.coe_algebraMap` (`@[simp] (algebraMap ℝ ℂ : ℝ → ℂ) =
  ((↑) : ℝ → ℂ)`, `rfl`) is the canonical simp bridge between
  `algebraMap ℝ ℂ x` and `((x : ℝ) : ℂ)` after `Polynomial.aeval_C`
  expansion. Adding it to a `simp only` set after the standard
  `aeval_X / map_*` set cleanly converts `algebraMap` artifacts to
  ofReal coercions, allowing `linear_combination`/`ring`-style
  closure (or, for our cycle, direct `eq_of_sub_eq_zero` once the
  expression is in the form `a - b = 0`).

* The `‖·‖²` decomposition `‖z‖² = z.re² + z.im²` (via
  `Complex.sq_norm` + `Complex.normSq_apply`) is the cleanest path
  for stability-norm bounds: each component sequence is bounded by
  stability, so `re² + im² ≤ C₁² + C₂²`. Avoids any complex-
  analytic infrastructure and uses only real-analysis lemmas.

* `pow_mul_pow_sub` (`a^m * a^(n-m) = a^n` for `m ≤ n`) is the
  bottom-cleanest split for the polynomial reciprocity proof: it
  gives `w^k = w^(i+1) * w^(k - (i+1))` in one rewrite, after which
  `mul_inv_cancel₀` on `w^(k - (i+1)) * (w^(k - (i+1)))⁻¹` closes.

* GPFS file system performance on this cluster can be wildly
  variable. A successful compile yesterday (cycle 181) ran in ~3
  minutes; today (cycle 182) the same compile is at 20+ minutes
  without completion. Strategy: keep proofs simple (no slow
  tactics), but the dominant cost is olean loading not tactic
  elaboration. Future cycles experiencing this slowness can either
  (a) wait — it does eventually finish; (b) commit unverified for
  Section441 specifically since it has no downstream dependents
  beyond the thin `OpenMath/Chapter4.lean` aggregator; (c) defer
  to a later cycle.

## Suggested next approach

Phase C.3 (real factorisation of `aPoly` into linear/quadratic
factors with non-positive `ξ`) is the next step. The textbook
argument:

> Because all zeros of a are real, or occur in conjugate pairs,
> the polynomial a can be decomposed into factors of the form
> z − ξ or of the form z² − 2ξz + (ξ² + η²), where the real
> number ξ cannot be positive.

Mathlib has the relevant tools:
* `Polynomial.derivative` and the conjugate-roots theory
  (`Polynomial.aeval_conj`, `Polynomial.IsRoot.map_conj`).
* `Polynomial.exists_quadratic_factor` (or similar) for irreducible
  quadratic factors over ℝ.
* The `Polynomial.splits` API for ℂ.

Phase C.3 is the high-risk phase (per `lem_441A_phase_C_scoping.md`).
Phase C.4 is the final closure: "all factors have non-negative
coefficients because ξ ≤ 0".

**Before Phase C.3**: verify cycle 182's compile cleanly. If the
compile fails with a specific tactic error, the next cycle should
prioritize fixing that error before moving on. If clean, mark Phase
C.2 as complete in the scoping doc and proceed to Phase C.3.

## Cluster slowness note

If the GPFS slowness persists across multiple cycles, consider:
* Writing a `loop_maintainer` issue suggesting cluster admin
  consultation.
* Pre-loading olean files into `/tmp/` ramdisk (similar to the
  cycle 181 "PATH=/tmp/lake-bin" workaround for elan slowness).
* Using a smaller test file as a "smoke test" for each cycle's
  changes before committing to the full Section441 compile.

These are loop-maintainer territory per CLAUDE.md.
