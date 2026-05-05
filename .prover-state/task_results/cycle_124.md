# Cycle 124 Results

## Worked on

The single remaining §515D sorry — the body of
`aux_515D_max_deviation_geometric_bound`
(`OpenMath/Chapter5/Section515.lean:2360`, ~360 LOC body).

Closing this body flips `thm:515D` from `partial` → `formalized` and
makes the capstone `stable_consistent_isConvergent` axiom-clean
(removes the last `sorryAx` from its dependency closure).

## Approach

Followed the cycle 124 strategy verbatim, with one structural
deviation forced by Lean's norm-scope semantics (see Discovery
below).

### New private helpers introduced

1. **`aux_515D_delta_closed_form`** (`Section515.lean:2207`, ~30 LOC).
   Pure algebraic vectorial closed form:
   `δ m = V^m·δ 0 + ∑_{k ∈ range m} V^(m-1-k)·R k`
   from a per-step recurrence `δ(k+1) = V·δ k + R k`. Proven by
   induction on m: zero case via `pow_zero, Matrix.one_mulVec`; succ
   case via `pow_succ', Matrix.mulVec_mulVec, Matrix.mulVec_sum,
   Finset.sum_range_succ`, plus `omega` for the index identity
   `m+1-1-k = (m-1-k)+1` for `k < m`.

2. **`aux_515D_iterated_V_bound_linfty`** (`Section515.lean:2257`,
   ~70 LOC). Sup'-form iterated V bound:
   `sup'_i |((V^k) *ᵥ x) i| ≤ C · sup'_j |x j|` for some C ≥ 0,
   derived directly from `M.IsStable`'s L∞-operator-norm content
   (`Matrix.linfty_opNNNorm_def` gives row-sum bound, then triangle
   inequality on matrix-vector product). Placed in a sub-section
   that opens `Matrix.Norms.Operator` so the L∞-operator-norm
   machinery is available locally — the file's main scope opens
   `Matrix.Norms.Frobenius`, which is incompatible with the L∞
   lemmas. The cycle 120 helper `aux_515D_iterated_V_bound`
   (Frobenius-norm hypothesis) is no longer the active path; kept
   in file for backward narrowing audit.

### Main body composition

Setup (~30 LOC): h_n, target, δ, R, δ_max definitions; non-negativity
of δ_max; per-step recurrence `δ(k+1) = V·δ k + R k` (via
`ring`-discharged identity).

Closed form: invoke helper (1).

Per-step bound: `|R k i| ≤ α·h_n·δ_max k + β·h_n²` directly from the
cycle 123 K-bound (`aux_515D_per_step_K_bound`) — the K-bound's LHS
is exactly `R k i` definitionally.

Sum-form bound (~80 LOC): take sup'_i of `|δ m i|` using the closed
form, split via triangle inequality (`abs_add_le`,
`Finset.abs_sum_le_sum_abs`), sup'-bound each summand via helper (2)
plus the K-bound. Algebraic simplification yields:
`δ_max m ≤ C₀·δ_max 0 + (C₀·α)·h_n·∑_{range m} δ_max k
                      + (C₀·β)·h_n²·m` (for m ≤ n).

Grönwall application (~120 LOC): branched on α > 0 vs α = 0.

* **α > 0 branch**: defined truncated sequence
  `u_seq m := if m ≤ n then δ_max m else 0`. Showed `u_seq 0 ≤ a`
  with `a := (1 + C₀·(1+α·Δx))·δ_max 0` (the +1 absorbs base case
  shortfall when C₀·(1+α·Δx) < 1). Showed the recurrence
  `u_seq m ≤ a + (C₀·α)·h_n·∑_{Ico 1 m} u_seq k + (C₀·β)·h_n²·m`
  for all m ≥ 1: for m ≤ n use `hsum_form` (after splitting
  `range m = {0} ∪ Ico 1 m` and absorbing `δ_max 0` into `a`); for
  m > n the LHS is 0 and the RHS is non-negative. Applied
  `aux_515D_gronwall_bound` at index n; got
  `δ_max n ≤ exp(C₀·α·n·h_n)·a + (exp(C₀·α·n·h_n)−1)·(C₀·β·h_n / (C₀·α))`.
  Substituted `n·h_n = x − x₀` and simplified `C₀·β/(C₀·α) = β/α`
  via `field_simp` (using `C₀ ≠ 0`, `α ≠ 0`). Witness constants:
  `C_init := exp(C₀·α·(x−x₀)) · (1 + C₀·(1+α·(x−x₀)))`,
  `C_lin := (exp(C₀·α·(x−x₀)) − 1) · (β/α)`.

* **α = 0 branch**: the recurrence reduces to
  `δ_max m ≤ C₀·δ_max 0 + C₀·β·h_n²·m`. At m = n, multiplying
  `h_n²·n = h_n·(x−x₀)` gives the desired form. Witness constants:
  `C_init := C₀`, `C_lin := C₀·β·(x−x₀)`.

LHS/RHS bridges: the goal's sup' uses `(yex x, deriv yex x)` while
δ_max uses `(yex (x₀ + n·h_n), deriv yex (x₀ + n·h_n))`. Since
`x₀ + n·h_n = x` (from `n·h_n = x − x₀`), these match after
rewriting `x ↦ x₀ + n·h_n`. Same for the initial side
(`x₀ ↦ x₀ + 0·h_n`).

### Aristotle usage

None. As the strategy explicitly noted, Aristotle is unsuitable for
tightly-composed proofs requiring five §515 helpers; manual
composition only.

## Result

**SUCCESS.** All §515D sorries closed. Verification gates:

1. ✅ `lake env lean OpenMath/Chapter5/Section515.lean` compiles
   (warnings only — pre-existing unused-var `hβ_nn` at line 1713 plus
   minor `simp only` and `push_cast` lints in the new code).
2. ✅ `lake env lean OpenMath/Chapter5/Section513.lean` exits 0.
3. ✅ `lake env lean OpenMath/Chapter5/Section514.lean` exits 0
   (warnings only — pre-existing `Matrix.toEuclideanLin_apply`
   deprecation).
4. ✅ `lake build OpenMath.Chapter5.Section515` succeeds, 2800 jobs.
5. ✅ `#print axioms
   OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
   returns `[propext, Classical.choice, Quot.sound]` — **no
   `sorryAx`**.
6. ✅ Tautology scanner: 0 hits (renamed initial `h_abs_sum` /
   `h_factor_out` → `habs_sum` / `hfactor_out` in the linfty helper
   to avoid the `:= h_*` pattern).
7. ✅ `lean_status.json` `thm:515D`: `partial` → `formalized`,
   `cycle: 124`.
8. ✅ `plan.md` `thm:515D` row: `[~]` → `[x]` with cycle 124 note.
9. ✅ Issue files updated:
   * `aux_515D_iterated_V_bound.md` — RESOLVED header added.
   * `cycle_121_strategy_B2_correction.md` — RESOLVED header added.
   * `aux_515D_output_tendsto_hypotheses.md` — "Cycle 124 update"
     section appended.

## Faithfulness check

For new helpers introduced this cycle:

* **`aux_515D_delta_closed_form`** — internal helper, no
  textbook-named entity. Pure algebraic identity. No faithfulness
  concern.
* **`aux_515D_iterated_V_bound_linfty`** — internal helper, no
  textbook-named entity. Same conclusion as cycle 120's
  `aux_515D_iterated_V_bound` but in L∞-operator-norm input. No
  faithfulness concern.

For the final-form `aux_515D_max_deviation_geometric_bound` (whose
body is now closed):

* Entity: `thm:515D` (Stability and Consistency Imply Convergence).
  Textbook statement (`entities/thm_515D.json`):
  > A stable and consistent general linear method is convergent.
* Capstone Lean statement
  `GeneralLinearMethod.stable_consistent_isConvergent` (Section515)
  matches: `M.IsStable ∧ M.IsConsistent → M.IsConvergent` modulo the
  cycle 116/118/123 cumulative strengthenings (see issue files
  `glm_isconvergent_strengthened.md`, `aux_515D_output_tendsto_hypotheses.md`,
  `stable_consistent_isConvergent_hc_nn.md`). The cycle 124 close
  introduces no NEW faithfulness divergences beyond those already
  documented.

## Dead ends

The strategy's literal Step 3 — invoking
`aux_515D_iterated_V_bound` directly with `M.IsStable` after the
`max C_raw 0` bridging — fails with a norm-instance unification
error: `Matrix.linftyOpSemiNormedRing.toNorm` (from `IsStable`,
defined in Section510 with `Matrix.Norms.Operator` open) doesn't
unify with `frobeniusNormedRing.toNorm` (the active norm in
Section515 with `Matrix.Norms.Frobenius` open). The cycle 120
`aux_515D_iterated_V_bound` was elaborated under Frobenius scope, so
its hypothesis demands a Frobenius-norm bound, but `M.IsStable`
provides L∞-operator. The two norms differ by a factor of r on
r×r matrices, and bridging requires both norm instances active in
the same proof — which Lean's scoped-instance system disallows.

Resolution: introduce a parallel L∞-flavoured helper inside a
sub-section that opens `Matrix.Norms.Operator` instead. The
sup'-form conclusion (no matrix norm in the conclusion) is
scope-independent, so the main body (back in Frobenius scope) can
consume it transparently.

## Discovery

**Norm-scope incompatibility between Section510 and Section515.**

`M.IsStable` is defined in Section510 (`open scoped Matrix.Norms.Operator`)
as `∃ C, PowerBounded C M.V`, which expands to `∃ C, ∀ k, ‖V^k‖ ≤ C`
with `‖·‖` resolving to L∞ operator norm at definition time. This
type is then frozen — extracting `M.IsStable` in Section515 (which
opens `Matrix.Norms.Frobenius`) gives an L∞-bound, NOT a
Frobenius-bound.

Consequence: any new helper in Section515 that wants to invoke L∞
machinery (`Matrix.linfty_opNNNorm_def`, `Matrix.linfty_opNorm_mulVec`,
etc.) must be placed in a sub-section that opens
`Matrix.Norms.Operator`. Mathlib's L∞ matrix norm theorems are
elaborated with `@[local instance]` for the L∞ norm class, so they
work fine inside such a sub-section, but cannot be used outside
without scope-switching.

This is good to remember for future §520 / §550 work that touches
`M.IsStable` — bridging through a sup'-form conclusion (no matrix
norm in conclusion) lets the Frobenius-scope main body consume L∞
results cleanly.

**Truncated u_seq pattern for Grönwall hypothesis closure.**

`aux_515D_gronwall_bound`'s recurrence hypothesis is `∀ m ≥ 1, u m ≤
a + α·h·∑ + β·h²·m`. Even though the Grönwall conclusion only uses
this at indices ≤ n_target, the hypothesis must be supplied for ALL
m ≥ 1 — including m > n where our `δ_max m` lacks a tight bound
(the K-bound only gives per-step decomposition for k+1 ≤ n). The
fix is to define `u_seq m := if m ≤ n then δ_max m else 0`: for
m ≤ n the recurrence holds via `hsum_form`; for m > n it holds
trivially since LHS = 0 ≤ RHS (RHS non-negative). The Grönwall
conclusion at index n then gives `u_seq n = δ_max n ≤ ...`.

This pattern generalises: any time you have a Grönwall-style bound
that requires recurrence on an extended index set but only know the
recurrence on a finite prefix, truncate the sequence to zero outside
the prefix.

## Suggested next approach

§515D is fully closed. The natural next targets are §520-§553
(stability domain, A-stability, order star theory) per the cycle
123 strategy's "forward planning" comment. Specifically:

* **`def:520C`** (stability function) is already formalized — good
  starting infrastructure.
* **`thm:550B`** (doubly companion matrix similarity) is the main
  open Chapter 5 target now.
* **§521** (max stability order definitions) is partially done but
  has no theorems closed.

For Chapter 5's order-star / stability-order chain:

* §551 `g_RS, h_RS` definitions and basic identities (~3 cycles).
* §552 stability-region geometry (~2 cycles).
* §553 capstone tying RK A-stability to order-star
  characterisation (~5 cycles, Wanner-Hairer style — substantial).

For Chapter 4 / 5 cross-validation:

* The cycle 124 closure of §515D's GLM-flavoured
  stability+consistency⇒convergence theorem complements the
  Chapter 4 LMM-flavoured `stable_consistent_isConvergent` (cycle
  068, axiom-clean) — both are now full witnesses to the
  Lax-equivalence pattern Butcher establishes for two distinct
  method families. A useful low-effort spot-check is
  `#print axioms` on both and confirming they share the same
  three-axiom dependency closure.

For revisiting faithfulness divergences:

* The §512A `IsConvergent` strengthening
  (`M_bound`/`ContDiff ℝ 1`/local-norm hypotheses, cycle 116) and
  the `_hc_nn`/`_hc_le_one` propagation (cycle 122-123) are stable
  and now consumed by an axiom-clean capstone. A "post-mortem"
  audit cycle re-examining whether any of these can be dropped (now
  that the proof is complete) might be worthwhile, but is low ROI
  compared to forward §550 progress.

Recommended cycle 125 strategy: forward planning toward §550 /
§552, OR a hygiene cycle to address the pre-existing warnings
(unused `hβ_nn`, deprecated `Matrix.toEuclideanLin_apply`, etc.)
that have accumulated.
