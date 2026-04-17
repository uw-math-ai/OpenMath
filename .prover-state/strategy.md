# Strategy — Cycle 95

## Status
- **0 sorrys** in committed codebase. CI GREEN (commit a79033e).
- Chapters 1–3 extensively formalized (30 files, ~200 theorems).
- Cycle counter is 93 in `.prover-state/cycle` — **set it to 95** at start of work.
- 5 Aristotle results completed for OneStepConvergence — **already incorporated manually in cycle 94, skip them**.
- No pending Aristotle jobs.

## Target: Formalize Picard–Lindelöf existence and uniqueness (Iserles §1.1, thm:110C)

### Why this target
This is the most fundamental unformalized theorem in the textbook. It states:
> If f is continuous in x and Lipschitz in y, then y' = f(x,y), y(a) = y₀ has a unique solution on [a,b].

We have formalized **numerical convergence** (Dahlquist equivalence, one-step convergence, BDF convergence) but NOT the **existence of the exact solution** that these numerical methods approximate. This is a genuine gap.

Additionally:
- It is Tier 1 in the extraction topological order (unblocks 11+ downstream entities).
- Entity data: `extraction/formalization_data/entities/thm_110C.json`.
- It requires `def:110A` (Lipschitz condition) and `lem:110B` (contraction mapping / Banach fixed-point).
- Mathlib has the Picard–Lindelöf theorem in `Mathlib.Analysis.ODE.PicardLindelof`. The task is to state the clean textbook version and connect it to Mathlib.

### What to formalize

Create `OpenMath/PicardLindelof.lean` with:

1. **def:110A — Lipschitz condition in second variable**: `IsLipschitzInY f L a b` means `∀ x ∈ [a,b], ∀ Y Z, ‖f(x,Y) - f(x,Z)‖ ≤ L * ‖Y - Z‖`. We already have ad-hoc versions in `OneStepConvergence.lean`; create the canonical definition matching Iserles Definition 1.1.

2. **thm:110C — Picard–Lindelöf theorem**: If f : ℝ × E → E is continuous in x and Lipschitz in y with constant L, then the IVP y' = f(x,y), y(a) = y₀ has a unique solution on [a,b]. State this as:

```lean
/-- Picard–Lindelöf theorem (Iserles Theorem 1.1).
If f is continuous and Lipschitz in y, the IVP has a unique solution. -/
theorem picardLindelof_exists_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {a b : ℝ} {L : ℝ} {y₀ : E}
    (hab : a < b)
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hf_lip : ∀ x ∈ Set.Icc a b, ∀ y z : E, ‖f x y - f x z‖ ≤ L * ‖y - z‖)
    (hL : 0 ≤ L) :
    ∃! y : ℝ → E, y a = y₀ ∧
      ∀ x ∈ Set.Icc a b, HasDerivAt y (f x (y x)) x := by
  sorry
```

3. **Continuous dependence on initial data**: If y and z solve the same ODE with different initial data y₀ and z₀, then `‖y(x) - z(x)‖ ≤ ‖y₀ - z₀‖ * exp(L * (x - a))`. This connects to our `Stiffness.lean` (oneSidedLipschitz_solution_bound).

### Proof approach

**Option A (recommended): Connect to Mathlib's `ODE.IVP_globalUnique_of_lipschitzOnWith`**

Mathlib's `Mathlib.Analysis.ODE.PicardLindelof` has:
- `ODE.exists_forall_hasDerivWithinAt_Icc_eq` — existence
- `ODE.IVP_globalUnique_of_lipschitzOnWith` — uniqueness under Lipschitz

The proof reduces to:
1. Construct the Mathlib-compatible hypothesis types from our cleaner statement.
2. Apply the Mathlib theorems.
3. Package the result in our notation.

**Start by checking what Mathlib provides:**
```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
export LEAN_CC=/usr/bin/gcc
# Search for Picard-Lindelöf in Mathlib
grep -r "PicardLindelof\|picardLindelof\|picard_lindelof" /tmp/OpenMath-lake/packages/mathlib/Mathlib/
```

Use `lean_local_search` and `lean_leansearch` to find the exact Mathlib API.

**Option B (fallback): Direct proof via Banach fixed-point**

If the Mathlib API is awkward to connect:
1. Define the Picard integral operator T: `(Ty)(x) = y₀ + ∫_a^x f(s, y(s)) ds`.
2. Show T is a contraction on C([a,b], E) with the weighted sup-norm `‖y‖_λ = sup_{x∈[a,b]} e^{-λ(x-a)} ‖y(x)‖` for λ > L.
3. Apply Banach fixed-point theorem (`Mathlib.Topology.MetricSpace.Contracting`).
4. Fixed point = unique solution.

### Sorry-first workflow
1. Write all definitions and theorem statements with `sorry`.
2. Verify compilation: `lake env lean OpenMath/PicardLindelof.lean`.
3. Submit ~5 Aristotle jobs on the sorrys.
4. Sleep 30 min, check once.
5. Close remaining manually using Lean LSP tools.
6. Verify, commit, push.

### What NOT to try
- Do NOT try to prove the Cauchy-Peano theorem (existence without uniqueness) — this requires Arzelà–Ascoli which is much harder.
- Do NOT implement the full Picard iteration sequence — just existence/uniqueness.
- Do NOT add `maxHeartbeats` above 200000.
- Do NOT modify existing files (OneStepConvergence.lean, Stiffness.lean) — create a new file.
- Do NOT try to formalize the proof from scratch if Mathlib already has it — wrapper/connection is fine.

### After success
1. Update `plan.md`: add "Picard–Lindelöf" section under Chapter 1, mark as `[x]`.
2. Update `extraction/formalization_data/lean_status.json` for entities def:110A, thm:110C.
3. Commit: `cycle 95: formalize Picard–Lindelöf existence and uniqueness (Iserles 1.1)`
4. Push.
5. Write task results to `.prover-state/task_results/cycle_095.md`.

### Build
```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
export LEAN_CC=/usr/bin/gcc
export LIBRARY_PATH="/tmp/lean4-toolchain/lib:/tmp/lean4-toolchain/lib/lean"
lake env lean OpenMath/PicardLindelof.lean
```

### Stretch goals (if main target completes early)
- **Gronwall inequality** (textbook version): `u(x) ≤ α + ∫_a^x β u(s) ds ⟹ u(x) ≤ α exp(β(x-a))`. Connect to Mathlib's `gronwall_bound_of_norm_deriv_right_le`.
- **Continuous dependence on initial data**: Exponential bound on solution difference from Lipschitz constant.
- **Perturbation bound**: If ŷ satisfies y' = f(x,y) + δ(x), then `‖y(x) - ŷ(x)‖ ≤ (max|δ|/L)(exp(L(b-a)) - 1)`.
