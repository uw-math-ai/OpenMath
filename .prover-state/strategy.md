# Strategy — Cycle 118

## Status
- **0 sorry's project-wide** (maintained since cycle 116)
- Aristotle results from cycle 117 (4 projects) are already incorporated — the manual proofs done in cycle 117 match or supersede all returned results. No incorporation needed.
- Next formalization target per `plan.md`: Order star infrastructure / Theorem 355A+

## Priority 1: Order Arrow Definitions and Theorem 355B (~60 min)

### Why this target
- Plan.md lists "Order star infrastructure / Theorem 355A+" as the #1 next target
- `OpenMath/OrderStars.lean` has basic order-star definitions (𝒜⁺, 𝒜⁻, 𝒜⁰) and properties but is MISSING the order arrow infrastructure (def:355A) needed for the Ehle barrier chain
- The tangent directions theorem (thm:355B) has a local proof (Taylor expansion near origin) that is achievable in Lean
- This is the foundational step toward the Ehle barrier (thm:355G)

### Step 1a: Add order arrow definitions (def:355A)

Read `extraction/formalization_data/entities/def_355A.json` for context.

Add to `OpenMath/OrderStars.lean`:

```lean
/-- The **order web**: locus where φ(z) = R(z)exp(-z) is real and positive. -/
def orderWeb (R : ℂ → ℂ) : Set ℂ := {z | ∃ r : ℝ, 0 < r ∧ R z * exp (-z) = ↑r}

/-- A ray direction θ from the origin is an **up-arrow direction** if
    t ↦ ‖R(t·exp(iθ))·exp(-t·exp(iθ))‖ is increasing at t = 0⁺. -/
def IsUpArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, 1 < ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖

/-- A ray direction θ from the origin is a **down-arrow direction** if
    t ↦ ‖R(t·exp(iθ))·exp(-t·exp(iθ))‖ is decreasing at t = 0⁺. -/
def IsDownArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖ < 1
```

**Note:** The textbook defines arrows as full paths, not just directions at the origin. However, the tangency theorem (355B) only concerns directions at 0, so direction-only definitions suffice for now. Full path definitions can be added later if needed.

### Step 1b: Prove Theorem 355B (arrow tangency directions)

Read `extraction/formalization_data/entities/thm_355B.json` for the statement.

**Theorem 355B**: Let R be a rational approximation to exp of exact order p, so that `R(z) = exp(z) - C·z^{p+1} + O(z^{p+2})` with `C ≠ 0`. Then:
- If C < 0: up-arrow directions at the rays `2kπ/(p+1)` for k = 0, ..., p
- If C > 0: down-arrow directions at the rays `2kπ/(p+1)` for k = 0, ..., p

**Proof approach for Lean:**

The key identity is: for z = r·exp(iθ) with r small,
```
φ(z) = R(z)·exp(-z) = 1 - C·r^{p+1}·exp(i(p+1)θ) + O(r^{p+2})
```

So `‖φ(z)‖² ≈ 1 - 2C·r^{p+1}·cos((p+1)θ) + O(r^{p+2})`.

When `C < 0` and `θ = 2kπ/(p+1)`: `cos((p+1)θ) = cos(2kπ) = 1`, so `‖φ‖² ≈ 1 + 2|C|r^{p+1} > 1` → up arrow. ✓

**Concrete Lean proof structure:**
1. Assume R has order p at 0: `R z = exp z - C * z^(p+1) + g z` where `g z = O(z^{p+2})`
2. Compute `‖R(z)·exp(-z)‖²` near 0 using `1 - C·z^{p+1} + g(z)·exp(-z)`
3. Show the dominant term in `‖φ‖² - 1` has sign `-2C·cos((p+1)θ)` at angle θ
4. For specific angles `θ = 2kπ/(p+1)`, the cosine is 1, giving the arrow direction

**Sorry-first:** Write the theorem statement with sorry, verify it compiles. Then submit to Aristotle. While waiting, prove the p=1 case (forward Euler) and p=2 case (trapezoidal/backward Euler) as concrete instances.

### Step 1c: Prove concrete instances

As sanity checks that also constitute standalone theorems:

1. **Forward Euler** (R(z) = 1+z, p=1, C=1/2 > 0): down arrows at θ=0 and θ=π. The down arrow at θ=0 means ‖φ(r)‖ < 1 for small positive r (positive real axis is in 𝒜⁻). Already partially captured by `forwardEuler_neg3_mem_orderStarPlus`.

2. **Backward Euler** (R(z) = 1/(1-z), p=1, C=-1/2 < 0): up arrows at θ=0 and θ=π.

3. **Trapezoidal** (R(z) = (1+z/2)/(1-z/2), p=2, C=-1/12 < 0): up arrows at θ = 0, 2π/3, 4π/3.

These are nice concrete verifications that compile independently.

### Step 1d: Aristotle submission

After writing the sorry-first skeleton:
1. Submit the full `OrderStars.lean` to Aristotle
2. Submit the `355B` tangency proof as a standalone lemma
3. Sleep 30 minutes, then check results once

## Priority 2: Extend A-Stability Characterizations via Order Stars (~30 min)

Only attempt after Priority 1 is complete or blocked.

### Step 2a: Theorem 355F (A-stability criterion)

Read `extraction/formalization_data/entities/thm_355F.json`.

**Theorem 355F**: A Runge-Kutta method is A-stable iff no up arrow that terminates at a pole crosses the imaginary axis.

This is hard to formalize without path topology, but a WEAKER version is achievable:

**Weak version**: If all poles of R are in the open right half-plane and ‖R(iy)‖ ≤ 1 for all real y, then the method is A-stable.

This is essentially Theorem 351B (already formalized in `AStabilityCriterion.lean`). Check if 355F adds anything beyond 351B. If not, document the connection and move on.

### Step 2b: Ehle wedge concrete verification

Verify the Ehle wedge for specific Padé pairs using existing infrastructure:
- Show R_{2,1} is NOT A-stable (the denominator is linear, can find explicit z with Re(z) ≤ 0 and ‖R(z)‖ > 1)
- Connect this to `pade21_not_inEhleWedge` already in OrderStars.lean

## Priority 3: Rooted Tree Infrastructure (if time permits, ~20 min)

Only attempt if Priorities 1-2 are complete.

Read `OpenMath/RootedTree.lean` and assess:
1. Can the `BTree` child representation be upgraded from `List` to `Multiset`?
2. Are there concrete trees of order 4 already? (Yes, per the explore agent)
3. Can `elementary_differential` and `weight` functions be defined?

This unblocks Collocation implications (342j, 342k, 342l).

## What NOT to Try

1. **Do NOT attempt the full Ehle barrier proof (thm:355G)** — it requires arrow path topology (termination at poles/zeros, 355C-355E) which needs winding numbers that Mathlib doesn't have.
2. **Do NOT work on Padé recurrences** (352D) — blocked on factorial-sum algebra, dead end per cycles 103-106.
3. **Do NOT increase maxHeartbeats** above 200000.
4. **Do NOT try to formalize 355C (arrow termination)** — requires asymptotic analysis at infinity in the complex plane, well beyond current Mathlib.
5. **Do NOT spend >30 min on any single sorry.** If stuck, submit to Aristotle and move on to the next task.
6. **Do NOT re-attempt the Aristotle results from cycle 117.** They are already incorporated.

## Build Commands

```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
lake env lean OpenMath/OrderStars.lean
```

If `lake` hangs, verify PATH starts with `/tmp/lake-bin:/tmp/lean4-toolchain/bin`.

## End-of-Cycle Checklist

- [ ] All modified `.lean` files compile with 0 sorry's (or sorry's are documented with issue files)
- [ ] Write `.prover-state/task_results/cycle_118.md`
- [ ] Update `.prover-state/cycle` to `118`
- [ ] Update `.prover-state/history.jsonl` with cycle summary
- [ ] Commit and push all changes
