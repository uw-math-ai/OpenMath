# Strategy — Cycle 119

## Status
- **0 sorry's project-wide** (maintained since cycle 116)
- Aristotle results from cycle 118 (Forward/Backward Euler arrows) are already incorporated — the manual proofs done in cycle 118 match the returned results. No incorporation needed.
- Order arrow infrastructure (def:355A) and 5 concrete instances are complete.
- Plan.md lists order star continuation and two in-progress items: Padé recurrences (352D), rooted trees (301A).

## Priority 1: Theorem 355F — A-stability criterion via order stars (~40 min)

### Why this target
- This is the next theorem in the 355 chain after the infrastructure completed in cycle 118
- The proof is SHORT and self-contained (see textbook proof below)
- It connects order star geometry to the existing A-stability framework
- It is the key necessary condition that feeds into the Ehle barrier (355G)

### What the theorem says (textbook)
A Runge-Kutta method is A-stable **only if**:
1. All poles of R(z) lie in the open right half-plane, AND
2. No up arrow of the order web intersects or is tangential to the imaginary axis.

### Proof approach
The textbook proof is elementary:
- Condition (1) is obvious (if R has a pole at z₀ with Re(z₀) ≤ 0, then |R(z)| → ∞ near z₀).
- Condition (2): if an up arrow intersects the imaginary axis at some point iy, then |R(iy)·exp(-iy)| > 1. Since |exp(-iy)| = 1, this gives |R(iy)| > 1, contradicting A-stability.

### Lean formalization plan

**Statement:**
```lean
/-- **Theorem 355F**: A-stability requires no up arrows touch the imaginary axis.
    If R is A-stable (‖R(z)‖ ≤ 1 for Re(z) ≤ 0), then for any pure imaginary z = iy,
    z ∉ orderStarPlus R (equivalently, z ∈ orderStarMinus R ∪ orderStarBdry R). -/
theorem aStable_imagAxis_not_orderStarPlus (R : ℂ → ℂ)
    (hA : ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1)
    (y : ℝ) : (↑y * I) ∉ orderStarPlus R
```

**Proof sketch:**
1. Unfold `orderStarPlus`: need to show ¬(1 < ‖R(iy) * exp(-iy)‖)
2. Use `orderStar_norm_eq` or `Complex.norm_exp_ofReal_mul_I` to get `‖exp(-iy)‖ = 1`
3. So `‖R(iy) * exp(-iy)‖ = ‖R(iy)‖ · 1 = ‖R(iy)‖`
4. By A-stability hypothesis (Re(iy) = 0 ≤ 0): `‖R(iy)‖ ≤ 1`
5. `¬(1 < 1)`

This should be a 5-line proof using existing infrastructure.

**Also state the pole condition as a separate lemma:**
```lean
/-- A-stable methods have no poles in the closed left half-plane. -/
theorem aStable_no_pole_left_half (R : ℂ → ℂ) (hR : Continuous R)
    (hA : ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1)
    (z : ℂ) (hz : z.re ≤ 0) : R z ≠ 0 → True  -- not needed as a separate statement
```

Actually, the pole condition is automatically captured since A-stability bounds ‖R‖ ≤ 1 on Re ≤ 0. For rational R, this means no poles in the closed left half-plane. State it simply:

```lean
/-- A-stable stability functions are bounded on the closed left half-plane,
    hence have no poles there (for meromorphic R). -/
theorem aStable_bounded_left_half (R : ℂ → ℂ)
    (hA : ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1)
    (z : ℂ) (hz : z.re ≤ 0) : ‖R z‖ ≤ 1 := hA z hz
```

### After 355F: Prove Theorem 355D (counting inequality)

**Theorem 355D**: For a rational approximation to exp of order p with numerator degree n and denominator degree d, the number of down arrows terminating at zeros (n̂) and up arrows terminating at poles (d̂) satisfy n̂ + d̂ ≥ p.

This requires formalizing the concept of "arrows terminating at poles/zeros" (355C), which is more involved. **Skip 355D unless 355F is done quickly.**

### Sorry-first approach
1. Write the theorem statement for 355F, verify it compiles
2. Prove it immediately (should be short)
3. Add corollary: for concrete methods, compute which imaginary-axis points are NOT in 𝒜⁺

## Priority 2: Theorem 355B — Arrow tangency directions (general statement) (~50 min)

### Why this target
- Cycle 118 proved 5 concrete arrow instances but NOT the general theorem
- The general statement with `Asymptotics` would be the cleanest formalization
- However, the general proof requires working with `O(z^{p+2})` which needs `Asymptotics.IsLittleO` / `IsBigO`

### Approach: State with explicit error hypothesis, prove for concrete Padé pairs

**Statement (with explicit hypothesis):**
```lean
/-- **Theorem 355B**: If R(z) = exp(z) - C·z^{p+1} + O(z^{p+2}) with C ≠ 0,
    then up arrows (C < 0) or down arrows (C > 0) in directions 2kπ/(p+1). -/
theorem arrow_tangency_directions (R : ℂ → ℂ) (p : ℕ) (C : ℝ) (hC : C ≠ 0)
    (hR : ∀ᶠ z in nhds 0, ‖R z - exp z + ↑C * z ^ (p+1)‖ ≤ ‖z‖ ^ (p+2) * someConstant)
    (k : Fin (p + 1)) :
    (C < 0 → IsUpArrowDir R (2 * ↑k * π / (↑p + 1))) ∧
    (C > 0 → IsDownArrowDir R (2 * ↑k * π / (↑p + 1)))
```

**Alternative: avoid Asymptotics entirely.** Instead, prove a version that takes a concrete polynomial remainder bound:

```lean
/-- For the (n,d)-Padé approximant with error constant C_{n+d+1}, the arrow
    directions at the origin are determined by the sign of C. -/
theorem pade_arrow_tangency (n d : ℕ) ...
```

### Concrete instances to prove
Build on the cycle 118 infrastructure:
- **Gauss-Legendre 2** (R = padeR 2 2, p=4, C=-1/720 < 0): up arrows at θ = 0, 2π/5, 4π/5, 6π/5, 8π/5
- **Radau IIA 2-stage** (R = padeR 1 2, p=3, C > 0): down arrows at θ = 0, π/2, π, 3π/2

These verify the theory on non-trivial examples.

### What NOT to try
- Do NOT attempt the full winding-number argument from 355C-355E
- Do NOT try to formalize "arrows terminate at poles" — needs path topology
- Do NOT use `Asymptotics.IsBigO` unless you're confident about the filter setup

## Priority 3: Update lean_status.json metadata (~10 min)

Many entities formalized in cycles 116-118 have stale metadata. Update:
- `def:355A` → done (OrderStars.lean: orderWeb, IsUpArrowDir, IsDownArrowDir)
- `thm:355B` → in_progress (concrete instances done, general statement TODO)
- `def:356A` → done (ANStability.lean: IsDJReducible)
- `def:357A` → done (BNStability.lean or ANStability.lean: depends on what 357A is)
- Verify thm:301A status

## Priority 4: Theorem 357D — BN-stability implies AN-stability for irreducible methods (~30 min)

Only if Priorities 1-2 are complete.

### What the theorem says
If an irreducible non-confluent Runge-Kutta method is BN-stable, then it is AN-stable.

### Approach
- Read the textbook proof from `extraction/formalization_data/entities/thm_357D.json`
- Check if the existing `IsDJReducible`, `IsANStable`, `IsBNStable` definitions suffice
- The proof likely uses the result that algebraic stability + DJ-irreducibility → positive weights (cor:356D, already proved)
- Sorry-first, submit to Aristotle

## What NOT to Try

1. **Do NOT attempt the full Ehle barrier (355G)** — requires arrow path topology (355C-355E) which needs winding numbers not in Mathlib.
2. **Do NOT work on Padé recurrences (352D)** — blocked on factorial-sum algebra, dead end per issue file.
3. **Do NOT increase maxHeartbeats** above 200000.
4. **Do NOT attempt 355C (arrow termination)** — requires asymptotic analysis at infinity.
5. **Do NOT spend >30 min on any single theorem.** If stuck, submit to Aristotle and move on.
6. **Do NOT re-attempt Aristotle results from cycle 118** — they are already incorporated.
7. **Do NOT attempt rooted tree upgrade (301A child representation)** — low priority, the current List-based representation works.

## Build Commands

```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
lake env lean OpenMath/OrderStars.lean
```

If `lake` hangs, verify PATH starts with `/tmp/lake-bin:/tmp/lean4-toolchain/bin`.

## End-of-Cycle Checklist

- [ ] All modified `.lean` files compile with 0 sorry's
- [ ] Write `.prover-state/task_results/cycle_119.md`
- [ ] Update `.prover-state/cycle` to `119`
- [ ] Update `.prover-state/history.jsonl` with cycle summary
- [ ] Commit and push all changes
