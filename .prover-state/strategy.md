# Strategy — Cycle 136

## Situation
- **Cycle**: 136
- **Project-wide sorrys**: 0 (maintained since cycle 134)
- **No pending Aristotle results to incorporate.** The two completed jobs (7b0236f3 and df09be51) were assessed in cycle 135: 7b0236f3's bridge theorem is already incorporated via `pade_exact_arrow_counts_of_countInequality`; df09be51 created stub modules for already-proved files (Collocation, RungeKutta, OrderConditions) — not usable.
- **Key infrastructure available**: `OrderArrowCountData`, `SatisfiesArrowCountInequality`, and `pade_exact_arrow_counts_of_countInequality` already exist in `OpenMath/OrderStars.lean` (added cycle 135).

## Priority 1: Housekeeping (do this FIRST)

### 1a. Update `plan.md`
The "Current Target" section is stale (still lists 342l sorry locations). Update it:
- Mark `[x]` on the `B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)` (342l) line — it is fully proved.
- Replace the "Current Target" block with:
  ```
  ## Current Target
  **Theorems 355D/355E/355G in `OpenMath/OrderStars.lean`: complete the order-star arrow counting pipeline and the Ehle barrier.**
  ```
- Remove the stale "Sorry locations" block (there are none).
- Remove the stale "Recent git history" block or update it.

### 1b. Update `lean_status.json`
- `thm:342C`: change status to `"done"` (all sub-items 342j/k/l/m/n/o/p are proved)
- `thm:301A`: leave as `"in_progress"` (child representation upgrade is still pending)

### 1c. Bump cycle counter
Write `136` to `.prover-state/cycle`.

### 1d. Append to `history.jsonl`
```json
{"cycle":136,"sorrys":0,"target":"Theorem 355D/355E arrow counting + Ehle barrier 355G","notes":"abstract arrow-count pipeline: axiomatize 355D, derive 355E, state 355G"}
```

## Priority 2: Complete the 355D → 355E → 355G Pipeline

### Goal
State Theorems 355D, 355E, and 355G in `OpenMath/OrderStars.lean`, with sorry-backed axioms ONLY for the parts that require global trajectory topology (documented in `.prover-state/issues/order_star_arrow_termination_topology.md`). Prove everything else.

### Mathematical Content

**Theorem 355D** (arrow inequality): For a rational approximation R to exp of order p with numerator degree n and denominator degree d, let ñ = #(down arrows at zeros) and d̃ = #(up arrows at poles). Then ñ + d̃ ≥ p.

**Theorem 355E** (Padé exact counts): For a Padé approximation with p = n + d, we have ñ = n and d̃ = d. (Squeeze argument from 355D.)

**Theorem 355G** (Ehle barrier): If R is an A-stable Padé approximation to exp with numerator degree n and denominator degree d, then n ≤ d ≤ n + 2.

### Concrete Steps

**Step 1**: Read `OpenMath/OrderStars.lean` lines 780–841 to see the existing `OrderArrowCountData` / `SatisfiesArrowCountInequality` / `pade_exact_arrow_counts_of_countInequality` infrastructure.

**Step 2**: State Theorem 355D. The cleanest formulation:
```lean
/-- Theorem 355D: For any rational approximation to exp of order p
with numerator degree n and denominator degree d, the arrow counts
satisfy ñ ≤ n, d̃ ≤ d, and ñ + d̃ ≥ p.

The proof uses the angular sector argument: arrows terminating at ±∞
fill angular sectors that sum to ≤ 2π, giving the inequality.
This requires global arrow trajectory analysis (see issue file
order_star_arrow_termination_topology.md). -/
theorem thm_355D (data : OrderArrowCountData)
    (h_approx : IsRationalApproxToExp data) :
    SatisfiesArrowCountInequality data := by
  sorry
```
where `IsRationalApproxToExp` is a new predicate connecting arrow count data to an actual approximation. Define it as:
```lean
/-- A rational function R of order p with deg(num)=n, deg(den)=d
has arrow counts consistent with the order star of R·exp(-z). -/
structure IsRationalApproxToExp (data : OrderArrowCountData) : Prop where
  order_eq : data.order = data.numeratorDegree + data.denominatorDegree
  -- Additional fields can be added later when topology is available
```
Wait — for Padé approximants, the order IS n + d, so `IsRationalApproxToExp` might be too general. Two options:
- **Option A (preferred)**: State 355D for general rational approximations (sorry), then specialize to Padé.
- **Option B**: State 355D directly for Padé (simpler, matches the squeeze argument).

Use **Option A** — it's more faithful to the textbook and `SatisfiesArrowCountInequality` already captures the general case.

**Step 3**: Prove Theorem 355E using the existing `pade_exact_arrow_counts_of_countInequality`:
```lean
/-- Theorem 355E: For Padé approximations, ñ = n and d̃ = d. -/
theorem thm_355E (data : OrderArrowCountData)
    (h_pade : IsPadeApproxToExp data)
    (h_355D : SatisfiesArrowCountInequality data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree :=
  pade_exact_arrow_counts_of_countInequality data h_pade.order_eq h_355D
```
This should be a one-liner or close to it, since the bookkeeping theorem already exists.

**Step 4**: State Theorem 355G (Ehle barrier). The textbook proof uses:
- 355E: all d up arrows terminate at poles
- 355F: A-stability means imaginary axis ⊂ order star boundary, so no up arrows cross iℝ
- Since d up arrows must reach d poles and cannot cross iℝ, the poles must all be in Re(z) < 0
- The denominator has degree d with all roots in left half-plane, and the order star boundary structure constrains the arrangement
- The detailed counting gives: n ≤ d ≤ n + 2

State with sorry:
```lean
/-- Theorem 355G (Ehle barrier): An A-stable Padé approximation R_{n,d}
to exp must satisfy n ≤ d ≤ n + 2. -/
theorem ehle_barrier (n d : ℕ)
    (h_aStable : ... A-stability condition ...)
    (h_pade : ... Padé condition ...) :
    n ≤ d ∧ d ≤ n + 2 := by
  sorry
```
The exact signature depends on what A-stability predicates are already in `OrderStars.lean`. Use the existing `IsAStableRational` or `aStable_imagAxis_not_orderStarPlus` infrastructure.

**Step 5**: Verify compilation:
```bash
LEAN_CC=gcc C_INCLUDE_PATH=/usr/include LIBRARY_PATH=/tmp/lean4-toolchain/lib PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH LAKE_NO_RESOLVE=1 lake env lean OpenMath/OrderStars.lean
```

**Step 6**: Submit the 355D sorry and any sub-lemmas to Aristotle (~3 jobs). Focus on:
- The `SatisfiesArrowCountInequality` implication from `IsRationalApproxToExp`
- Any angular-counting sub-lemmas you can decompose
- The 355G sorry

### What the proofs should look like when done

- **355D**: sorry (depends on global arrow trajectory topology — documented blocker)
- **355E**: fully proved (one-liner from `pade_exact_arrow_counts_of_countInequality` + 355D)
- **355G**: sorry (depends on 355E + A-stability pole-arrangement argument)

This is the **sorry-first architecture** mandated by CLAUDE.md. The sorrys are precisely documented as depending on topology not yet available in Mathlib.

## Priority 3 (if time remains): Update 355F Connection

The existing `aStable_imagAxis_not_orderStarPlus` theorem in `OrderStars.lean` proves one direction of the A-stability criterion. Check if it can be connected to the 355G statement to reduce the gap. Specifically:
- Does the existing A-stability predicate match what 355G needs?
- Can we state a lemma: "A-stable ⇒ no up arrow crosses iℝ ⇒ all poles in Re(z) < 0"?

If this connection is clean, add it. If it requires substantial new infrastructure, leave it for cycle 137.

## What NOT to Try

1. **Do NOT attempt to formalize continuous arrow trajectories or winding numbers.** This is the documented blocker in `order_star_arrow_termination_topology.md`. Accept sorry and document.
2. **Do NOT modify `OpenMath/Collocation.lean`** — it is done and fully proved.
3. **Do NOT attempt Theorem 355C** (arrow termination dichotomy) — it requires the very asymptotic/trajectory analysis that is blocked. Instead, let 355D absorb 355C's content as part of its sorry.
4. **Do NOT increase `maxHeartbeats`** — decompose proofs instead.
5. **Do NOT submit more than 5 Aristotle jobs** — batch them and check once after 30 min.
6. **Do NOT spend time on the Aristotle results from cycle 135** (7b0236f3, df09be51) — both have been assessed and contain nothing new to incorporate.
7. **Do NOT attempt to prove 355D without sorry** — the angular sector argument requires topology. State it, sorry it, document it, and move on to 355E (which IS provable) and 355G (which is the goal).

## Build Commands
```bash
LEAN_CC=gcc C_INCLUDE_PATH=/usr/include LIBRARY_PATH=/tmp/lean4-toolchain/lib PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH LAKE_NO_RESOLVE=1 lake env lean OpenMath/OrderStars.lean
```

## Exit Criteria
- **Full success**: Housekeeping complete + 355D stated with sorry + 355E proved as corollary + 355G stated with sorry + all compiles
- **Good progress**: Housekeeping complete + 355D stated with sorry + 355E proved as corollary + compiles
- **Minimum acceptable**: Housekeeping complete + at least one of {355D, 355E, 355G} stated in `OrderStars.lean` and compiling
