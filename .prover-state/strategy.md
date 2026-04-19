# Strategy — Cycle 124

## Situation
- **1 sorry** in the entire project: `h_A_term` inside `reflect_satisfiesE` at `OpenMath/ReflectedMethods.lean:391`.
- Aristotle project `9cc99ed3` COMPLETED with a full ℚ-based proof (extracted to `.prover-state/aristotle_results/9cc99ed3-e6ac-4582-8edb-fe07c5a30a01/`).
- Five focused Aristotle jobs submitted at end of cycle 123 (a63c1035, b62cceee, 5870e46f, fd3966f1, 083e58a2) — status unknown.

## Priority 1: Close `h_A_term` — the LAST sorry in the project

### Step 0: Check the five new Aristotle jobs

Check status of jobs a63c1035, b62cceee, 5870e46f, fd3966f1, 083e58a2 using `mcp__aristotle__get_status`. If any completed, extract and incorporate. These target `h_A_term` directly over ℝ in the actual repo file — if any succeeded, they should be drop-in.

Sleep 30 minutes ONLY if all five are still IN_PROGRESS AND below 50% progress. If they are QUEUED or clearly not going to complete soon, skip waiting and go to Step 1.

### Step 1: Port the Aristotle ℚ proof to ℝ

The completed Aristotle proof at `.prover-state/aristotle_results/9cc99ed3-e6ac-4582-8edb-fe07c5a30a01/05_reflect_satisfiesE_aristotle/ReflectSatisfiesE.lean` contains three key helper lemmas that close the proof. Port them to ℝ in `OpenMath/ReflectedMethods.lean` as private helpers.

#### Helper 1: `gen_alt_binom_sum` (the generalized identity)

```
∑_{m=0}^n C(n,m)(-1)^m / (m+a) = n! * (a-1)! / (n+a)!    for a ≥ 1
```

The Aristotle proof uses induction on n. Port to ℝ:

```lean
private lemma gen_alt_binom_sum (n a : ℕ) (ha : 0 < a) :
    ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℝ) * (-1) ^ m / ((m : ℝ) + (a : ℝ)) =
      ↑(n.factorial) * ↑((a - 1).factorial) / ↑((n + a).factorial) := by
```

**Base case** (n = 0): the sum is `1/a`, and the RHS is `1 * (a-1)! / a! = 1/a`. Use `cases a` + `norm_num` + `field_simp`.

**Inductive step**: Split using Pascal's rule. The Aristotle proof's inductive step uses `simp_all +decide` and `grind`. Replace `grind` with `field_simp; ring` or explicit factorial algebra. The key recursion is:
```
f(n+1, a) = f(n, a) + f(n, a+1) * (-1) * ...
```
Actually the Aristotle proof line 40-47 is complex. A cleaner approach over ℝ: prove by induction on n, using the identity:
```
C(n+1,m) = C(n,m) + C(n,m-1)
```
and splitting the sum at the Pascal boundary.

**If `gen_alt_binom_sum` is too hard to port in 30 minutes**: skip it and try the direct approach in Step 2.

#### Helper 2: `double_binom_sum` (the double identity)

```
∑_{α<r} ∑_{β<q} C(r-1,α)(-1)^α C(q-1,β)(-1)^β / ((β+1)(α+β+2))
  = 1/(r*(q+r))
```

The Aristotle proof first evaluates the inner sum over α using `gen_alt_binom_sum`, then simplifies the remaining single sum.

#### Helper 3: `cross_term_expand` (connecting h_A_term to the double sum)

This expands both `(1-c)` powers, swaps sums, and applies `hE`:
```lean
∑ i j, b_i (1-c_i)^{k-1} A_{ij} (1-c_j)^{l-1}
  = ∑_α ∑_β C(k-1,α)(-1)^α C(l-1,β)(-1)^β / ((β+1)(α+β+2))
```

This mirrors the existing `reflect_satisfiesC` proof pattern already in the file.

#### Assembly

With all three helpers:
```lean
have h_A_term := (cross_term_expand t hE l hl hlζ k hk hκη).trans
  (double_binom_sum l k hl hk)
-- double_binom_sum gives 1/(k*(l+k))
-- convert to 1/(k*l) - 1/(l*(k+l)) by algebra
```

### Step 2: Alternative approach if porting stalls

If `gen_alt_binom_sum` is too messy over ℝ, try proving `double_binom_sum` directly by **double induction on k and l**, using `alternating_binom_div_succ` (already proved in the file) as the base case tool.

**Base case l=1**: Inner sum has only b=0 term. Reduces to:
```
∑_{a=0}^{k-1} C(k-1,a)(-1)^a / ((1)(a+2)) = 1/(k*(1+k))
```
Partial fraction: `1/(a+2) = 1 - 1/(a+1) + ...`. Actually simpler: use `gen_alt_binom_sum` at `a=2`:
```
∑ C(k-1,a)(-1)^a/(a+2) = (k-1)! * 1! / (k+1)! = 1/(k(k+1))
```
Or without `gen_alt_binom_sum`: partial fraction `1/((a+1)(a+2)) = 1/(a+1) - 1/(a+2)`, then two applications of `alternating_binom_div_succ` at different shifts.

Wait — the base l=1 sum is `∑_a C(k-1,a)(-1)^a / (1*(a+2))` = `∑_a C(k-1,a)(-1)^a/(a+2)`. This is NOT `alternating_binom_div_succ` (which has `1/(a+1)`). So we need either `gen_alt_binom_sum` at `a=2`, or a telescoping argument.

**Telescoping for the base case**: Write `1/(a+2) = 1/(a+1) - 1/((a+1)(a+2))` — no, that's wrong. Instead use:
```
1/(a+2) = (1/(a+1)) * (a+1)/(a+2)
```
This doesn't help either. The clean path is `gen_alt_binom_sum`.

### Step 3: The nuclear option — prove `gen_alt_binom_sum` via the Beta function integral

Over ℝ, the identity `∑ C(n,m)(-1)^m/(m+a) = B(n+1, a) = n!(a-1)!/(n+a)!` follows from the integral `∫₀¹ t^{a-1}(1-t)^n dt`. Mathlib has `intervalIntegral.integral_pow_mul_one_sub_pow` or similar Beta function infrastructure.

The Aristotle proof actually uses this approach for `alternating_binom_sum` (lines 21-26) — it computes `∫₀¹ (1-x)^n dx`. The generalization uses `∫₀¹ x^{a-1}(1-x)^n dx = B(a, n+1)`.

**Look for Mathlib's Beta function**: search for `betaIntegral`, `integral_pow_mul_one_sub_pow`, `Euler.betaIntegral`. If available, the proof is:
1. `∫₀¹ x^{a-1}(1-x)^n dx = B(a, n+1) = Γ(a)Γ(n+1)/(Γ(n+a+1)) = (a-1)!n!/(n+a)!`
2. Expand `(1-x)^n = ∑ C(n,m)(-1)^m x^m`
3. Integrate termwise: `∑ C(n,m)(-1)^m ∫₀¹ x^{m+a-1} dx = ∑ C(n,m)(-1)^m/(m+a)`
4. Equate.

### What NOT to try

1. **Do NOT try `ring`/`field_simp`/`norm_num` on the double sum** — it has symbolic parameters k, l.
2. **Do NOT try `grind`** — it exists in Lean 4 but may not close factorial identities over ℝ.
3. **Do NOT try to prove the double sum by direct algebraic manipulation** without helper lemmas — cycles 123 showed this doesn't work.
4. **Do NOT abandon the E proof for other theorems** — this is the last sorry in the entire project.
5. **Do NOT re-derive B/C/D proofs** — they are already done.
6. **Do NOT use `maxHeartbeats` increases** — decompose instead.
7. **Do NOT use integral representations unless Mathlib has explicit Beta integral infrastructure** — check first with `lean_loogle` or `lean_leansearch`.

### Recommended execution order

1. Check 5 Aristotle jobs (5 min)
2. If any completed with working proof → incorporate and done
3. Otherwise: search Mathlib for Beta integral / `betaIntegral` (5 min)
4. If Beta integral exists → prove `gen_alt_binom_sum` via integral (20 min)
5. Prove `double_binom_sum` using `gen_alt_binom_sum` (15 min)
6. Prove `cross_term_expand` (wire up the expansion + hE application) (15 min)
7. Close `h_A_term` by combining (5 min)
8. Verify compilation (5 min)
9. Write task result, commit (5 min)

Total: ~75 min. If step 4 stalls at 30 min, submit the `gen_alt_binom_sum` lemma to Aristotle and work on `cross_term_expand` while waiting.

## Verification

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ReflectedMethods.lean
```

## Commit message (if sorry closed)

```
cycle 124: close reflect_satisfiesE — 0 sorry project-wide
```

## Priority 2: If E is closed, pick next target

If the project reaches 0 sorry, the plan.md next targets are:
1. **Order star / Ehle barrier** (Theorem 355A+) — assess `OpenMath/OrderStars.lean`
2. **Rooted tree infrastructure** (Theorem 301A) — upgrade child representation
3. **Theorem 342C remaining implications** (342j, 342k, 342l) — need rooted tree infrastructure

Pick whichever is most tractable. The order star theory is the plan.md top priority.

## End-of-Cycle Checklist

- [ ] All modified `.lean` files compile
- [ ] Write `.prover-state/task_results/cycle_124.md`
- [ ] Update `.prover-state/cycle` to `124`
- [ ] Update `.prover-state/history.jsonl` with cycle summary
- [ ] Commit and push all changes
