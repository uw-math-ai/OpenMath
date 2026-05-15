# Cycle 291 Strategy

## TL;DR

Ship **Phase A.2 starter lemmas** for the cycle 289 manual closure
plan of `lem:342A` (342f): the two **easy** orthogonality components
F.1 and F.2 identified in cycle 290's task-results "Suggested next
approach". Both follow directly from cycle 277's
`butcherShiftedLegendre_orthogonal` plus scalar/constant pull-out
through `intervalIntegral.integral_const_mul`.

**Do NOT attempt the hard cross-term** `⟨(2n - 1) · (2X - 1) · P_{n-1},
P_k⟩ = 0` this cycle — it requires the `2X - 1 = P_1^*` substitution
plus a basis-expansion argument. Defer to cycle 292.

**Do NOT poll/resubmit Aristotle** — cycle 289 closed the door on
search-based closure of (342f) after the third 20% stall on
`efe4940e`. The manual closure path (Phase A.1 → A.2 → A.3 → final
combination) is on track; stay disciplined.

## Context

Cycle 290 successfully shipped **Phase A.1 (b)** —
`recurrence_residual_natDegree_lt` — axiom-clean in ~140 LOC. The
phase plan in `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
§5 now has these checkpoints:

- ✅ Phase A.1 (a): `n_mul_choose_two_n_n_eq` (cycle 289).
- ✅ Phase A.1 (b): `recurrence_residual_natDegree_lt` (cycle 290).
- ⏳ Phase A.2: orthogonality `⟨Q, P_k^*⟩ = 0` for `k ≤ n - 2`.
- ⏳ Phase A.3: basis-span conclusion `Q = 0`.
- ⏳ Final: close (342f) general + `lean_status.json` bump.

Phase A.2 has three components per the issue file §5:
1. **(F.1)** `⟨(n : ℝ) • P_n, P_k⟩ = 0` for `k < n` — direct from (342a).
2. **(F.2)** `⟨C((n - 1):ℝ) · P_{n-2}, P_k⟩ = 0` for `k ≤ n - 3` — direct from (342a) since `k ≠ n - 2`.
3. **(F.3)** `⟨(2n - 1) · (2X - 1) · P_{n-1}, P_k⟩ = 0` for `k ≤ n - 3` — harder; requires `2X - 1 = P_1^*` (cycle 273's `butcherShiftedLegendre_one`) + basis expansion.

Cycle 291 targets **F.1 and F.2 only**. F.3 deferred to cycle 292.

## What to do this cycle

### Step 0 (preflight, 5 min) — verify `butcherShiftedLegendre_orthogonal` signature

Before writing any code, confirm the exact signature of cycle 277's
orthogonality theorem. Use `Grep` on `OpenMath/Chapter3/Section342.lean`
for `butcherShiftedLegendre_orthogonal` and read the declaration. Key
things to confirm:

- Argument order: is it `(hmn : m ≠ n)` or `(hmn : n ≠ m)`?
- Integrand order: is it `P_m.eval x * P_n.eval x` or vice versa?
- Integration variable: is it `(0:ℝ)..1` or `0..(1:ℝ)`?

Adjust the recipes below to match. The arguments matter for the
final `rw` step.

### Priority 1 (P1, must ship) — `recurrence_residual_orthogonal_first_term`

Location: `OpenMath/Chapter3/Section342.lean`, immediately after
`recurrence_residual_natDegree_lt` (around line ~2800).

Target signature (adjust integrand order to match Step 0's findings):

```lean
/-- **Phase A.2 (F.1) — orthogonality of `(n : ℝ) • P_n^*` against
`P_k^*` for `k < n`.** Direct from cycle 277's
`butcherShiftedLegendre_orthogonal` via scalar pull-out. The first
summand of the cycle 290 recurrence residual is orthogonal to
`P_k^*` for every `k < n`. -/
theorem recurrence_residual_orthogonal_first_term (n : ℕ) (hn : 1 ≤ n)
    {k : ℕ} (hk : k < n) :
    ∫ x in (0:ℝ)..1, ((n : ℝ) • butcherShiftedLegendre n).eval x *
                       (butcherShiftedLegendre k).eval x = 0 := by
  sorry  -- close manually; do NOT submit to Aristotle
```

**Expected LOC: ~15.** Tactic recipe:

```lean
  simp only [Polynomial.eval_smul, smul_eq_mul]
  -- Goal: ∫ x in (0:ℝ)..1, (n : ℝ) * (P_n.eval x) * (P_k.eval x) = 0
  rw [show (fun x : ℝ => (n : ℝ) * (butcherShiftedLegendre n).eval x *
         (butcherShiftedLegendre k).eval x) =
       (fun x : ℝ => (n : ℝ) * ((butcherShiftedLegendre n).eval x *
         (butcherShiftedLegendre k).eval x)) from by funext x; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [butcherShiftedLegendre_orthogonal hk.ne']
  ring
```

**Notes**:
- `hk.ne'` gives `n ≠ k` from `hk : k < n`. If
  `butcherShiftedLegendre_orthogonal`'s argument order is reversed
  (`(hmn : m ≠ n)` with integrand `P_m * P_n`), pass `hk.ne'` as is
  or `hk.ne` (which gives `k ≠ n`).
- `intervalIntegral.integral_const_mul` pulls a constant out:
  `∫ x, c * f x = c * ∫ x, f x`. Verify the exact name; alternatives:
  `intervalIntegral.integral_const_mul'`, `MeasureTheory.integral_const_mul`.
- If the `show ... from by funext` rewrite is awkward, try
  `simp_rw [mul_assoc]` first to associate the multiplication.

### Priority 2 (P2, must ship) — `recurrence_residual_orthogonal_third_term`

Location: immediately after P1.

Target signature:

```lean
/-- **Phase A.2 (F.2) — orthogonality of `C((n - 1):ℝ) · P_{n-2}^*`
against `P_k^*` for `k ≤ n - 3`.** Direct from cycle 277's
`butcherShiftedLegendre_orthogonal` since `k ≤ n - 3 < n - 2`, so
`n - 2 ≠ k`. Constant pull-out via `Polynomial.eval_mul`,
`Polynomial.eval_C`, and `intervalIntegral.integral_const_mul`. The
third summand of the cycle 290 recurrence residual is orthogonal to
`P_k^*` for every `k ≤ n - 3`. -/
theorem recurrence_residual_orthogonal_third_term (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0:ℝ)..1, (Polynomial.C ((n - 1 : ℕ) : ℝ) *
                       butcherShiftedLegendre (n - 2)).eval x *
                       (butcherShiftedLegendre k).eval x = 0 := by
  sorry
```

**Expected LOC: ~20.** Tactic recipe:

```lean
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  -- Goal: ∫ x in (0:ℝ)..1, ((n-1 : ℕ) : ℝ) * P_{n-2}.eval x * P_k.eval x = 0
  rw [show (fun x : ℝ => ((n - 1 : ℕ) : ℝ) *
         (butcherShiftedLegendre (n - 2)).eval x *
         (butcherShiftedLegendre k).eval x) =
       (fun x : ℝ => ((n - 1 : ℕ) : ℝ) *
         ((butcherShiftedLegendre (n - 2)).eval x *
         (butcherShiftedLegendre k).eval x)) from by funext x; ring]
  rw [intervalIntegral.integral_const_mul]
  have h_ne : n - 2 ≠ k := by omega
  rw [butcherShiftedLegendre_orthogonal h_ne]
  ring
```

**Critical**: the hypothesis pair `(hn : 3 ≤ n)` + `(hk : k ≤ n - 3)`
forces `k ≤ n - 3 < n - 2` since `n - 2 = (n - 3) + 1 > n - 3 ≥ k`.
`omega` should close `n - 2 ≠ k` directly given these.

If `butcherShiftedLegendre_orthogonal`'s argument order is
`(hmn : k ≠ n - 2)`, swap to `h_ne.symm` or restate as
`have h_ne : k ≠ n - 2 := by omega`.

### Priority 3 (P3, optional stretch — only if P1+P2 close cleanly with ≥30 min cycle budget remaining)

Combined Phase A.2 partial statement establishing orthogonality of the
first + third summands together, using `intervalIntegral.integral_add`:

```lean
/-- **Partial Phase A.2** — combined orthogonality of the first and
third summands of the cycle 290 recurrence residual against `P_k^*`
for `k ≤ n - 3`. The second summand (cross-term involving
`(2X - 1) · P_{n-1}`) is deferred to a separate cycle. -/
theorem recurrence_residual_orthogonal_easy (n : ℕ) (hn : 3 ≤ n)
    {k : ℕ} (hk : k ≤ n - 3) :
    ∫ x in (0:ℝ)..1, (((n : ℝ) • butcherShiftedLegendre n +
                       Polynomial.C ((n - 1 : ℕ) : ℝ) *
                       butcherShiftedLegendre (n - 2)).eval x) *
                       (butcherShiftedLegendre k).eval x = 0 := by
  sorry
```

**Expected LOC: ~15.** Recipe: `Polynomial.eval_add` + distribute over
multiplication via `add_mul` + `intervalIntegral.integral_add` (needs
integrability witnesses — `Continuous.intervalIntegrable` of a
polynomial × polynomial product is automatic via
`Polynomial.continuous.mul`) + apply P1 and P2. Skip if either P1 or
P2 stalls.

Note: P3 needs `hk_strong : k < n` to invoke P1; this follows from
`hn : 3 ≤ n` and `hk : k ≤ n - 3` via `omega` (`k ≤ n - 3 < n`).

### Priority 4 (P4, housekeeping — must do alongside P1/P2)

Update `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
with a "Cycle 291 update" subsection (mirror the cycle 289 / cycle 290
update style at the end of the file):

- Phase A.2 starter lemmas F.1 + F.2 shipped axiom-clean.
- F.3 (cross-term) remains open; cycle 292+ target.
- Phase A.3 (basis-span conclusion) remains open; cycle 293+ target.
- LOC ladder so far: cycle 289 ~80 LOC; cycle 290 ~140 LOC;
  cycle 291 ~35–50 LOC.

Do NOT update `lean_status.json` row for `lem:342A` — still `partial`,
no entity-status change.

Do NOT update `plan.md` row for `lem:342A` — already `[~]`. Append a
brief cycle 291 note to the existing run of cycle-specific notes
inline with the partial-status entry (mirror cycle 290's note shape).

## What NOT to try

These are explicitly out of scope; do not freelance them:

1. **DO NOT submit (342f) to Aristotle.** Cycle 289 closed this door
   after three consecutive 20% stalls on project `efe4940e` over
   ~35 minutes (cycle 287 obs #1, 288 obs #2, 289 obs #3). Manual
   closure per `lem_342A_342f_manual_closure_plan.md` only.

2. **DO NOT attempt the F.3 cross-term** `⟨(2n - 1) · (2X - 1) · P_{n-1},
   P_k⟩ = 0`. Per the issue file §5 and cycle 290 task results
   §"Suggested next approach", this requires:
   - Substituting `2X - 1` in terms of `P_1^*` (using cycle 273's
     `butcherShiftedLegendre_one`).
   - Expanding `P_1 · P_{n-1}` in the `{P_j^*}_{j=0..n}` basis.
   - Fourier-coefficient symmetry argument:
     `⟨P_1 P_{n-1}, P_j⟩ = ⟨P_{n-1}, P_1 P_j⟩` and `P_1 P_j` has
     `natDegree = j + 1 ≤ n - 2`, so the inner product is zero by
     orthogonality basis of `P_{n-1}` against `Polynomial.degreeLT ℝ (n - 1)`.
   - This is ~100–150 LOC of dedicated work; **not a cycle 291 deliverable**.

3. **DO NOT pursue parity-strengthened bounds.** The textbook uses
   parity (342c) to tighten `natDegree Q < n` to `natDegree Q < n - 1`,
   which would let Phase A.2 only need `k ≤ n - 3` instead of `k ≤ n - 2`.
   This optimization is irrelevant for cycle 291's deliverables and
   should be addressed (or skipped) in the Phase A.3 capstone.

4. **DO NOT modify `butcherShiftedLegendre_orthogonal`** (cycle 277).
   The cycle 277 deliverable is the load-bearing primitive for Phase
   A.2. If the argument order `m ≠ n` is awkward, use `Ne.symm`,
   `.ne'`, or `.ne` at the call site rather than rewriting the theorem.

5. **DO NOT raise `maxHeartbeats` above 200000.** If a `simp` chain
   stalls, decompose into smaller named lemmas. Cycle 290's approach
   of using `set` aliases + `rw [hL_def]` for unfolding is the
   canonical pattern.

6. **DO NOT introduce `sorry`/`axiom`/`constant`.** Cycle 290's
   deliverable bar applies: ship axiom-clean or skip the cycle.

7. **DO NOT attempt `Section441.lean` compilation.** 43+ consecutive
   GPFS timeouts since cycle 182. Per
   `.prover-state/issues/cycle_182_gpfs_slowness.md`, skip any §441
   compilation; only `Section441B.lean` (cycle 237 new file) is
   healthy on this cluster.

8. **DO NOT extend the n-ladder past n=11.** Cycle 288 already shipped
   n=11; further empirical witnesses provide marginal value. The
   focus is the general-case manual closure, not more concrete cases.

## Verification checklist before commit

After P1 and P2 land:

```bash
# 1. Single-file compile
lake env lean OpenMath/Chapter3/Section342.lean    # expect exit 0

# 2. Aggregator
lake env lean OpenMath/Chapter3.lean               # expect exit 0

# 3. Sorry count
grep -c sorry OpenMath/Chapter3/Section342.lean    # expect 0

# 4. Axiom-clean on both new theorems (via lean_verify MCP if available,
#    or via #print axioms inside the file as a temporary check that
#    is removed before commit)
```

Use the `mcp__lean-lsp__lean_verify` MCP tool to confirm each new
theorem's axiom dependency is exactly `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`).

## Suggested next-cycle planner action (cycle 292)

Phase A.2 (F.3) cross-term `⟨(2n - 1) · (2X - 1) · P_{n-1}, P_k⟩ = 0`
for `k ≤ n - 3`. Concrete tasks:

1. Establish a helper bridging `C 2 * X - C 1 = butcherShiftedLegendre 1`
   from cycle 273's `butcherShiftedLegendre_one` (should be a `rfl` or
   one-line `simp` once the alias direction is matched).

2. Show `⟨P_1 · P_{n-1}, P_k⟩ = 0` for `k ≤ n - 3` via the symmetry
   `⟨P_1 P_{n-1}, P_k⟩ = ⟨P_{n-1}, P_1 P_k⟩` (commutativity of
   multiplication inside the integrand) plus
   `(P_1 * P_k).natDegree ≤ k + 1 ≤ n - 2 < n - 1`.

3. The orthogonality of `P_{n-1}` against any polynomial of
   `natDegree < n - 1` requires a span argument: any polynomial of
   degree `< n - 1` lies in `Polynomial.degreeLT ℝ (n - 1)`, which is
   spanned by `{P_0^*, ..., P_{n-2}^*}`. This is the **basis-span
   lemma** that is also required by Phase A.3, so cycle 292 should
   ship it as a reusable helper.

LOC budget: ~100–150 LOC for F.3 + the basis-span helper.

Phase A.3 (basis-span conclusion `Q = 0`) and the final (342f)
closure remain for cycles 293+ per the issue file §5.
