# Cycle 039 strategy

## TL;DR

**Primary target: `def:406A`** (local truncation error of an LMM,
Butcher §406, p. 345). Single-cycle deliverable: extend
`OpenMath/Chapter4/Section404.lean` with a `## §406 — Local
truncation error` section, define `LinearMultistepMethod.localTruncationError`
faithful to the textbook formula, and ship one or two non-vacuity
witnesses showing the LTE vanishes on solutions where it should.

**Do NOT pick `thm:243A`** this cycle. Reasons in §1 below.

**No Aristotle results** to incorporate this cycle.

---

## 1. Why `def:406A` and not `thm:243A`

Cycle 038's task-result note offered both as candidates and (correctly)
flagged that `thm:243A` likely needs more infrastructure. Here is the
explicit ruling:

- `thm:243A` is the equivalence
  `M.IsConvergent ↔ (M.IsStable ∧ M.IsConsistent)`.
  Stating it is trivial (we have all three predicates). **Proving it**
  decomposes into the textbook chain
  - (⇒) `thm:405A` (convergent ⇒ stable) + `thm:405B` (convergent ⇒
        preconsistent) + `thm:405C` (convergent ⇒ consistent), and
  - (⇐) `thm:406D` / `thm:422C` (stable + consistent ⇒ convergent — the
        hard direction, requiring discrete Grönwall on LMM iterates and
        the Picard–Lindelöf strengthening flagged in
        `picard_lindelof_bound_strengthening.md`).
  None of those four supporting theorems exists yet. Closing
  `thm:243A` properly is a 4–6 cycle project. CLAUDE.md and `plan.md`
  both forbid committing a `sorry`-stubbed theorem outside an active
  multi-cycle restructuring window — and we have not opened one. So
  the correct disposition for `thm:243A` is **leave deferred** until
  `thm:405A/B/C` and `thm:406D` are formalized, then close it as a
  one-line corollary.

- `def:406A` is a clean **definition** with concrete textbook formula.
  Its only dependencies (`def:404A`, `def:404B`) are formalized as of
  cycle 038. It is the natural unblocker for `lem:406B` (Convergence
  condition sufficiency bound) and ultimately for `thm:406D` — i.e.
  it is on the critical path back to `thm:243A` anyway.

So: **`def:406A` first**, then in subsequent cycles work through
`lem:406B → thm:406C → thm:405A → thm:405B → thm:405C → thm:406D`.
After `thm:406D` lands, `thm:243A` is a corollary.

## 2. Concrete tasks for `def:406A`

### 2a. Extend `OpenMath/Chapter4/Section404.lean`

Append a new section after the `§402 — Convergence` block (currently
ends at line 354 with `end OpenMath.Chapter4.Section404`). Insert the
new content **before** the `end` line — keep all new declarations
inside the existing namespace. The file already opens
`OpenMath.Chapter4.Section404` and has `LinearMultistepMethod`,
`IsConsistent`, etc. in scope.

### 2b. Read `extraction/formalization_data/entities/def_406A.json` first

Mandatory per CLAUDE.md. The textbook formula (Butcher §406, p. 345) is

```
L(y, x, h) = y(x) − Σ_{i=1}^{k} α_i · y(x − ih)
                  − h · Σ_{i=0}^{k} β_i · y'(x − ih).
```

**Sign-convention warning.** Butcher's textbook formula in this
passage uses the implicit coefficient `+1` on `y(x)` (he sums α from
i = 1, not i = 0). Our `LinearMultistepMethod` structure normalises
**`α 0 = -1`** (cycle 036 convention; preserved through cycles
037–038). Therefore the literal textbook expression
`y(x) − Σ_{i=1}^{k} α_i y(x − ih)` becomes, in our convention,
```
y(x) − Σ_{i=1}^{k} M.α i.succ · y(x − i·h)
   = −Σ_{i=0}^{k} M.α i · y(x − i·h)        -- because M.α 0 = -1
```
i.e. `L(y, x, h) = -[Σ_{i=0}^{k} M.α i · y(x − i·h) + h · Σ_{i=0}^{k} M.β i · y'(x − i·h)]`.

You have **two encoding choices**. Pick **option A** unless you find a
genuine obstacle:

- **Option A (recommended, textbook-faithful):** define `L` directly by
  the textbook formula, using `M.α i.succ` for the i = 1..k sum:
  ```lean
  def LinearMultistepMethod.localTruncationError {k : ℕ}
      (M : LinearMultistepMethod k) (y : ℝ → ℝ) (x h : ℝ) : ℝ :=
    y x
      - ∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
      - h * ∑ i : Fin (k + 1), M.β i * deriv y (x - (i.val : ℕ) * h)
  ```
  This matches Butcher one-to-one and avoids any sign-flip in the
  predicate name. The `α 0 = -1` normalisation is *not used* in this
  encoding; that is fine — the textbook formula simply does not refer
  to `α 0`.

- **Option B (uniform-index):** define `L` as
  `-[Σ_{i=0}^{k} M.α i · y(x − i·h) + h · Σ_{i=0}^{k} M.β i · y'(x − i·h)]`
  using `Fin (k+1)` sums and `M.α_zero` to recover Butcher's formula.
  Equivalent up to algebra but **less faithful** at the syntactic
  level. If you take this route, **prove the equivalence** as a
  separate lemma — this is the CLAUDE.md "equivalent formulation
  requires explicit equivalence lemma" rule.

### 2c. Use `deriv y` for `y'`

Mathlib's `deriv : (ℝ → ℝ) → ℝ → ℝ` returns `0` if `y` is not
differentiable at the point. That is the standard Mathlib spelling
and matches what every consumer in §406 onward will expect. Do
**not** introduce an `IsDifferentiableAt`-bundled variant — the
textbook signature `L(y, x, h)` is a value, not a theorem;
differentiability is the caller's concern, exactly like
`IsLMMSolution` does not require `f` continuous.

### 2d. Witnesses (non-vacuity, per CLAUDE.md)

Provide **at least two** sanity facts. Suggested:

1. **Constant solution kills the LTE under preconsistency.** Show
   `localTruncationError M (fun _ => c) x h = 0` provided
   `M.IsPreconsistent` and `c : ℝ`. The α-sum becomes
   `c · Σ M.α i.succ = c · 1 = c` (preconsistency); the β-sum is
   `0` because `deriv (fun _ => c) = 0` everywhere. So
   `L = c − c − 0 = 0`. **Tactic sketch:** `unfold`, then `simp` with
   `deriv_const`, `Finset.sum_const_zero`, `Finset.mul_sum` and
   `← M.IsPreconsistent`-flavoured rewrites. If `simp` doesn't close,
   finish with `ring` or `linarith`.

2. **Linear-in-x solution kills the LTE under consistency.** Show
   `localTruncationError M (fun t => a*t + b) x h = 0` provided
   `M.IsConsistent` and arbitrary `a, b, x, h`. Computation:
   `y(x − ih) = a·(x − ih) + b`, so
   - α-sum = `Σᵢ M.α i.succ · (a(x − (i+1)h) + b)
              = a·x · Σᵢ M.α i.succ
                − a·h · Σᵢ (i+1) · M.α i.succ
                + b · Σᵢ M.α i.succ`
              = `a·x · 1 − a·h · (Σᵢ (i+1) M.α i.succ) + b · 1`
                (preconsistency).
   - β-sum = `Σᵢ M.β i · a = a · Σᵢ M.β i`.
   - Plugging in:
     `L = (a*x + b) − [a·x − a·h·(Σ (i+1) α_{i+1}) + b] − h · a · (Σ β_i)`
     `= a·h · [(Σ (i+1) α_{i+1}) − Σ β_i]`
     `= 0` by `M.SatisfiesEq404b` (the (404b) consistency identity).

   This witness is the textbook content of "consistency means LTE is
   `O(h²)` for smooth solutions" (the linear case is the borderline
   `O(h²) = 0` instance) and is the cleanest non-vacuity demonstration.

   *If witness 2 turns out to require >40 lines of arithmetic*, retreat
   to just witness 1 and write a brief comment that the linear-in-x
   case is left for cycle 040 (along with a stub theorem name so the
   gap is visible). Witness 1 alone is sufficient for the CLAUDE.md
   non-vacuity rule.

3. **Optional bonus — explicit Euler unfolding sanity check.**
   `localTruncationError explicitEulerLMM y x h
      = y x − y (x − h) − h · deriv y x`. Sanity check by
   `simp [explicitEulerLMM, localTruncationError, ...]` then `ring`
   to verify the unfolding closes cleanly. (Not required — just a
   smoke test that confirms the encoding is right.)

### 2e. Aristotle batch

After writing the sorry-first skeleton (definition + `sorry`'d
witnesses), **submit the two witness theorems to Aristotle** as a
single batch, then continue with manual proofs in parallel. CLAUDE.md
is explicit: Aristotle is free compute, use it. Sleep 30 min, check
results once, take whichever (manual or Aristotle) finishes first.

If you don't reach the Aristotle step before manual proofs close,
that is also fine per the CLAUDE.md rule "if your manual proof
finishes first, keep it" — but **try** to submit (Aristotle warm-up
takes <1 minute and runs in the background while you work).

## 3. After `def:406A` ships

Update `extraction/formalization_data/lean_status.json`:
```
"def:406A": "formalized"  (was "unformalized")
```
And update `plan.md`:
- Change `[ ] def:406A` → `[x] def:406A` in the Chapter 4 table.
- Bump the progress counter at the top:
  `38 / 175` → `39 / 175`.

## 4. What NOT to try

- **Do NOT** state `thm:243A` with a `sorry`'d proof body. Leave it
  deferred. (Reasons in §1.) If you find the temptation strong, the
  meta-rule is: a `sorry` is acceptable only mid-restructuring; we are
  not in a restructuring cycle for §405–§406; opening one without a
  decomposition plan in `strategy.md` would itself be off-strategy.

- **Do NOT** raise `maxHeartbeats` above 200000 (CLAUDE.md hard rule).
  If a `simp` or `ring` step times out, decompose: extract the α-sum
  identity and the β-sum identity as separate lemmas first, then
  combine.

- **Do NOT** modify `OpenMath/Chapter4/Section404.lean` at any line
  earlier than the new `## §406` section header. Cycles 036–038
  committed those definitions and witnesses; touching them risks
  breaking the existing IsConsistent / IsStable / IsConvergent
  theorems and gains nothing.

- **Do NOT** modify `scripts/autonomous_loop.py` (worker / planner
  rule from cycle 015). Scanner false positives go in
  `.prover-state/issues/tautology_scanner_false_positives.md` for the
  loop maintainer.

- **Do NOT** introduce `axiom` or `constant` for the `deriv y`
  computation. Mathlib's `deriv_const`, `deriv_add`, `deriv_const_mul`,
  `deriv_id'`, `deriv_sub`, `deriv_neg` cover the smooth cases needed
  for witnesses 1 and 2. Use `lean_local_search "deriv_const"` to
  confirm the names before relying on them.

- **Do NOT** start work on `lem:406B`, `thm:405A/B/C`, `thm:406C/D`,
  or `thm:422C` this cycle. Each is its own cycle; take them in plan
  order in subsequent cycles.

- **Do NOT** use `h_<name>` for any new hypothesis names in the
  cycle's commits — it trips the tautology scanner. Use
  `hcons`, `hpre`, `heq`, etc. (no underscore after `h`). See
  `tautology_scanner_false_positives.md` for context.

- **Do NOT** chase the "previous cycle didn't commit" phantom. Cycle
  038 committed at `bc72bd0` (verified `git log -1 origin/Main/Experiments`).
  If the prompt's `attempts.md` rolls forward a stale "empty diff"
  warning, check `git log -1 origin/Main/Experiments --format='%H %s'`
  first — same diagnostic the cycle-009 / cycle-014 / cycle-015
  consultants prescribed.

## 5. Workflow checklist (concrete)

1. `Read extraction/formalization_data/entities/def_406A.json` — quote
   the statement in your commit message body and in the Lean docstring.
2. Sketch the four-line `LinearMultistepMethod.localTruncationError`
   definition (Option A from §2b).
3. Write the two witness theorems with `sorry` bodies. Run
   `lake env lean OpenMath/Chapter4/Section404.lean` to verify the
   skeleton compiles.
4. Submit witness theorems to Aristotle as a batch (~5 sub-jobs is
   fine; even 2 is fine — single batch).
5. Close witness 1 (constant solution) by hand. Aim for ≤15 lines:
   ```
   unfold ... ; simp [deriv_const, Finset.sum_const_zero,
                       ← Finset.mul_sum, M.IsPreconsistent ...];
   ring
   ```
   or similar. If `simp` does not close, manually rewrite using
   `Finset.mul_sum`, then close with `linarith` or `ring`.
6. Close witness 2 (linear solution) by hand. Aim for ≤40 lines.
   Decompose into `α_sum_linear` and `β_sum_linear` helper lemmas if
   the inline proof bloats. The key identity at the end is
   `M.SatisfiesEq404b` rewriting `Σᵢ (i+1) M.α i.succ = Σᵢ M.β i`.
7. After Aristotle returns (or after your 30-min check, whichever
   first): if Aristotle has a cleaner proof, swap in. If not, keep
   yours.
8. Run `lake env lean OpenMath/Chapter4/Section404.lean` again to
   verify the cycle's deliverable is sorry-free.
9. Run `#print axioms OpenMath.Chapter4.Section404.localTruncationError` —
   should show `[propext, Classical.choice, Quot.sound]` only (or
   `[]` for the definition itself; the witness theorems should show
   the standard three).
10. Update `lean_status.json` and `plan.md` per §3.
11. Pre-commit faithfulness check (CLAUDE.md). For the new `def`:
    - Quote `def_406A.json`'s `statement_text` / `statement_latex`.
    - Confirm Lean type matches (Option A is direct match; Option B
      requires the equivalence lemma).
    - Definition-smuggling check: ✓ defined as the textbook formula,
      not as "L = O(h²)" (the order property is a *consequence* under
      consistency, not the definition).
12. `git status` to verify only `OpenMath/Chapter4/Section404.lean`,
    `extraction/formalization_data/lean_status.json`, `plan.md`,
    `.prover-state/task_results/cycle_039.md`, and any new issue file
    (if you wrote one) are modified outside `.prover-state/`'s
    machine-managed files.
13. Commit and push. Verify the commit reaches `origin/Main/Experiments`
    by running `git log -1 origin/Main/Experiments --format='%H %s'` —
    this is the cycle-009 consultant's diagnostic against the recurrent
    "empty diff" phantom.
14. Write `.prover-state/task_results/cycle_039.md` per the CLAUDE.md
    template. Include the faithfulness-check section.

## 6. Stretch goal (only if §5 finishes early)

If `def:406A` ships fast and you have spare cycle time, the
**lowest-risk follow-on** is to also formalize `def:451A` (G-stable,
§451) — another single-definition deliverable in Chapter 4, listed in
`plan.md`. It depends on Chapter 1's Section 110 / inner-product
infrastructure already used by `thm:112B`. One witness (e.g. the
trivial `G = 1` scalar or `G = I` identity matrix on a 1-step method)
demonstrates non-vacuity.

But: **only attempt the stretch goal if the primary target is
complete and committed**. Do not ship a half-finished `def:451A`
alongside a finished `def:406A`. Two separate commits if both land.

## 7. Open issues (for awareness; not actionable this cycle)

- `lmm_convergence_witness_deferred.md` — gates a concrete
  `IsConvergent` witness on `thm:422C` infrastructure.
- `picard_lindelof_bound_strengthening.md` — gates `thm:406D` (and
  hence `thm:243A`'s ⇐ direction).
- `tautology_scanner_false_positives.md` — loop-maintainer issue;
  do not edit `scripts/autonomous_loop.py` from the worker.
- `AN_stability_deferred.md`, `equivalent_self_general_deferred.md`,
  `jordan_canonical_form_missing.md`, `reduced_method_deferred.md`,
  `symmetry_group_equivalence.md` — Chapter 1 / 3 deferrals; not
  in scope for cycle 039.

These all stay open after cycle 039.
