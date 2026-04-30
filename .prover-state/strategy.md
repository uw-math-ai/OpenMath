# Cycle 040 Strategy

## Status going in

- Cycle 039 landed `def:406A` (`localTruncationError`) cleanly at the
  current branch tip, with two non-vacuity witnesses
  (`localTruncationError_const`, `localTruncationError_linear`). All
  Chapter 4 §404/§406 *definitions* are now in place. No `sorry` on
  the branch.
- No pending Aristotle results to incorporate.
- The natural next link in the Chapter 4 chain is **`lem:406B`** —
  "Convergence condition sufficiency bound". Its single dependent is
  `thm:406C` (global error bound), which is in turn a key prerequisite
  for `thm:405A/B/C` and `thm:406D` (and thus for `thm:243A` once Ch.4
  is done). So `lem:406B` is the right target.

## Primary target — `lem:406B`

**Entity file**: `extraction/formalization_data/entities/lem_406B.json`
(read this verbatim before writing any Lean).

**Textbook statement** (from the JSON):
> If `y` is the exact solution to the standard initial value problem
> and `x ∈ [x₀ + kh, x̄]`, then
>   `|L(y, x, h)| ≤ (½ Σ_{i=1}^k i² |αᵢ| + Σ_{i=1}^k i |iαᵢ − βᵢ|) · L · M · h²`.

`L` here is the Lipschitz constant of `f`, `M` is the bound on
`‖f(y(·))‖` over the interval, and `L(y, x, h)` is the local
truncation error from `def:406A`.

**Note on the textbook bound** ⚠️: the textbook proof claims the
algebraic decomposition

  `L(y,x,h) = Σ αᵢ (y(x) − y(x−ih) − ih y'(x)) + h Σ (iαᵢ − βᵢ)(y'(x) − y'(x−ih))`.

Re-deriving this from preconsistency (`Σαᵢ = 1`) and (404b)
(`Σ iαᵢ = Σ_{i=0}^k βᵢ`) by direct algebra appears to give the **simpler**

  `L(y,x,h) = Σ αᵢ (y(x) − y(x−ih) − ih y'(x)) + h Σ βᵢ (y'(x) − y'(x−ih))`,

which would change the bound's second sum from `Σ i|iαᵢ − βᵢ|` to
`Σ i|βᵢ|`. **DO NOT trust this planner derivation**: re-derive the
decomposition yourself by direct expansion early in the cycle,
*before* writing the bound's RHS. If your derivation matches Butcher,
use Butcher's form. If it disagrees with Butcher, file a dated issue
at `.prover-state/issues/lem_406B_textbook_check.md` documenting the
two candidate forms with full algebraic justification (both forms
are valid upper bounds; the question is which is the one Butcher
intended). Then ship whichever is mathematically sound — do not
silently encode one.

### Required hypotheses (signature design, do not skip)

The textbook's "exact solution" / `M`-bound / Lipschitz-`L` triple is
not a single Mathlib predicate. You will need to introduce them
explicitly. Recommended Lean signature shape (scalar `ℝ → ℝ`, matching
`def:406A`):

```lean
theorem localTruncationError_bound
    {k : ℕ} (M_method : LinearMultistepMethod k)
    (hcons : M_method.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M_method.localTruncationError y x h|
      ≤ ((1/2) * ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M_method.α i.succ|
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)
              * |M_method.β i.succ| /- or |i.val+1 * α i.succ - β i.succ| -/)
        * L * M_bound * h^2 := by
  sorry
```

The "scalar `ℝ → ℝ`" choice is forced by `def:406A` (which uses
`y : ℝ → ℝ` and `deriv y`). Generalising to `ℝ^N` would be a separate
infrastructure cycle and is out of scope here. Do *not* drop
`hf_lip`, `hf_y_bound`, or `hy_ode`: the proof crucially needs all
three.

### Sorry-first decomposition (MANDATORY per CLAUDE.md)

State the theorem above with the full RHS, then decompose into the
sub-lemmas below. **Compile after each sub-lemma is stated, before
attempting any proofs.** Then prove what's tractable; submit the rest
to Aristotle.

1. **Sub-lemma A — norm bound on `y(x+hξ) − y(x)`** (textbook eq.
   (406b)):
   ```lean
   lemma exact_solution_norm_bound
       (hy_diff …) (hy_ode …) (hf_y_bound …) (x h : ℝ) (hh : 0 ≤ h)
       (ξ : ℝ) (hξ : ξ ≤ 0) :
       |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := sorry
   ```
   Proof sketch: `y(x+hξ) − y(x) = ∫_{x}^{x+hξ} y'(t) dt =
   ∫_{x}^{x+hξ} f(y(t)) dt`, then `|·| ≤ |hξ| · M_bound`. Mathlib:
   `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
   `intervalIntegral.norm_integral_le_of_norm_le_const`.

2. **Sub-lemma B — FTC identity for the residual `T_i`**:
   ```lean
   lemma residual_integral_form
       … (i : ℕ) (hi : 1 ≤ i) :
       y x - y (x - i*h) - (i*h) * deriv y x
         = h * ∫ ξ in (-(i : ℝ))..0, (f (y (x + h*ξ)) - f (y x)) := sorry
   ```
   Proof sketch: by FTC + change of variables `t = x + hξ`.

3. **Sub-lemma C — bound on the residual `‖T_i‖ ≤ ½ i² h² LM`**:
   Combine A + B + Lipschitz: `|T_i| ≤ h · L · ∫_{-i}^0 |y(x+hξ) −
   y(x)| dξ ≤ hL · ∫_{-i}^0 h(−ξ) M dξ = hL · h M · i²/2`.

4. **Sub-lemma D — Lipschitz bound on `f(y(x)) − f(y(x−ih))`**:
   ```lean
   lemma deriv_diff_bound
       … (i : ℕ) :
       |deriv y x - deriv y (x - i*h)| ≤ (i : ℝ) * h * L * M_bound := sorry
   ```
   This is `|f(y(x)) − f(y(x−ih))| ≤ L · |y(x) − y(x−ih)|`, then
   sub-lemma A with `ξ = −i`.

5. **Sub-lemma E — algebraic decomposition** (the load-bearing
   identity; **verify direction first per the warning above**):
   ```lean
   lemma localTruncationError_decomposition
       (hcons : M.IsConsistent) (y …) (x h : ℝ) :
       M.localTruncationError y x h
         = ∑ i : Fin k, M.α i.succ
              * (y x - y (x - ((i.val+1):ℝ)*h)
                 - ((i.val+1):ℝ)*h * deriv y x)
           + h * ∑ i : Fin k, /- coefficient: M.β i.succ OR
                                ((i.val+1):ℝ)*M.α i.succ - M.β i.succ -/
                  * (deriv y x - deriv y (x - ((i.val+1):ℝ)*h))
       := sorry
   ```
   Proof: pure algebra. Unfold `localTruncationError`, peel the `i=0`
   term off the β-sum (it contributes `−h β₀ y'(x)`), apply
   preconsistency to convert `y(x)` to `Σ αᵢ y(x)`, apply (404b) to
   collapse the `y'(x)` coefficient. The `SatisfiesEq404b` cast bridge
   from the auto-memory file (`MEMORY.md`) is required:
   `convert ... using 1; exact Finset.sum_congr rfl …; push_cast; ring`.

6. **Sub-lemma F (the main theorem)**: triangle inequality on the
   decomposition + sub-lemmas C + D, with
   `Finset.abs_sum_le_sum_abs` and `mul_le_mul`-style monotonicity.

### Aristotle batch

After sorry-first compiles cleanly, submit sub-lemmas A–E (skip F —
the main theorem is the integration point, prove it manually after
its dependencies close). Aristotle is good at FTC plumbing
(sub-lemma A, B) and at Lipschitz/triangle bookkeeping (sub-lemma D).
Sub-lemma E is the algebraic decomposition; Aristotle may struggle
with the SatisfiesEq404b cast bridge — try it anyway, but keep your
manual proof ready.

Use the auto-memory note in `MEMORY.md` for the cast pattern when
working with `SatisfiesEq404b`.

Submit as a self-contained Lean file at
`.prover-state/aristotle_submissions/cycle_040/sub_lemmas.lean`,
exactly as cycle 039 did. Sleep 30 minutes after submission, then
poll once with `mcp__aristotle__get_status`.

### Faithfulness checklist (cycle 040 specifics)

- [ ] **Tautology check**: the theorem's conclusion is a numerical
      bound — verify it does not collapse to a hypothesis.
- [ ] **Hypothesis strength check**: `hf_lip` (Lipschitz) and
      `hf_y_bound` are textbook-required. Do *not* add a closed-ball
      strengthening (Butcher's hypothesis is global Lipschitz on the
      relevant interval).
- [ ] **Definition smuggling**: do not redefine `localTruncationError`.
      Use the existing one from `def:406A`.
- [ ] **Textbook-discrepancy escalation**: if you find the
      decomposition `iαᵢ − βᵢ` vs `βᵢ` discrepancy is real, file the
      issue file before committing.

## Fallback target — only if sorry-first signature does not compile

If the sorry-first scaffold does not compile within ~45 minutes (most
likely cause: `LipschitzWith L.toNNReal f` or `deriv y` mismatch with
Mathlib's `intervalIntegral` API), **switch immediately** to:

**Fallback: `def:451A`** — G-stable (Butcher §451). Read
`extraction/formalization_data/entities/def_451A.json`. This is a
standalone Chapter 4 definition with no Ch.4 prerequisites in our
codebase yet (its dependencies `def:404B` and any G-stability prereq
are already in or self-contained). It is a pure `def`+`structure` +
witness deliverable, mirroring `def:357B` (algebraic stability) in
shape — likely 1-cycle tractable. After fallback, submit a sanity
witness (e.g. trivial linear test problem) per CLAUDE.md
non-vacuity rule.

Do **not** chain to a different fallback. If even def:451A is
intractable, write an issue describing why and stop — a cycle with
"sorry-first lem:406B + open issue" is acceptable progress per
CLAUDE.md's "minimum: decompose a sorry or write an issue" rule.

## What NOT to try (failed approaches and stale traps)

- **Do NOT** generalise `localTruncationError` to vector-valued
  `y : ℝ → ℝ^N`. Cycle 039's definition is scalar; generalising is a
  separate infrastructure cycle and not on the critical path. Stay
  scalar.
- **Do NOT** attempt to *construct* the exact solution `y` inside
  `lem:406B`. Take it as a hypothesis (just like `def:402A`'s
  `IsConvergent` does). The
  `picard_lindelof_bound_strengthening` issue does not block
  `lem:406B`.
- **Do NOT** raise `maxHeartbeats` above 200000. If sub-lemma F or E
  times out, decompose further (e.g. peel out a separate `α`-sum
  bound and `β`-sum bound).
- **Do NOT** introduce `axiom`/`constant`. If sub-lemma B's
  change-of-variables FTC is unwieldy, write it as a helper lemma in
  the same file rather than axiomatising it.
- **Do NOT** edit `scripts/autonomous_loop.py`. Scanner false
  positives go in `.prover-state/issues/` for the loop maintainer (see
  `tautology_scanner_false_positives.md` from cycle 015).
- **Do NOT** touch any `extraction/raw_text/`,
  `extraction/formalization_data/entities/*.json`, or
  `extraction/formalization_data/index.json` /
  `topo_order.json` / `by_chapter.json`. These are regenerated. Edit
  only `extraction/formalization_data/lean_status.json` to record
  formalization status.
- **Do NOT** silently follow Butcher's algebraic decomposition without
  re-deriving it. The planner suspects a textbook typo; the worker
  must verify.

## Bookkeeping

When work lands:
1. Update `extraction/formalization_data/lean_status.json` row for
   `lem:406B` (or `def:451A` if you fall back) — set status,
   `lean_file`, `lean_symbol`.
2. Update `plan.md` Chapter 4 row from `[ ]` to `[x]` (or `[~]` if you
   landed structure + sub-lemmas but not the main theorem).
3. Update progress count: 39 → 40 (or 39 if structure-only).
4. Write `.prover-state/task_results/cycle_040.md` per the CLAUDE.md
   format, with the **Faithfulness check** section filled in
   exhaustively for `lem:406B` (or fallback).
5. If you ship structure + some sub-lemmas with the main theorem
   still `sorry`, that's fine — the cycle still moves the chain
   forward, and `[~]` (in progress) is the right plan.md status.
6. If you discover the textbook decomposition discrepancy is real,
   the issue file from §"Note on the textbook bound" is the
   load-bearing artefact for cycle 041 to pick up.

## Why this cycle, this target

`thm:406C` (the only dependent of `lem:406B`) sits on the critical
path to `thm:243A` (the cross-chapter Ch.2→Ch.4 deferral). Every
other Chapter 4 leaf — `thm:431A`, `thm:441C`, `thm:454A`, the
`def:442A` principal-sheet machinery, the §410 order-criteria
theorems — is parallel to this chain, not on it. Picking
`lem:406B` is the strategic move; picking another Ch.4 leaf would
be cherry-picking per CLAUDE.md's "follow the strategy" rule.

The scale of the cycle (one theorem + 5 sub-lemmas + analysis
infrastructure) genuinely is multi-cycle. **Sorry-first** is the
correct deliverable shape: it locks in the signature, exposes the
sub-lemmas as the unit of future Aristotle work, and lets cycles 041
and 042 close them one at a time without redesigning the overall
proof. Aim for "structure + 2 sub-lemmas closed" as the realistic
cycle 040 ceiling; anything more is bonus.
