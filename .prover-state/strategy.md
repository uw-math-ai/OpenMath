# Cycle 052 Strategy — `globalError_eq_linRec` (bridge LMM error sequence to §141 `linRec`)

## Status going in

- **Sorry count: 1** at `OpenMath/Chapter4/Section404.lean:2014`
  (`stable_consistent_isConvergent`, the cycle-047 outer-assembly
  scaffold). **DO NOT touch this sorry this cycle.** It is the
  cycle 053+ outer-assembly target.
- **Pending Aristotle: none.**
- **Last cycle delivered**: `globalError_per_step_sum_form` (cycle
  051) — the per-step bound parameterised by the *sum* of recent
  errors instead of an abstract `Mmax`.

The convergence theorem `thm:406D` is being assembled brick-by-brick:
each cycle adds one helper lemma keeping `sorry` count at 1. Cycles
045–051 closed seven helpers; cycle 052 adds the eighth — and the
first piece of the outer assembly itself, in the form of an
*algebraic identity* (no analytic hypotheses required).

## This cycle's target: `globalError_eq_linRec`

A single private helper lemma that **expresses the LMM global error
sequence as a `Section141.linRec`** with explicit parameters. This is
step 1+2 of the cycle 051 outer-assembly outline, factored out as a
standalone identity so cycle 053 can compose it with
`Section141.linRec_closed_form` (cycle 012) to get the explicit
`Σ θ_{n-i} ε'_i + Σ θ_{n-i} ψ_i` decomposition.

### Why this lemma

The cycle 045 lemma's per-step bound has the shape

  `|ε_n − Σ_{j:Fin k} α_{j+1} · ε_{n−1−j}|  ≤  C_h · Mmax + D_h · h²`

i.e. it bounds the *residual* of the linear recurrence. Define

  `ψ(n) := ε(n) − Σ_{j:Fin k} α_{j+1} · ε(n−1−j.val)`

so that **by definition** `ε` satisfies the inhomogeneous linear
recurrence `ε(n) = Σ α(j) · ε(n−1−j) + ψ(n)` for every `n`. Together
with the trivial initial values `ε(j) = ε(j)` for `j : Fin k`, this
characterises `ε` as the unique solution `linRec k α y₀init ψ`.
Cycle 053 can then apply `linRec_closed_form` to get the
`θ`-decomposition.

This is **pure algebra** — no hypotheses on `f`, `yex`, Lipschitz,
consistency, smallness, etc. The lemma is a uniqueness-by-induction
identity. That makes it (a) tractable in one cycle, and (b)
maximally reusable downstream.

### Concrete signature (target)

Insert immediately AFTER `globalError_per_step_sum_form`
(line 1986) and BEFORE the `LinearMultistepMethod.stable_consistent_isConvergent`
docstring block (currently line 1988). Keep `private` (matches
neighbouring helpers).

```lean
open OpenMath.Chapter1.Section141 in
/-- **The LMM global error sequence equals `Section141.linRec`.**
Given an LMM `M`, an exact solution `yex`, and any iterate sequence
`Y`, the global error
    ε(n) := yex(x₀ + n·h) − Y(n)
is exactly `Section141.linRec` applied with:

* coefficients `α(j) := M.α j.succ` (the tail-α coefficients),
* initial values `y₀init(j) := ε(j.val)` (the first `k` errors),
* forcing `ψ(n) := ε(n) − Σ_{j:Fin k} M.α j.succ · ε(n − 1 − j.val)`
  (the per-step residual at index `n`).

This is a pure algebraic identity — no hypotheses on `f`, `yex`, or
`Y`. The proof is by strong induction on `n`: for `n < k`,
`linRec_of_lt` returns the initial value `y₀init ⟨n, _⟩ = ε n`; for
`n ≥ k`, `linRec_of_ge` plus the IH plus the definition of `ψ`
collapse to `ε n` by `ring`.

Used by: cycle 053+ outer assembly of `thm:406D` — composes with
`Section141.linRec_closed_form` (cycle 012, Theorem 141A) to give
the explicit `θ`-decomposition. -/
private lemma globalError_eq_linRec
    {k : ℕ} (M : LinearMultistepMethod k)
    {yex : ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ} (n : ℕ) :
    yex (x₀ + (n : ℝ) * h) - Y n
      = linRec k
          (fun j : Fin k => M.α j.succ)
          (fun j : Fin k => yex (x₀ + (j.val : ℝ) * h) - Y j.val)
          (fun m =>
            (yex (x₀ + (m : ℝ) * h) - Y m)
              - ∑ j : Fin k, M.α j.succ
                  * (yex (x₀ + ((m - 1 - j.val : ℕ) : ℝ) * h)
                      - Y (m - 1 - j.val)))
          n := by
  sorry
```

Note: the `open OpenMath.Chapter1.Section141 in` line lets the
declaration use `linRec` unqualified. There is already an
`open OpenMath.Chapter1.Section141 in` at line 1684 for the
`theta_isHomogeneousSolution`/`theta_bounded_of_isStable` helpers;
follow the same pattern (a per-declaration `open ... in` rather than
a file-level `open`).

## Approach (specific tactic plan)

The proof is strong induction on `n` with two cases (`n < k` and
`n ≥ k`):

### Step 0 — Set up the induction.
```lean
induction n using Nat.strong_induction_on with
| _ n ih =>
  by_cases hn : n < k
  · -- Case n < k: linRec returns the initial value.
    rw [linRec_of_lt _ _ _ _ _ hn]
    -- Goal: yex(x₀ + n·h) - Y n
    --     = (fun j : Fin k => yex(x₀ + j.val·h) - Y j.val) ⟨n, hn⟩
    rfl                       -- β-reduces the lambda; `j.val = n`.
  · -- Case n ≥ k: linRec recurses.
    push_neg at hn
    rw [linRec_of_ge _ _ _ _ _ hn]
    -- Goal: ε n = Σ α(j) · linRec(n-1-j.val) + ψ n
    -- where ψ unfolds to (ε n) - Σ α(j) · ε(n-1-j.val).
    sorry
```

### Step 1 — Apply IH to each `linRec(n-1-j.val)` term.

For each `j : Fin k`, `n - 1 - j.val < n` (since `n ≥ k ≥ 1` for the
recursive case to fire — but: for `k = 0`, the `Fin 0` sum is empty,
so this branch is vacuous).

Case split on `k = 0` vs `k ≥ 1` first if Lean complains about the
`n ≥ 1` derivation:

```lean
rcases Nat.eq_zero_or_pos k with hk0 | hkpos
· -- k = 0: the `Fin 0` sum vanishes; ψ n = ε n; linRec n = ε n. 
  subst hk0
  simp [linRec, Finset.sum_empty] -- or unfold linRec_of_ge directly
· -- k ≥ 1, n ≥ k ≥ 1, so n - 1 is well-defined and n - 1 - j.val < n.
  have hsub : ∀ j : Fin k, n - 1 - j.val < n := fun j => by
    have hj : j.val < k := j.isLt
    have h1 : 1 ≤ n := le_trans hkpos hn
    omega
  have h_eq : ∀ j : Fin k,
      linRec k _ _ _ (n - 1 - j.val) =
        yex (x₀ + ((n - 1 - j.val : ℕ) : ℝ) * h) - Y (n - 1 - j.val) :=
    fun j => (ih (n - 1 - j.val) (hsub j)).symm
  simp_rw [h_eq]
  ring
```

The `_`s in `linRec k _ _ _` are: the α-coefficients, the y₀init
function, the ψ function — all the same triple as in the goal, so
Lean should unify them. If unification fails (because the lambdas in
the IH are not syntactically identical to the lambdas in `h_eq`),
make the IH application explicit:

```lean
have h_eq : ∀ j : Fin k,
    linRec k
      (fun j' : Fin k => M.α j'.succ)
      (fun j' : Fin k => yex (x₀ + (j'.val : ℝ) * h) - Y j'.val)
      (fun m => (yex (x₀ + (m : ℝ) * h) - Y m)
                - ∑ j' : Fin k, M.α j'.succ
                    * (yex (x₀ + ((m - 1 - j'.val : ℕ) : ℝ) * h)
                        - Y (m - 1 - j'.val)))
      (n - 1 - j.val) =
        yex (x₀ + ((n - 1 - j.val : ℕ) : ℝ) * h) - Y (n - 1 - j.val) :=
  fun j => (ih (n - 1 - j.val) (hsub j)).symm
```

### Step 2 — `simp_rw` + `ring`.

After substituting all the IH applications, both sides become
syntactically `Σ α(j) · ε(n-1-j) + (ε n − Σ α(j) · ε(n-1-j))`, which
collapses to `ε n` by `ring`. The `simp_rw` needs the rewriting form
of the IH (i.e., `simp_rw [h_eq]` rewrites occurrences of
`linRec k _ _ _ (n - 1 - j.val)` to `yex(...) − Y(...)`).

### Step 0 fallback (if `rfl` fails for `n < k` case)

If `rfl` doesn't close the `n < k` case, the issue is likely that
the lambda's β-reduction is not happening automatically. Try in
order:

```lean
· rw [linRec_of_lt _ _ _ _ _ hn]
  -- One of these should close it:
  rfl                   -- β-reduce the y₀init lambda
  -- OR
  simp only             -- force β-reduction
  -- OR
  show yex (x₀ + ((⟨n, hn⟩ : Fin k).val : ℝ) * h) - Y (⟨n, hn⟩ : Fin k).val
       = yex (x₀ + (n : ℝ) * h) - Y n
  rfl
```

The `Fin.val ⟨n, hn⟩ = n` step is definitional, so `rfl` should
work. If not, `simp` is the bigger hammer.

## Why this is a 1-cycle target (not 2+)

* No new infrastructure — uses only `Section141.linRec_of_lt`,
  `linRec_of_ge`, and `Nat.strong_induction_on`. All three are
  standard.
* No analytic hypotheses — pure algebraic identity.
* Decomposition into two cases (`n < k`, `n ≥ k`) plus a `k = 0` /
  `k ≥ 1` sub-case is mechanical.
* The `ring`-closer at the end is well-tested at this point in the
  codebase; the algebra is "x = a + (x − a)".

Estimated proof body: ~25–35 lines.

## Aristotle plan

Submit ONE Aristotle job containing only `globalError_eq_linRec` at
the start of the cycle, with `linRec`, `linRec_of_lt`,
`linRec_of_ge`, and `Nat.strong_induction_on` in the prompt's
"available lemmas" hint. The lemma is small and uses only
elementary recursion machinery; Aristotle should solve it within
the 30-minute window.

While Aristotle runs, attempt the manual proof per Step 0 → 1 → 2
above. The induction skeleton is rote enough that the manual proof
should land first; if Aristotle returns a cleaner version, prefer
the cleaner one for readability.

CLAUDE.md cap: ONE Aristotle status check after 30 minutes. Do not
poll repeatedly.

## What NOT to do (failure modes from prior cycles)

* **DO NOT close the line-2014 sorry**
  (`stable_consistent_isConvergent`). It is the cycle 053+ outer-
  assembly target. Your job this cycle is to add ONE helper lemma
  that the outer assembly will consume in cycle 053. Touching the
  line-2014 sorry is a high-risk move (cycle 047 was reverted for
  introducing a sorry; the recovery protocol has been: add one
  closed helper per cycle).

* **DO NOT introduce new `sorry`s.** The new helper must compile
  cleanly. If you cannot close the proof in this cycle, file a
  structured issue at
  `.prover-state/issues/global_error_eq_linRec_blocked.md` per
  CLAUDE.md issue protocol — do NOT commit a `sorry`-bodied lemma
  (sorry count must remain at 1).

* **DO NOT generalise to vector-valued `y : ℝ → ℝ^N`.** The scalar-
  only convention has been stable since cycle 040; this lemma
  inherits it.

* **DO NOT add hypotheses about `f`, Lipschitz, `IsLMMSolution`,
  consistency, stability, etc.** This is a pure algebraic identity.
  Adding hypotheses makes it less reusable in cycle 053+ and
  obscures the mathematical content.

* **DO NOT raise `maxHeartbeats`.** A 35-line induction proof
  closing with `ring` does not need it. If `simp_rw` + `ring` is
  slow, decompose: prove `h_eq` and rewrite occurrences one at a
  time, then close with `linarith` or explicit `calc`.

* **DO NOT use `Nat.rec` or `Nat.recOn` for the induction.** The
  Section 141 file uses `Nat.strong_induction_on` consistently;
  follow the same convention. Strong induction is mandatory because
  the recursive call is to `n − 1 − j.val`, not `n − 1`.

* **DO NOT use `Finset.sum_le_sum_nbij'`** — it does not exist
  (cycle 050). N/A this cycle (no sum-reindexing needed) but worth
  reiterating.

* **DO NOT poll Aristotle more than once.** CLAUDE.md is explicit.

* **DO NOT take any "stuck on Section404.lean / commit didn't
  land / sorry count regressed" framing in the prompt at face
  value.** The pattern matches cycles 008/014/015/040/041 phantoms
  — verify with `git log --oneline -5`,
  `git diff HEAD~1 HEAD --stat`, and the current sorry count
  (`grep -n "sorry" OpenMath/Chapter4/Section404.lean | wc -l`).
  If the verification commands say "1 sorry, last commit landed",
  proceed with the proof work.

## Pre-commit faithfulness checklist

For `globalError_eq_linRec` (the only new declaration expected this
cycle):

* **Entity ID**: N/A — internal helper, not a Butcher entity. Same
  category as `recentSum_swap_bound`, `globalError_per_step_sum_form`,
  `sum_theta_psi_contraction`. Document in the docstring with the
  cycle 012 (`linRec_closed_form`) and cycle 053+ (outer assembly)
  cross-references explicit.
* **Tautology check**: PASS — the conclusion is a uniqueness
  identity. The `linRec` term on the RHS is computed by
  `Section141.linRec`'s recursion; the `ε` term on the LHS is the
  global error. They are not syntactically identical.
* **Identity check**: PASS — the proof body is strong induction +
  `linRec_of_lt`/`linRec_of_ge` + `ring`. The `ring` step does real
  algebraic work (cancelling `Σ α · ε` against itself); this is not
  a vacuous re-export.
* **Hypothesis strength check**: PASS — the lemma takes only the
  most general data (`M`, `yex`, `Y`, `x₀`, `h`, `n`). No
  Lipschitz, ODE, consistency, or stability hypotheses; the
  identity is pure algebra and would not be improved by weakening
  hypotheses (none to weaken).
* **Class/structure check**: N/A.
* **Definition smuggling check**: N/A.
* **Absent theorem check**: N/A — the docstring forward-references
  `cycle 053+`'s consumer, not a non-existent theorem.

## Stretch goal (optional, ONLY if main lemma lands in <1 hour)

If `globalError_eq_linRec` compiles cleanly with significant time
remaining, prepare a *second* helper lemma:

```lean
open OpenMath.Chapter1.Section141 in
/-- **Closed-form decomposition of the LMM global error.**
Compose `globalError_eq_linRec` with `linRec_closed_form` to get
the explicit `θ`-decomposition. -/
private lemma globalError_closed_form
    {k : ℕ} (M : LinearMultistepMethod k)
    {yex : ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ} (n : ℕ) :
    yex (x₀ + (n : ℝ) * h) - Y n
      = (∑ i ∈ Finset.range (min k (n + 1)),
            theta k (fun j : Fin k => M.α j.succ) (n - i)
              * yPrime k (fun j : Fin k => M.α j.succ)
                  (fun j : Fin k => yex (x₀ + (j.val : ℝ) * h) - Y j.val)
                  i)
        + ∑ i ∈ Finset.Icc k n,
            theta k (fun j : Fin k => M.α j.succ) (n - i)
              * ((yex (x₀ + (i : ℝ) * h) - Y i)
                  - ∑ j : Fin k, M.α j.succ
                      * (yex (x₀ + ((i - 1 - j.val : ℕ) : ℝ) * h)
                          - Y (i - 1 - j.val))) := by
  rw [globalError_eq_linRec M n]
  exact linRec_closed_form k _ _ _ n
```

This is a one-liner once `globalError_eq_linRec` is in place. If
both compile, cycle 053 starts from a fully-decomposed shape.

This is OPTIONAL. If the main lemma is non-trivial (Step 0
fallback fires, or the `simp_rw` is finicky), skip the stretch
goal — `globalError_eq_linRec` alone is the cycle 052 deliverable.

## Pre-commit verification

Before committing:

1. `lake env lean OpenMath/Chapter4/Section404.lean` — must compile
   cleanly with no new errors.
2. `lean_diagnostic_messages` on Section404.lean — must show ONLY
   the four pre-existing warnings (unused-variable at lines 568,
   627, 1204; sorry at line 2014). NO new warnings.
3. `lean_verify` on
   `OpenMath.Chapter4.Section404.globalError_eq_linRec` — must
   report axioms `[propext, Classical.choice, Quot.sound]` only
   (no new axioms).
4. Sorry count must remain at **1** (line 2014 unchanged; no new
   sorries from the stretch goal either).
5. If the stretch goal lands too: also `lean_verify` on
   `globalError_closed_form` — same axiom report expected.

## Cycle 053+ preview (do not implement this cycle)

After `globalError_eq_linRec` lands, cycle 053 continues the outer
assembly:

1. **(this cycle's stretch goal, if not yet landed)** Compose with
   `linRec_closed_form` to expose the `Σ θ_{n-i} ε'_i + Σ θ_{n-i} ψ_i`
   shape.
2. Apply `theta_bounded_of_isStable` (cycle 047) to extract the `Θ`
   bound on `θ`. Need `0 < k` here — file an issue if `k = 0` becomes
   awkward (it should not, since `IsConvergent` is vacuous for `k = 0`
   in any practical sense; the `IsLMMSolution` recurrence becomes
   `Y(n) = -h · β_0 · f(...)`, a one-step explicit-ish iteration).
3. Apply this cycle's `globalError_per_step_sum_form` (and inheritor
   `globalError_eq_linRec` to translate the `ψ` shape) to get
   `|ψ_i| ≤ C_h · Sε(i) + D_h · h²`.
4. Apply `sum_theta_psi_contraction` (cycle 048) to bound
   `|Σ θ_{n-i} ψ_i|`.
5. Apply `recentSum_swap_bound` (cycle 050) to collapse the nested
   recent-window sum (gives `k · Σ |ε|`).
6. Apply `discrete_gronwall_exp_bound` (cycle 046) for the final
   exponential closed form.
7. Apply `starting_error_sum_tendsto_zero` (cycle 049) for the
   `φ(h) → 0` limit.
8. Combine via `Filter.Tendsto.add`, `squeeze_zero`,
   `Real.exp_continuous`.

Cycle 054 polishes the `Filter.Tendsto` algebra. Estimated total
remaining: 2–3 cycles (052 → 053 → 054) to close `thm:406D` and
unblock `thm:243A`.

## Reference: surrounding helper signatures (for orientation)

```
-- Section141 (cycle 012):
def linRec (k : ℕ) (α : Fin k → R) (y₀init : Fin k → R)
    (ψ : ℕ → R) : ℕ → R          -- Section141.lean:53
lemma linRec_of_lt … (h : i < k) :
    linRec k α y₀init ψ i = y₀init ⟨i, h⟩    -- Section141.lean:100
lemma linRec_of_ge … (h : k ≤ n) :
    linRec k α y₀init ψ n
      = (∑ j : Fin k, α j * linRec k α y₀init ψ (n - 1 - j.val)) + ψ n
                                              -- Section141.lean:107
theorem linRec_closed_form … :
    linRec k α y₀init ψ n
      = (∑ i ∈ Finset.range (min k (n + 1)),
             theta k α (n - i) * yPrime k α y₀init i)
        + ∑ i ∈ Finset.Icc k n,
            theta k α (n - i) * ψ i           -- Section141.lean:373

-- Section404 (cycles 045–051):
theorem globalError_recurrence_bound_textbook …  -- Section404.lean:1331
lemma discrete_gronwall_exp_bound …               -- Section404.lean:1631
theorem theta_bounded_of_isStable …               -- Section404.lean:1737
private lemma sum_theta_psi_contraction …         -- Section404.lean:1762
private lemma starting_error_each_tendsto_zero …  -- Section404.lean:1810
private lemma starting_error_sum_tendsto_zero …   -- Section404.lean:1851
private lemma recentSum_swap_bound …              -- Section404.lean:1886
private lemma globalError_per_step_sum_form …     -- Section404.lean:1936
theorem stable_consistent_isConvergent …          -- Section404.lean:2010
  -- ↑ this is the ONE remaining sorry (line 2014). DO NOT TOUCH.
```
