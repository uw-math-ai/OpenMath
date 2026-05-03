# Cycle 102 Strategy — close `localStageError_bound_b` (515b)

## Status snapshot

- **Sorry count: 1.** The lone remaining sorry is at
  `OpenMath/Chapter5/Section515.lean:629` inside
  `GeneralLinearMethod.localStageError_bound_b` (Butcher inequality
  515b of `lem:515A`).
- **Cycle 101 closed (515a)** via the T1+T2+T3+T4 decomposition with
  four private helpers (`aux_T1_eq_zero`, `aux_T2_eq_zero`,
  `aux_T3_bound`, `aux_T4_bound`) plus
  `aux_y_diff_norm_bound` (cycle 100). Score = +2, axiom-clean.
- **Aristotle**: not contributing this cycle. Skip the polling step.

## Priority 1 — close `localStageError_bound_b` (the only sorry)

This cycle's deliverable is the (515b) mirror of (515a). The
textbook decomposition is structurally analogous but with five key
adjustments:

1. **Output-side coefficients** `B`/`V` instead of `A`/`U`.
2. **Different matrix shape**: `B : Matrix (Fin r) (Fin s) ℝ` and
   `V : Matrix (Fin r) (Fin r) ℝ`, so the row index of the goal is
   `Fin r`.
3. **Integration over `[0, 1]`** (one fixed step from `xn1` to
   `xn1 + h`) instead of `[0, c_i]`.
4. **Extra `T3'` term** capturing `v_i · h · (y'(xn) − y'(xn1))`.
5. **Algebraic identity uses** `V·u = u` (replacing `U·u = 𝟙`) and
   `B·𝟙 + V·v = u + v` (replacing `c = A·𝟙 + U·v`).

### Mathematical decomposition (verify before coding!)

For the LHS of (515b):
```
X_b := u_i·y(xn) + v_i·h·y'(xn)
       − h·Σ_j B_{ij}·f(yex(xn1+h c_j))
       − Σ_j V_{ij}·(u_j·y(xn1) + v_j·h·y'(xn1))
```
where `xn = xn1 + h`. Substitute:

* **FTC** `y(xn1+h) − y(xn1) = h·∫_0^1 f(yex(xn1+hξ)) dξ` (apply
  `aux_T1_eq_zero` at `c_i := 1`).
* **Add/subtract** `f(yex(xn1)) = y'(xn1)`:
  `u_i·y(xn) = u_i·y(xn1) + u_i·h·y'(xn1) + T3b_int`
  where `T3b_int := u_i·h·∫_0^1 (f(yex(xn1+hξ)) − f(yex(xn1))) dξ`.
* **Bridge** `y'(xn) − y'(xn1) = f(yex(xn1+h)) − f(yex(xn1))`
  (via `hy_ode`):
  `v_i·h·y'(xn) = v_i·h·y'(xn1) + T3'b`
  where `T3'b := v_i·h·(f(yex(xn1+h)) − f(yex(xn1)))`.
* **Add/subtract** `y'(xn1)` in the B-sum:
  `h·Σ B_{ij}·f(yex(xn1+h c_j))
     = (Σ B_{ij})·h·y'(xn1) + T4b`
  where `T4b := h·Σ B_{ij}·(f(yex(xn1+h c_j)) − f(yex(xn1)))`.
* **V-sum unfolds** via `V·u = u`:
  `Σ V_{ij}·(u_j y(xn1) + v_j·h·y'(xn1))
     = u_i·y(xn1) + (Σ V_{ij} v_j)·h·y'(xn1)`.

Combining, the leading-order terms in `y(xn1)` and `h·y'(xn1)`
must cancel. The `h·y'(xn1)` coefficient is
`u_i + v_i − Σ B_{ij} − Σ V_{ij} v_j`, which equals zero by
**consistency** `B·𝟙 + V·v = u + v`:
`(B·𝟙)_i + (V·v)_i = u_i + v_i  ⇒  Σ B_{ij} + Σ V_{ij} v_j = u_i + v_i`.

So `X_b = T3b_int + T3'b − T4b`, and
```
|X_b| ≤ |T3b_int| + |T3'b| + |T4b|
      ≤ ½·|u_i|·h²L²M + |v_i|·h²L²M + h²L²M·Σ|B_{ij} c_j|
      = h²L²M·(½|u_i| + |v_i| + Σ|B_{ij} c_j|)
```
matching the textbook bound exactly.

### Step 1 — refactor `aux_T4_bound` to general row dim

`aux_T4_bound` (Section515.lean:371) currently takes
`A : Matrix (Fin s) (Fin s) ℝ` and `i : Fin s`. For the (515b) call
we need it on `M.B : Matrix (Fin r) (Fin s) ℝ` with `i : Fin r`.

**Refactor in place**: change `{s : ℕ}` to `{s r : ℕ}`, change
`A : Matrix (Fin s) (Fin s) ℝ` to `A : Matrix (Fin r) (Fin s) ℝ`,
and change `i : Fin s` to `i : Fin r`. The proof body is unchanged
— it never uses the row index structurally. Update the call site in
`localStageError_bound_a` (line 521): the call already passes `M.A`
with `r := s` implicitly; verify Lean's unification still infers
the right row dim by recompiling Section515.lean after the rename.

### Step 2 — add `aux_T3'_bound` (new helper)

For the `T3'b` term:
```lean
private theorem aux_T3'_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (vi : ℝ) :
    |vi * h * (f (y (x + h)) - f (y x))|
      ≤ |vi| * (h^2 * L^2 * M_bound) := by
  -- |f(y(x+h)) - f(y x)| ≤ L * |y(x+h) - y x| ≤ L * (h * 1 * (L * M))
  -- via Lipschitz + aux_y_diff_norm_bound at ξ = 1.
```
**Proof sketch**: Lipschitz of `f` gives
`|f(y(x+h)) − f(y x)| ≤ L · |y(x+h) − y x|` (use the same
`hf_lip.dist_le_mul` + `Real.dist_eq` + `Real.coe_toNNReal` chain
as in `aux_T3_bound`/`aux_T4_bound`). Then need
`|y(x+h) - y x| = |y(x + h*1) - y x|`. Apply
`aux_y_diff_norm_bound _hL _hM hy_C1 hy_ode hf_y_bound x h hh 1`
to get `|y(x + h*1) − y x| ≤ h · |1| · (L · M_bound) = h · L · M`.
Multiply through by `|vi · h|`:
`|vi · h · (f − f)| = |vi| · h · |f − f|` (using `abs_mul` twice
and `abs_of_nonneg hh`)
`≤ |vi| · h · L · h · L · M = |vi| · h² · L² · M`.
Close with `ring`.

Note: `x + h*1 = x + h` requires a `simp` step after invoking
`aux_y_diff_norm_bound` since the latter's conclusion is in the
`x + h*ξ` shape.

### Step 3 — add `aux_T2_b_eq_zero` (new helper)

Algebraic identity using `V·u = u` and `B·𝟙 + V·v = u + v`:
```lean
private theorem aux_T2_b_eq_zero {s r : ℕ}
    (B : Matrix (Fin r) (Fin s) ℝ) (V : Matrix (Fin r) (Fin r) ℝ)
    (u v : Fin r → ℝ)
    (hVu : V *ᵥ u = u)
    (hCons : B *ᵥ (fun _ => 1) + V *ᵥ v = u + v)
    {y : ℝ → ℝ} (xn1 h : ℝ) (i : Fin r) :
    u i * y xn1 + (u i + v i) * h * deriv y xn1
      - (∑ j, V i j * (u j * y xn1 + v j * h * deriv y xn1))
      - (∑ j, B i j * h * deriv y xn1) = 0 := by
```
**Proof sketch**: same shape as `aux_T2_eq_zero` (Section515.lean:237).
Distribute the V-sum into y-part and h·y'-part exactly as
`hU_split` did for `U`; show `Σ V_{ij} u_j = u_i` (via
`(V *ᵥ u) i = ∑ V_{ij} u_j` rfl + `hVu`); show
`Σ B_{ij} + Σ V_{ij} v_j = u_i + v_i` from
`(B·𝟙) i = Σ B_{ij}` (rfl-unfold + `simp` to drop `*1`) and
`(V·v) i = Σ V_{ij} v_j` (rfl) plus `hCons`. Close with `ring`.

### Step 4 — close `localStageError_bound_b`

Mirror `localStageError_bound_a`'s proof body (Section515.lean:497–591)
exactly, with these substitutions:

| (515a) | (515b) |
|---|---|
| Integral upper bound `c i` | `1` |
| `(c i)^2 / 2` term | `1/2` (i.e. `½ |u_i|`) |
| `Σ A i j * h * deriv yex xn1` | `Σ B i j * h * deriv yex xn1` |
| `aux_T2_eq_zero ... A U u v _hUu c hc_def_eq` | `aux_T2_b_eq_zero ... M.B M.V u v _hVu _hCons` |
| `aux_T3_bound ... (c i) (_hc_nonneg i)` | `aux_T3_bound ... 1 (by norm_num : (0:ℝ) ≤ 1)`, gives `½·h²L²M·1²`; multiply by `|u_i|` via separate calc step |
| no T3' term | new `aux_T3'_bound _hL _hM _hf_lip _hy_C1 _hy_ode hf_yex_bound xn1 h _hh (v i)` |
| `aux_T4_bound ... M.A c xn1 h _hh i` | `aux_T4_bound ... M.B c xn1 h _hh i` (after Step 1 refactor) |
| `linear_combination hT1 + hT2 - hT3_expand + hT4_expand + hsumA_swap - (c i * h) * hy'0` | `linear_combination` with new coefficients reflecting the (515b) structure |

The final `linear_combination` step is the most error-prone. The
coefficient structure mirrors (515a) but with:
- `hT1` multiplied by `u i` (since `T3b_int` carries the `u_i`
  factor)
- new `hT3'b_def` term (the `T3'b` definition unfolded)
- `hsumA_swap` becomes `hsumB_swap` (Σ B over `deriv yex` ↔ Σ B
  over `f(yex)`)
- `(c i * h) * hy'0` becomes `(u i + v i) * h * hy'0` (matching
  the `(u i + v i) * h * deriv y xn1` term in `aux_T2_b_eq_zero`)

If `linear_combination` fails, use the backup plan below. Spend
**at most 30 minutes** attempting `linear_combination` directly
before falling back to manual decomposition.

### Step 5 — verification

Run all three checks **in the exact order below** (per
`tautology_scanner_false_positives.md` re: stale-cache `sorryAx`):

```bash
lake env lean OpenMath/Chapter5/Section515.lean    # standalone compile
lake build OpenMath.Chapter5.Section515            # update .olean cache
```

Then in Lean:
```
#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStageError_bound_b
#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStageError_bound_a
```

Both should show `[propext, Classical.choice, Quot.sound]` only.
Standalone compile should report **0 sorry** in `Section515.lean`.

## Priority 2 — update `lean_status.json` and write task results

If Priority 1 succeeds:

* **Update** `extraction/formalization_data/lean_status.json`: mark
  `lem:515A` from `partial` to `formalized` (both 515a and 515b
  closed).
* **Update** `plan.md`: change `[~]` to `[x]` on the `lem:515A`
  row in Chapter 5 and note "(cycle 102 closure: 515a + 515b
  axiom-clean)". Also bump "Progress: 63 / 175" to "64 / 175"
  (`lem:515A` was previously partial-counted; verify the count is
  consistent with `lean_status.json`).
* **Write** `.prover-state/task_results/cycle_102.md` with the
  standard format including a faithfulness check that flags the
  inherited `0 ≤ c i` restriction (carries over from cycle 101)
  and notes `lem:515A` is now complete.

## Priority 3 — pre-commit faithfulness audit

For each new lemma introduced this cycle:

* `aux_T3'_bound`: not a textbook-numbered lemma; sub-bound for
  `T3'b`. No divergence (sign-symmetric in `vi` because of
  `|vi|`).
* `aux_T2_b_eq_zero`: not a textbook-numbered lemma; algebraic
  identity. No divergence.
* `aux_T4_bound` (refactored): same statement modulo row dim
  generalization. No semantic change.
* `localStageError_bound_b` (textbook entity `lem:515A`,
  inequality 515b): same `(hc_nonneg : ∀ i, 0 ≤ c i)` faithfulness
  divergence as cycle 101's (515a). No new divergence; document in
  the docstring + cycle 102 task result.

## What NOT to try (explicitly)

* **Do NOT** raise `maxHeartbeats` above 200000.
* **Do NOT** try to bound `T3'b` by `aux_T3_bound` directly — the
  T3 helper integrates over `[0, c_i]` whereas T3'b is a single
  *point evaluation* `f(yex(xn1+h)) − f(yex(xn1))`. They are
  different shapes; `aux_T3'_bound` is genuinely new.
* **Do NOT** rewrite `aux_T4_bound`'s row index from `Fin s` to
  `Fin r'` and then try to make it polymorphic over BOTH dims by
  using a sigma type — just generalize to two index params
  `{s r : ℕ}` and a matrix `Matrix (Fin r) (Fin s) ℝ`. The cycle
  101 callsite will continue to work with `r := s` inferred (the
  unification is unambiguous because `M.A` has type
  `Matrix (Fin s) (Fin s) ℝ`).
* **Do NOT** try `linarith` in place of `linear_combination` for
  the algebraic decomposition. Cycle 101 confirmed `linarith`
  treats products as opaque atoms and fails to bridge `c i * h *
  deriv yex xn1` ↔ `h * c i * f (yex xn1)`. Use
  `linear_combination` from the start.
* **Do NOT** introduce `axiom`/`constant`. Every step has a
  Mathlib-grounded proof.
* **Do NOT** edit `scripts/autonomous_loop.py`; the prompt-builder
  staleness phantoms are loop-maintainer territory (see
  `tautology_scanner_false_positives.md`).
* **Do NOT** poll Aristotle more than once. Per cycle 101, the
  current batch is at 2% and not contributing — skip the poll
  entirely this cycle.
* **Do NOT** redefine `IsConvergent`, `IsConsistent`, or
  `IsStable`. The (515b) proof consumes only the algebraic
  hypotheses bundled in `localStageError_bound_b`'s signature.
* **Do NOT** start `lem:515B` (`ϕ` linear-system bound) yet — it
  depends on (515a) AND (515b) AND a new contraction argument
  for `(I − h₀L|A|) ϕ = ½c² + |A||c|`. Save for cycle 103+.
* **Do NOT** weaken or bypass the cycle 101 `0 ≤ c i` hypothesis.
  The cycle 102 (515b) must inherit the same restriction
  consistently — both inequalities (515a) and (515b) take the
  same `_hc_nonneg` parameter.

## Backup plan (if `linear_combination` blocks in Step 4)

If the algebraic-identity step fails to close in 30 minutes:

1. **Decompose into smaller `have` lemmas**, each proving one
   piece of the cancellation: e.g.
   `have h_uy_split : u i * yex (xn1 + h) = u i * yex xn1 +
       u i * h * deriv yex xn1 + T3b_int_signed`.
   Then close the final equality with chained `rw`s + `ring`.
2. **Worst case**, leave (515b) as a `sorry` and commit
   the four new helpers (`aux_T3'_bound`, `aux_T2_b_eq_zero`, the
   `aux_T4_bound` refactor) as a +1 partial progress cycle. Sorry
   count would remain at 1 but the helper infrastructure is now
   ready for cycle 103 to consume.

The cycle should **not** end with score < +1. Even the worst-case
backup commits real infrastructure progress (three new
sub-lemmas).

## File touchpoints

* `OpenMath/Chapter5/Section515.lean` — primary file, all changes
  here.
* `extraction/formalization_data/lean_status.json` — Priority 2.
* `plan.md` — Priority 2 (status checkbox).
* `.prover-state/task_results/cycle_102.md` — Priority 2.

No edits expected to:
* `OpenMath/Chapter5/Section512.lean`, `Section510.lean`,
  `Section513.lean`, `Section514.lean` (definitions stable).
* `Section404.lean` (LMM analog, unaffected by GLM §515 work).
* Any extraction or scripts/ files.
