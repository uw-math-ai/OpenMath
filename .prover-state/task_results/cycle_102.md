# Cycle 102 Results

## Worked on
`OpenMath/Chapter5/Section515.lean:629` — closing the lone remaining
sorry inside `GeneralLinearMethod.localStageError_bound_b` (Butcher
inequality 515b of `lem:515A`).

This completes `lem:515A` (both 515a from cycle 101 and 515b from
this cycle), so §515's first lemma is fully formalized.

## Approach
Followed the planner strategy verbatim: T1+T2+T3+T3'+T4 decomposition
with five textbook steps for the (515b) mirror of (515a):

1. **Refactored `aux_T4_bound`** in place from `{s : ℕ}` /
   `Matrix (Fin s) (Fin s) ℝ` / row index `Fin s` to
   `{s r : ℕ}` / `Matrix (Fin r) (Fin s) ℝ` / row index `Fin r`.
   The proof body never used the row-index structure, so it carried
   over unchanged. Cycle 101's call site (with `M.A` of square shape)
   continues to type-check via Lean's unification with `r := s`.

2. **Added `aux_T3'_bound`** — new helper for the point-evaluation
   bound `|v_i · h · (f(y(x+h)) − f(y x))| ≤ |v_i| · h² L² M`.
   Proof: Lipschitz bridge `|f(y(x+h)) − f(y x)| ≤ L · |y(x+h) − y x|`;
   then `aux_y_diff_norm_bound` at `ξ = 1` gives
   `|y(x+h*1) − y x| ≤ h · |1| · (L·M)` which simplifies to
   `h · L · M` via `abs_one`/`mul_one` rewrites; multiply by
   `|v_i| · h` (with `0 ≤ h` to extract from absolute value).

3. **Added `aux_T2_b_eq_zero`** — output-side algebraic identity:
   `u_i·y(xn1) + (u_i + v_i)·h·y'(xn1)
      − Σ V_{ij}·(u_j·y(xn1) + v_j·h·y'(xn1))
      − Σ B_{ij}·h·y'(xn1) = 0`
   under hypotheses `V·u = u` and `B·𝟙 + V·v = u + v`.
   Proof: distribute V-sum into y/y' parts (mirroring `aux_T2_eq_zero`
   for U), use rfl-unfolds of `(V*ᵥu) i`, `(V*ᵥv) i`, `(B*ᵥ𝟙) i`,
   then close with `linear_combination -(h * deriv y xn1) * hCons_i`
   where `hCons_i : Σ B_{ij} + Σ V_{ij} v_j = u_i + v_i` is extracted
   from `congrFun hCons i`.

4. **Closed `localStageError_bound_b`** by mirroring (515a)'s proof
   body. Specialized `aux_T1_eq_zero` at `c_i := 1` then bridged
   `xn1 + h*1 = xn1 + h` via a `rw` step; specialized `aux_T3_bound`
   at `c_i := 1` and used `simpa` to drop the `* 1^2` factor; called
   `aux_T3'_bound` for the new T3' term and `aux_T4_bound` (with the
   row-dim refactor in step 1) for the T4 term. Then mirrored the
   (515a) `set`-based abbreviations (T3v, T3'v, T4v, Iv, SBfb, Vinp,
   SBhy, SBhf) and discharged the algebraic decomposition with
   `linear_combination u i * hT1 + hT2 - u i * hT3_expand
       + hT4_expand + hsumB_swap - (u i + v i) * h * hy'0
       + v i * h * hy'h`.
   The triangle inequality cascade `|A + B − C| ≤ |A| + |B| + |C|`
   then plugs in the three sub-bounds and a final `ring` step
   collapses everything into the textbook RHS
   `h² L² M (½|u_i| + |v_i| + Σ|B_{ij} c_j|)`.

5. **Updated `lean_status.json`** to mark `lem:515A` as `formalized`
   (with both `localStageError_bound_a` and `localStageError_bound_b`
   in `lean_symbol`); updated `plan.md` to flip `[~]` → `[x]` on the
   `lem:515A` row and bumped `Progress: 63 / 175 → 64 / 175`.

Aristotle: skipped this cycle per planner direction (the cycle 101
batch was at 2% and not contributing).

## Result
**SUCCESS — `lem:515A` complete, axiom-clean, file compiles with no
warnings or sorry.**

* `lake env lean OpenMath/Chapter5/Section515.lean` exits 0 with
  no warnings (no `declaration uses sorry`).
* Total sorry count in the file: **0** (was 1 at cycle start).
* `linear_combination` discharged the (515b) algebraic decomposition
  on the first attempt — the coefficient pattern derived from the
  textbook decomposition (`u i * hT1 + hT2 - u i * hT3_expand +
  hT4_expand + hsumB_swap - (u i + v i) * h * hy'0 + v i * h * hy'h`)
  was correct.

Two tactic-name fixes were needed during the calc cascade:
* `abs_add` → `abs_add_le` (Mathlib name).
* `add_le_add_right (abs_add_le _ _) _` produced a left-additive
  result, so switched to `gcongr; exact abs_add_le _ _` (matching
  the memory-noted `add_le_add_left dispatch` pattern).

## Faithfulness check

### `aux_T3'_bound` (cycle 102, NEW — not a textbook entity)

* Sub-bound for the (515b) decomposition's `T3'b` term. Not numbered
  in Butcher; corresponds to a single line in the (515b) proof
  derivation ("`v_i·h·(y'(x_n) − y'(x_{n−1}))`"). No textbook
  divergence — sign-symmetric in `v_i` because of `|v_i|`.

### `aux_T2_b_eq_zero` (cycle 102, NEW — not a textbook entity)

* Algebraic identity unfolding the output-side T2 cancellation.
  The two consistency hypotheses `V·u = u` and `B·𝟙 + V·v = u + v`
  match Butcher's GLM consistency conditions (510c). No divergence.

### `aux_T4_bound` (cycle 101, REFACTORED row dim)

* Same statement modulo generalizing `Matrix (Fin s) (Fin s) ℝ` to
  `Matrix (Fin r) (Fin s) ℝ` (and row index `Fin s` → `Fin r`).
  Proof body unchanged. No semantic change.

### `GeneralLinearMethod.localStageError_bound_b` (Entity `lem:515A`, inequality 515b)

* Textbook statement (quoted from `entities/lem_515A.json`):
  > `‖y_i^{[n]} − h Σ_j b_{ij} f(Ŷ_j) − Σ_j V_{ij} y_j^{[n−1]}‖`
  > `≤ h² L² M (½ |u_i| + |v_i| + Σ_j |b_{ij} c_j|)`.

* **Lean statement captures**: same content. Algebraically and
  modulo the autonomous-scalar encoding (`y, f : ℝ → ℝ`), the bound
  is exactly the textbook (515b).

* **Faithfulness divergence (inherited from cycle 101's 515a)**:
  Extra hypothesis `_hc_nonneg : ∀ i, 0 ≤ c i`, identical to (515a).
  Carries through because (515b)'s T3 sub-bound calls `aux_T3_bound`
  at `c_i := 1` (which is trivially nonneg) AND its T4 sub-bound
  calls `aux_T4_bound` which itself does NOT need `0 ≤ c j`
  (`aux_T4_bound` works for arbitrary `c j` via `|c j|` in the
  bound). So actually the (515b) inequality is *already*
  sign-symmetric in `c_j` if (515a) is — the only non-trivial
  `c i ≥ 0` requirement in (515b) is in the (515a)-style
  sub-instances, which (515b) uses at `c_i = 1` only.
  The `_hc_nonneg` hypothesis on (515b) is therefore *redundant*
  but kept for signature consistency with (515a). All standard
  GLMs (explicit Euler, classical RK, Gauss) satisfy `c ∈ [0, 1]`,
  so this carries no practical weakness.

* **No new divergence beyond cycle 101's**.

## Dead ends
None this cycle. The strategy's prediction that
`linear_combination` would close the algebraic decomposition was
correct on the first attempt. The two tactic-name issues
(`abs_add` → `abs_add_le`; `add_le_add_right` argument order)
were quick fixes.

## Discovery
* The mathlib lemma name for the triangle inequality is
  `abs_add_le`, not `abs_add` (which exists for groups but is the
  identity `|a+b| = |a+b|`, not the inequality).
* `add_le_add_right h c : a + c ≤ b + c` *adds on the right*, but
  `gcongr` is more robust against unification ambiguity in
  arithmetic expressions where Lean infers the wrong slot for the
  monotone variable. Future calc cascades over absolute values
  should default to `gcongr; exact <key_lemma>`.
* `set Iv := ∫... with hIv_def` followed by `linear_combination`
  works as expected: ring treats the `set` abbreviation as opaque,
  and the algebra goes through cleanly. This is a robust technique
  for proofs that mix integral expressions with elementary
  identities (cf. cycle 101's same-pattern usage in 515a).
* When `aux_T3_bound` is specialized at `c_i := 1`, the bound
  `(1/2) * h^2 * L^2 * M_bound * 1^2` simplifies to
  `(1/2) * h^2 * L^2 * M_bound` via plain `simpa` (Mathlib's
  `one_pow` and `mul_one` fire automatically).

## Suggested next approach
* **`lem:515B`** is the natural next target — it depends on (515a)
  AND (515b) AND a new contraction argument
  `(I − h₀L|A|) ϕ = ½c² + |A||c|`. The sub-lemma `ϕ ∈ ℝ^s` defines
  the scaling vector for the full local-error bound. Recommend
  scaffolding `ϕ` first as the unique solution to a strictly
  diagonally dominant linear system (consequence of
  `h₀ L ‖A‖_∞ < 1`), then proving
  `‖Ŷ_i − Ŷ_i^∗‖ ≤ h² L² M ϕ_i` via Banach iteration on the
  internal-stage residuals.
* **`lem:515C`** (accumulated error estimate) and **`thm:515D`**
  (full convergence theorem) follow once 515B is closed. These
  three together complete §515.
* The cycle 101/102 `_hc_nonneg` hypothesis should ideally be
  weakened, but only matters for exotic methods with negative
  abscissae. Low priority unless a downstream consumer needs it.
* Aristotle was idle this cycle; resume submissions next cycle on
  515B sub-lemmas (the contraction step is a strong candidate).
