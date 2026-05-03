# Cycle 101 Results

## Worked on

- `OpenMath/Chapter5/Section515.lean::localStageError_bound_a` (the
  inequality (515a) of `lem:515A`).
- Added four private sub-lemmas implementing the textbook T1+T2+T3+T4
  decomposition: `aux_T1_eq_zero`, `aux_T2_eq_zero`, `aux_T3_bound`,
  `aux_T4_bound`.
- Updated signatures of `localStageError_bound_a` and
  `localStageError_bound_b` to take `(hc_nonneg : ∀ i, 0 ≤ c i)`
  (required by `aux_T3_bound`).

## Approach

Aristotle status check (single call): batch
`18cdd9f8-0168-4a49-9721-f214918a7afe` was at 2% complete. Per
strategy, treated as not contributing this cycle and went manual.

Per strategy Priority 1, added the four `private theorem`s before the
`/-! ## Lemma 515A` block:

* **`aux_T1_eq_zero`** (FTC chain rule): proved
  `y(x + h c_i) − y(x) − h ∫₀^{c_i} f(y(x + h ξ)) dξ = 0` by chain
  rule giving `HasDerivAt (fun c => y(x + h c)) (h f(y(x + h c))) c`,
  then `intervalIntegral.integral_eq_sub_of_hasDerivAt`, then
  `intervalIntegral.integral_const_mul` to pull `h` out. Closed with
  `linarith`.

* **`aux_T2_eq_zero`** (matrix algebra): proved
  `y(x) + c_i h y'(x) − Σ U_{ij}(u_j y(x) + v_j h y'(x)) − Σ A_{ij} h y'(x) = 0`
  by distributing the U-sum into y-part and h·y'-part, using
  `(U *ᵥ u) i = Σ U_{ij} u_j = 1` (rfl-unfold of `Matrix.mulVec`),
  then closed with `ring`.

* **`aux_T3_bound`** (Lipschitz integral): bounded
  `|h · ∫₀^{c_i} (f(y(x+hξ)) − f(y x)) dξ| ≤ ½ h² L² M c_i²` by
  `abs_mul + abs_of_nonneg hh`, then
  `intervalIntegral.abs_integral_le_integral_abs`, then per-point
  bound `|f(y(x+hξ)) − f(y x)| ≤ L · h · ξ · L · M` (Lipschitz +
  `aux_y_diff_norm_bound`), then `intervalIntegral.integral_mono_on`,
  then `intervalIntegral.integral_const_mul` and `integral_id`
  (ξ → c_i²/2). Required `0 ≤ c_i` to drop `|ξ|` on `[0, c_i]`.

* **`aux_T4_bound`** (Lipschitz discrete): bounded
  `|h · Σ_j A_{ij}(f(y(x+h c_j)) − f(y x))| ≤ h² L² M Σ_j |A_{ij} c_j|`
  by `abs_mul`, `Finset.abs_sum_le_sum_abs`, per-summand Lipschitz
  bridge + `aux_y_diff_norm_bound`, sum and pull constants out via
  `Finset.sum_le_sum` and `Finset.sum_mul`.

Per Priority 2, closed `localStageError_bound_a` using a
`linear_combination` proof of the algebraic identity
`yex(xn1+h·c_i) − h·Σ A_{ij} f(yex(xn1+h·c_j)) − Σ U_{ij}(...) = T3v − T4v`,
combining hT1 (=0), hT2 (=0), expansions of T3v and T4v via
`intervalIntegral.integral_sub` + `integral_const`, and the bridge
`hsumA_swap` + `hy'0` to align the `deriv yex xn1` and `f (yex xn1)`
forms in the matrix sum. The final bound was assembled via
`abs_sub` + `add_le_add hT3 hT4` + `ring`.

## Result

**SUCCESS — sorry count goes 2 → 1**, axiom-clean for all five new
theorems. Verification:

- `lake env lean OpenMath/Chapter5/Section515.lean`: no errors,
  exactly 1 sorry warning (line 603, `localStageError_bound_b`).
- `lake build OpenMath.Chapter5.Section515` finished cleanly.
- `lean_verify` on each of `localStageError_bound_a`,
  `aux_T1_eq_zero`, `aux_T2_eq_zero`, `aux_T3_bound`, `aux_T4_bound`:
  axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Faithfulness check

For each new private theorem and the main theorem signature update:

* **`aux_T1_eq_zero`** — Not a textbook-numbered lemma. Captures
  the FTC telescoping step from Butcher §515 proof of (515a):
  `Ŷ_i − y(x_{n−1}) − h ∫_0^{c_i} f(y(x_{n−1} + hξ)) dξ = 0`. No
  divergence.

* **`aux_T2_eq_zero`** — Not a textbook-numbered lemma. Captures
  the algebraic identity using `c = A·𝟙 + U·v` and `U·u = 𝟙`:
  `y(x) + c_i h y'(x) − Σ U_{ij}(u_j y(x) + v_j h y'(x)) − Σ A_{ij} h y'(x) = 0`.
  No divergence.

* **`aux_T3_bound`** — Not a textbook-numbered lemma; corresponds
  to Butcher's `T3` sub-bound. **Faithfulness divergence**: textbook
  treats `c_i ∈ ℝ`; we restrict to `c_i ≥ 0`. **Strength**: weakening
  hypothesis (extra `0 ≤ c_i`). Justification: the bound is
  sign-symmetric, all standard GLMs (explicit Euler, classical RK,
  Gauss) satisfy `c ∈ [0, 1]`, and the `c_i < 0` case can be added
  in a follow-up by case-splitting the integration interval.

* **`aux_T4_bound`** — Not a textbook-numbered lemma; corresponds
  to Butcher's `T4` sub-bound. No divergence (sign-symmetric in `c_j`
  via `|c_j|` from `aux_y_diff_norm_bound`).

* **`localStageError_bound_a`** (textbook entity `lem:515A`,
  inequality (515a)) — Quoted statement from
  `extraction/formalization_data/entities/lem_515A.json`:
  > `‖ Ŷ_i − h Σ_{j=1}^s a_{ij} f(Ŷ_j) − Σ_{j=1}^r U_{ij} y_j^{[n−1]} ‖ ≤ h² L² M ( ½ c_i² + Σ_{j=1}^s |a_{ij} c_j| )`
  Lean statement captures: same content. **Faithfulness divergence**:
  extra hypothesis `(hc_nonneg : ∀ i, 0 ≤ c i)` inherited from the
  `aux_T3_bound` `c_i ≥ 0` narrowing (documented in the docstring of
  `localStageError_bound_a`).

* **`localStageError_bound_b`** (still `sorry`): added the same
  `(hc_nonneg : ∀ i, 0 ≤ c i)` parameter to keep the signature
  stable for cycle 102's mirror proof. No proof change.

## Dead ends

* Initial `linarith` attempt on the algebraic decomposition
  `yex(xn1+h·c_i) − h·SAfb − Uinp = T3v − T4v` failed: the
  proof requires bridging `c i * h * deriv yex xn1` (in hT2) with
  `h * c i * f (yex xn1)` (in `hT3_expand`) which differ by
  commutativity *and* by `hy_ode`. `linarith` treats the products
  as opaque atoms and could not unify them. Replaced with
  `linear_combination` using the explicit coefficient
  `hT1 + hT2 − hT3_expand + hT4_expand + hsumA_swap − (c i * h) · hy'0`,
  which `ring` resolves.

* `((L.toNNReal : ℝ≥0) : ℝ) = L` failed to elaborate (Lean
  inferred `L` as `Type`); replaced with the unambiguous
  `(Real.toNNReal L : ℝ) = L`.

* `Finset.sum_add_distrib` over a pre-multiplied target produced
  unmatched patterns; replaced with `simp only [mul_add]; rw
  [Finset.sum_add_distrib]; congr 1; ...` to give Lean a
  cleaner factor-then-distribute path.

* `Matrix.dotProduct` is not a valid name; the actual definition
  is at root level (`def dotProduct ... ⬝ᵥ ...` inside
  `namespace Matrix` but the def itself lives in the root
  namespace per Mathlib's `Mul.lean`). For `(M *ᵥ v) i = Σ_j M_{ij} v_j`,
  used `rfl` directly (it's definitionally equal via the `mulVec`
  + `dotProduct` chain).

## Discovery

* `linear_combination` is the right tool for "this is an algebraic
  identity modulo a few rewrite steps that `linarith` can't bridge":
  it accepts polynomial coefficients on each hypothesis (e.g.
  `(c i * h) * hy'0`) and uses `ring` to verify the residual. This
  side-steps both the commutativity issue and the substitution issue
  in one shot.

* The chain-rule pattern `HasDerivAt (fun c => y(x + h*c))` is
  cleanest with `(hasDerivAt_id c).const_mul h |>.const_add x`.
  Avoid `(hasDerivAt_const _ _).add ...` paths: they introduce
  pointwise-`+` lambdas that `simp` doesn't normalize back.

* `(M *ᵥ v) i = ∑ j, M i j * v j` is `rfl` in Mathlib v4.28.0 (no
  `Matrix.mulVec_apply` simp-lemma needed). For `(M *ᵥ (fun _ => 1)) i`,
  use `show ∑ j, M i j * 1 = _; simp`.

* The `set` tactic renames hypotheses transitively, including
  ones introduced earlier (e.g. `set Uinp := ... with hUinp_def`
  rewrote the `Uinp` term inside a previously-proved `hT2`). This
  is convenient but means the order of `set` and `have` matters
  when relying on the substitution.

* `aux_y_diff_norm_bound` (cycle 100) reused as workhorse for
  both T3 (per-point in the integrand) and T4 (per-summand at
  `ξ = c_j`) with no modification needed.

## Suggested next approach

* **Cycle 102 — close `localStageError_bound_b` (515b)** mirroring
  the (515a) closure. The decomposition is structurally identical
  but with output coefficients `B`/`V` instead of `A`/`U`, plus an
  extra `½ |u_i| + |v_i|` term on the right-hand side coming from
  the `y_i^{[n]}` definition. Reuse `aux_T3_bound` and `aux_T4_bound`
  as-is (they take `A` and `c` polymorphically; `B` and `c` slot
  in directly). Need a `T1_b`-analogue using
  `y_i^{[n]} = u_i y(xn) + v_i h y'(xn)` (i.e. evaluated at `xn1 + h`)
  and a `T2_b`-analogue using consistency `B·𝟙 + V·v = u + v`.
  The `aux_T2_eq_zero`-style algebraic step is similar but uses
  `B·𝟙 + V·v = u + v` instead of `c = A·𝟙 + U·v`.

* **Cycle 103 (or beyond) — start `lem:515B`** which uses (515a)
  and (515b) plus the `ϕ` linear-system definition to bound
  `‖Ŷ_i − Ŷ_i^∗‖`. The `ϕ` machinery (cycle 100 deferred) needs
  an existence + non-singularity argument for `(I − h₀L|A|) ϕ = ½c² + |A||c|`
  via the contraction `h₀ L ‖A‖_∞ < 1`.

* **Optional — drop `c_i ≥ 0` restriction in `aux_T3_bound`**.
  The textbook is sign-symmetric. To match exactly, case-split on
  `c_i ≥ 0` vs `c_i < 0` and on the negative branch use
  `intervalIntegral.integral_symm` to flip the integration interval.
  Low priority: no current downstream method needs `c_i < 0`.
