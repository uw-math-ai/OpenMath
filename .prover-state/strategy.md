# Cycle 246 Strategy — `thm:319B` Phase 1 (accumulation recurrence)

## A. Target

**`thm:319B` Global truncation error bound via local error accumulation**
(Butcher §319 p. 190; entity record:
`extraction/formalization_data/entities/thm_319B.json`).

Textbook statement (paraphrased; verbatim in JSON):

> Let `h₀` and `L^†` be such that the local truncation error at step
> `k = 1, …, n` is bounded by `δ_k ≤ C h^{p+1}` for `h ≤ h₀`. Then
> the global truncation error is bounded by
>
> ```
> ‖y(xₙ) − yₙ‖ ≤  (exp(L^† (xₙ − x₀)) − 1) / L^†  · C h^p   if L^† > 0
> ‖y(xₙ) − yₙ‖ ≤  (xₙ − x₀) · C h^p                        if L^† = 0
> ```

Textbook proof (Butcher §319 p. 190):
1. From Figure 319(ii), the global error accumulates as
   `‖y(xₙ) − yₙ‖ ≤ C h^{p+1} ∑_{k=1}^{n} (1 + h L^†)^{n−k}`
   (i.e. each local error propagates through the remaining `n − k`
   steps with growth factor `1 + h L^†` per step, by `lem:319A`).
2. For `L^† = 0`: the sum is `n`, and `n h = x − x₀`, giving the bound.
3. For `L^† > 0`: geometric sum
   `∑_{k=1}^n (1+hL^†)^{n−k} = ((1+hL^†)^n − 1)/(h L^†) ≤
    (exp(L^† h n) − 1)/(h L^†) = (exp(L^†(x−x₀)) − 1)/(h L^†)`,
   yielding `C h^p (exp(L^†(x−x₀)) − 1) / L^†`.

## B. Cycle 246 scope: Phase 1 only (accumulation recurrence)

This theorem decomposes cleanly into two phases matching the cycle
244 → 245 split for `lem:319A`:

* **Phase 1 (cycle 246, this cycle)** — define the iterated-step
  trajectory framework, define the per-step local truncation error
  abstractly, and prove the **accumulation recurrence**:
  ```
  ‖yex(n) − traj(n)‖
    ≤ (1 + h L^†)^n · ‖yex(0) − traj(0)‖
      + ∑_{k=0}^{n−1} (1 + h L^†)^{n−1−k} · δ_k
  ```
  by induction on `n`, with the inductive step composing `lem_319A`
  with the triangle inequality. No closed-form `exp` bound yet.

* **Phase 2 (cycle 247, deferred)** — specialise `δ_k ≤ C h^{p+1}` and
  bound the geometric sum by `(exp(L^† n h) − 1)/L^†` to recover the
  headline. Splits cleanly because `(1 + h L^†)^n ≤ exp(h L^† n)`
  requires a real-analysis bound (`Real.add_one_le_exp` and friends)
  that is conceptually orthogonal to the induction skeleton.

The split mirrors `lem:319A`'s cycle 244 (recurrences) → cycle 245
(M-matrix closed-form) pattern. Phase 1 is structural; Phase 2 is
analytic.

## C. File and location

Continue in `OpenMath/Chapter3/Section319.lean` (after cycle 244–245's
work, currently 474 LOC, 0 sorries). Open a new `section Phase3`
inside `namespace OpenMath.Chapter3.Section312.RKTableau` after the
existing `Phase2` section, *before* its closing `end Phase2`.

Imports are already sufficient (the file imports
`OpenMath/Chapter3/Section381`, `OpenMath/Matrix/MMatrix`, and the
relevant Mathlib normed-space machinery). Do **not** add new imports
unless a chosen Mathlib lemma fails to resolve.

## D. Deliverables

### D1 — Iterated trajectory predicate

Define a predicate capturing "`traj : Fin (n + 1) → N` is the sequence
of RK iterates starting from `traj 0`":

```lean
def IsRKTrajectory {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (h : ℝ) {n : ℕ} (traj : Fin (n + 1) → N) : Prop :=
  ∀ k : Fin n,
    M.IsRKOneStep f (traj k.castSucc) h (traj k.succ)
```

Each `Fin n` index `k` represents the step from node `k` to node
`k+1`. The predicate composes with cycle 245's `lem_319A` naturally
via `Fin.castSucc` / `Fin.succ`.

### D2 — Local truncation error bound predicate (abstract)

Rather than introducing a separate "local truncation error" function
(which would require defining the *exact* one-step image of `yex k`
under `f`, an existential), absorb the bound into a hypothesis on
`δ : Fin n → ℝ`:

```lean
/-- `HasLocalTruncationErrorBound M f h yex δ` says that for each step
`k`, there exists an intermediate value `y_step` such that the method
`M` produces `y_step` from `yex k.castSucc` in one step, and
`‖yex k.succ − y_step‖ ≤ δ k`. This is Butcher's Figure 319(ii). -/
def HasLocalTruncationErrorBound {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (h : ℝ) {n : ℕ} (yex : Fin (n + 1) → N)
    (δ : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, ∃ y_step : N,
    M.IsRKOneStep f (yex k.castSucc) h y_step ∧
    ‖yex k.succ - y_step‖ ≤ δ k
```

### D3 — Phase 1 headline: `accumulation_recurrence`

```lean
theorem accumulation_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {h h₀ : ℝ} (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    (h_norm : ‖((h₀ * L) • M.A.map (fun a => |a|))‖ < 1)
    {n : ℕ} {traj yex : Fin (n + 1) → N}
    (h_traj : M.IsRKTrajectory f h traj)
    {δ : Fin n → ℝ} (_hδ_nn : ∀ k, 0 ≤ δ k)
    (h_lte : M.HasLocalTruncationErrorBound f h yex δ) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ‖yex (Fin.last n) - traj (Fin.last n)‖
        ≤ (1 + h * L_dag) ^ n * ‖yex 0 - traj 0‖
          + ∑ k : Fin n, (1 + h * L_dag) ^ (n - 1 - k.val) * δ k
```

**Note on existential**: the `∃ L_dag` mirrors `lem_319A`'s shape
(cycle 245). This is the cleanest interface because `L_dag` is fully
determined by `(M, L, h₀)` but its closed-form
`L * ∑ᵢ |bᵢ| * ((I − h₀ L |A|)⁻¹ 𝟙)ᵢ` is non-trivial to expose;
existential packaging defers that surface.

### D4 — Non-vacuity witness on `paddedEuler`

```lean
example (h h₀ : ℝ) (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    {n : ℕ} (traj yex : Fin (n + 1) → ℝ)
    (h_traj : paddedEuler.IsRKTrajectory (fun y => y) h traj)
    (δ : Fin n → ℝ) (hδ_nn : ∀ k, 0 ≤ δ k)
    (h_lte : paddedEuler.HasLocalTruncationErrorBound
              (fun y => y) h yex δ) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ‖yex (Fin.last n) - traj (Fin.last n)‖
        ≤ (1 + h * L_dag) ^ n * ‖yex 0 - traj 0‖
          + ∑ k : Fin n, (1 + h * L_dag) ^ (n - 1 - k.val) * δ k := by
  /- Reuse cycle 245's D5 paddedEuler smallness witness with f := id. -/
```

The witness reuses cycle 245's D5 example shape: `paddedEuler.A = 0`
⇒ `K = 0` ⇒ `‖K‖ = 0 < 1`, so the M-matrix hypothesis is automatic.

## E. Proof recipe for D3 (accumulation_recurrence)

This is the substantive content. ~80–120 LOC of induction.

### E.1 Extract `L_dag` once at the top

Cycle 245's `lem_319A` (line 279 of Section319.lean) has signature

```
theorem lem_319A {s} (M) {N} [...] {f} {L} (hL) (hf_lip)
    {y₀ z₀} {h h₀} (hh) (hh_le) (hh₀) (h_norm) :
  ∃ L_dag, 0 ≤ L_dag ∧
    ∀ y₁ z₁, M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f z₀ h z₁ →
              ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖
```

Notice `(y₀, z₀)` are **implicit** binders — the existential
captures `L_dag` and the conclusion is universally quantified in
`(y₁, z₁)`. But `(y₀, z₀)` themselves are implicit in the outer
theorem signature, so `L_dag` actually depends on them syntactically
(though not mathematically). **Workaround**: at the use site, when
we want to apply `lem_319A` at multiple `(y₀, z₀)` pairs (one per
step `k`), each application produces a *possibly different* `L_dag`.

**Practical solution**: pass dummy values. Re-derive `L_dag` once at
the start of `accumulation_recurrence` with `y₀ := (0 : N), z₀ := (0 : N)`
(or any fixed pair), then notice that the *body* of `lem_319A` only
uses `(y₀, z₀)` to bind `y₁, z₁` in the contraction conclusion —
the existential `L_dag` and its non-negativity are constructed
independently of `(y₀, z₀)`. So the extracted `L_dag` works
uniformly.

Actually, even simpler: **re-state our own internal `lem_319A`-style
lemma** with `(y₀, z₀)` *universal* in the conclusion. The existing
`lem_319A`'s body (cycle 245) does construct `L_dag` from
`(K, w, b)` only — never touches `(y₀, z₀)` until the final `refine
⟨L_dag, hL_dag_nn, ?_⟩` and the inner `intro y₁ z₁ hY hZ`. So
we can either:

* **Option (a)**: extract `L_dag` once with dummy `(y₀ := 0, z₀ := 0)`
  via `obtain ⟨L_dag, hL_dag_nn, _⟩ := M.lem_319A hL hf_lip hh hh_le hh₀ h_norm`
  (Lean will infer `y₀, z₀ := default`). Then re-invoke `lem_319A`
  inside the induction step with the correct `(y₀, z₀)` to get the
  actual contraction at that step. The two `L_dag`s are *definitionally
  the same* because the existential's choose is built from
  `(K, w, b)` only.

* **Option (b)** (cleaner; recommended): introduce a private helper
  `lem_319A_extract` that produces a *universal* `L_dag`:

  ```lean
  private theorem lem_319A_extract {s} (M) {N} [...] {f} {L} (hL) (hf_lip)
      {h h₀} (hh) (hh_le) (hh₀) (h_norm) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ y₀ z₀ y₁ z₁,
        M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f z₀ h z₁ →
        ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖
  ```

  The proof inlines the cycle 245 body but moves the `intro y₀ z₀`
  inside the final `refine`. ~5 LOC delta from `lem_319A`'s body —
  factor by `apply lem_319A` no, doesn't work because of the
  implicit `{y₀, z₀}` binders. Just copy-paste cycle 245's body
  with one line moved.

**Recommendation**: go with **Option (a)** first. It's a one-liner
at the call site. If the definitional `L_dag`-equality between two
calls turns out to not hold (because Lean's `Classical.choose` is
opaque), fall back to Option (b) — which is a clean ~50-LOC private
helper. Worker should attempt Option (a) for 15 minutes; pivot to
Option (b) if `L_dag` doesn't unify across two `lem_319A` invocations
inside the proof.

Actually, **simplest path** is Option (b) outright. It's a verbatim
re-issue of cycle 245's body with the `(y₀, z₀)` quantifier moved
inside. Worth the ~50 LOC for clarity. **Recommend Option (b)
directly** — skip the gamble on definitional `L_dag` equality.

### E.2 Induction on `n`

```lean
induction n with
| zero =>
  /- Goal: after `refine ⟨L_dag, hL_dag_nn, ?_⟩`,
     ‖yex (Fin.last 0) - traj (Fin.last 0)‖
       ≤ (1 + h L_dag)^0 * ‖yex 0 - traj 0‖
         + ∑ k : Fin 0, _
     LHS = ‖yex 0 - traj 0‖ since Fin.last 0 = 0.
     RHS = 1 * ‖yex 0 - traj 0‖ + 0.
  -/
  simp [Fin.last, pow_zero]
| succ m ih =>
  /- Inductive step. -/
  …
```

#### Base case (`n = 0`)

`Fin.last 0 = 0`, so the LHS is `‖yex 0 - traj 0‖`. The RHS is
`(1 + h L_dag)^0 * ‖yex 0 - traj 0‖ + ∑_{k : Fin 0} … = ‖yex 0 - traj 0‖ + 0`.
Closes by `simp [Fin.last, pow_zero, Finset.sum_empty]` or
explicit `le_refl`.

#### Inductive step (`n = m + 1`)

**Step S1 — restrict the prefix**.
Define the restricted trajectory `yex' traj' : Fin (m + 1) → N` by
composing with the embedding `Fin (m + 1) ↪ Fin (m + 2)` (i.e.
`Fin.castSucc`). The restricted local-truncation-error sequence is
`δ' : Fin m → ℝ`, `δ' k := δ k.castSucc`.

The restricted `IsRKTrajectory` and `HasLocalTruncationErrorBound`
hypotheses are direct restrictions of the originals.

**Step S2 — apply `ih`**.
This gives:
```
‖yex' (Fin.last m) - traj' (Fin.last m)‖
  ≤ (1 + h L_dag)^m * ‖yex' 0 - traj' 0‖
    + ∑ k : Fin m, (1 + h L_dag)^(m-1-k.val) * δ' k
```

Unfold: `yex' 0 = yex (Fin.castSucc 0) = yex 0` (similarly for
`traj`); `yex' (Fin.last m) = yex (Fin.castSucc (Fin.last m)) =
yex ⟨m, by omega⟩` which has Lean-value `m`. Call this `m_in_Fin
m_plus_two`. The key identity:

`Fin.castSucc (Fin.last m) = ⟨m, m.lt_succ_self⟩ : Fin (m + 2)`

This is *NOT* the same as `Fin.last (m+1) = ⟨m+1, …⟩`, but it IS
the predecessor of `Fin.last (m+1)`:

`(Fin.castSucc (Fin.last m)).succ = (Fin.last m).succ = Fin.last (m+1)`

(via `Fin.succ_last` or by direct construction).

**Step S3 — bound the last step via triangle inequality and `lem_319A_extract`**.

Let `M_m := Fin.castSucc (Fin.last m) : Fin (m+2)` (this is the
index pointing to node `m`). By `M_m.succ = Fin.last (m+1)`, the
"last step" of the full trajectory takes us from `traj M_m` to
`traj (Fin.last (m+1))`, witnessed by `h_traj ⟨m, m.lt_succ_self⟩`
(or `h_traj (Fin.last m)` — verify the right index by
unfolding `IsRKTrajectory`).

Extract the local-truncation-error step `k := Fin.last m : Fin (m+1)`:
```
obtain ⟨y_step, h_step, h_diff⟩ := h_lte (Fin.last m)
```
`h_step : M.IsRKOneStep f (yex (Fin.castSucc (Fin.last m))) h y_step`
`h_diff : ‖yex (Fin.last m).succ - y_step‖ ≤ δ (Fin.last m)`

By `Fin.succ_last m`: `(Fin.last m).succ = Fin.last (m+1)`, so
`h_diff : ‖yex (Fin.last (m+1)) - y_step‖ ≤ δ (Fin.last m)`.

Apply `lem_319A_extract`'s contraction property to
`(y₀ := yex M_m, z₀ := traj M_m, y₁ := y_step, z₁ := traj (Fin.last (m+1)))`:
```
‖y_step - traj (Fin.last (m+1))‖
  ≤ (1 + h L_dag) * ‖yex M_m - traj M_m‖
```

Now triangle inequality:
```
‖yex (Fin.last (m+1)) - traj (Fin.last (m+1))‖
  ≤ ‖yex (Fin.last (m+1)) - y_step‖ + ‖y_step - traj (Fin.last (m+1))‖
  ≤ δ (Fin.last m) + (1 + h L_dag) * ‖yex M_m - traj M_m‖
```

**Step S4 — combine with `ih` and rearrange**.

From `ih` at `M_m = Fin.castSucc (Fin.last m)`:
```
‖yex M_m - traj M_m‖
  ≤ (1 + h L_dag)^m * ‖yex 0 - traj 0‖
    + ∑ k : Fin m, (1 + h L_dag)^(m-1-k.val) * δ k.castSucc
```

Multiplying by `(1 + h L_dag) ≥ 0`:
```
(1 + h L_dag) * ‖yex M_m - traj M_m‖
  ≤ (1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
    + ∑ k : Fin m, (1 + h L_dag)^(m-k.val) * δ k.castSucc
```

(using `(1 + h L_dag) * (1 + h L_dag)^(m-1-k.val) = (1 + h L_dag)^(m-k.val)`
when `k.val ≤ m - 1`, which holds because `k : Fin m` implies
`k.val < m`. Use `omega` to discharge `m - 1 - k.val + 1 = m - k.val`.)

Adding `δ (Fin.last m)` to both sides:
```
‖yex (Fin.last (m+1)) - traj (Fin.last (m+1))‖
  ≤ δ (Fin.last m)
    + (1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
    + ∑ k : Fin m, (1 + h L_dag)^(m-k.val) * δ k.castSucc
```

The RHS of the goal at `n = m + 1`:
```
(1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
  + ∑ k : Fin (m+1), (1 + h L_dag)^((m+1)-1-k.val) * δ k
= (1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
  + ∑ k : Fin (m+1), (1 + h L_dag)^(m-k.val) * δ k
```

By `Fin.sum_univ_castSucc`:
```
∑ k : Fin (m+1), (1 + h L_dag)^(m-k.val) * δ k
  = ∑ k : Fin m, (1 + h L_dag)^(m-k.castSucc.val) * δ k.castSucc
    + (1 + h L_dag)^(m-(Fin.last m).val) * δ (Fin.last m)
```

Since `k.castSucc.val = k.val` (definitionally) and
`(Fin.last m).val = m`, so `m - (Fin.last m).val = 0`. The last
term becomes `(1 + h L_dag)^0 * δ (Fin.last m) = δ (Fin.last m)`.

So the RHS reduces to exactly the LHS bound we derived. Close
with `linarith` or explicit `add_le_add` + rewriting.

### E.3 Tactical hints

* `Fin.sum_univ_castSucc` splits `∑ : Fin (m+1)` into `∑ : Fin m` of
  the castSucc'd indices plus the `Fin.last m` term. Reference:
  `Mathlib.Algebra.BigOperators.Fin`.
* `Fin.succ_last`: `(Fin.last m).succ = Fin.last (m+1)`. Verify
  with `lean_local_search "Fin.succ_last"` or check
  `Mathlib.Data.Fin.Basic`. If unavailable by that name, prove
  inline as `by ext; simp [Fin.val_succ, Fin.val_last]`.
* `pow_succ` and `pow_zero` for the `(1 + h L_dag)^n` manipulations.
* `Finset.mul_sum` to pull the outer `(1 + h L_dag)` into the sum.
* `omega` for the `Nat`-subtraction arithmetic
  `m - 1 - k.val + 1 = m - k.val` inside the exponent (given
  `k.val < m`).
* `linarith` or explicit `nlinarith` for the final algebraic
  combine step. `nlinarith` may be needed because the bound
  involves products of non-negative reals; prefer `linarith` after
  explicit calc steps.
* For the destructuring of `HasLocalTruncationErrorBound`:
  `obtain ⟨y_step, h_step, h_diff⟩ := h_lte (Fin.last m)`.
* For `0 ≤ 1 + h * L_dag`: `have : 0 ≤ 1 + h * L_dag :=
  add_nonneg zero_le_one (mul_nonneg hh.le hL_dag_nn)` (or
  `by positivity`).

### E.4 Caveats

* **Index gymnastics**. The `Fin (m+1) → Fin (m+2)` embedding and
  the `Fin.last`/`Fin.castSucc`/`Fin.succ` interactions are subtle.
  Write small `have` blocks proving the key index identities
  (e.g. `(Fin.last m).castSucc = ⟨m, by omega⟩` and
  `(Fin.last m).succ = Fin.last (m+1)`) explicitly, then `rw`/
  `simp` with them.
* **Nat-subtraction inside exponents**. `m - 1 - k.val` is
  Nat-subtraction; if `k.val ≥ m`, it would saturate at 0. Inside
  the proof `k : Fin m` guarantees `k.val < m`, so subtraction is
  well-behaved, but `omega` may need help. Use
  `Nat.sub_add_cancel` after establishing `k.val + 1 ≤ m`.
* **Restricting `IsRKTrajectory` and `HasLocalTruncationErrorBound`**.
  Both are universally quantified over `Fin n`; restricting to
  `Fin m ⊂ Fin (m+1)` should be a one-line `fun k => …`-style
  composition. Be careful with the implicit
  `Fin.castSucc`-coercion of the index argument.

## F. Pre-flight checks (do these first, ~5–10 min)

1. **Verify `lem_319A` extraction works as planned**. Read the
   signature at `OpenMath/Chapter3/Section319.lean:279`. Confirm
   that `(y₀, z₀)` are implicit binders. They are
   (`{y₀ z₀ : N}`), and Lean's `Classical.choose` may not preserve
   definitional equality across two `lem_319A` invocations with
   different implicit `y₀, z₀`. **Recommended**: just write the
   internal helper `lem_319A_extract` (Option (b) above, §E.1) — it's
   a verbatim port of cycle 245's body with one line moved (~50 LOC).
   Saves a potential debugging cycle.

2. **`Fin.succ_last` lookup**. Quick `lean_local_search
   "Fin.succ_last"` or check Mathlib's `Fin.Basic`. Likely
   available; if not, prove inline.

3. **Open scopes**: `open scoped Matrix Matrix.Norms.Frobenius` is
   needed inside `section Phase3` because the `h_norm` hypothesis
   uses the Frobenius scope on a matrix. Mirror cycle 245's
   `section Phase2` opening (line 438).

## G. Anti-recipes (do NOT do)

1. **Do NOT attempt the closed-form `exp` bound this cycle.** Phase
   2 is explicitly deferred. Touching `Real.add_one_le_exp` or
   geometric-sum closed forms would blow the LOC budget.

2. **Do NOT try to compile `OpenMath/Chapter4/Section441.lean`**.
   That file is the documented GPFS-pathology trigger (~43rd
   consecutive timeout per `cycle_182_gpfs_slowness.md`). Section
   319 / 381 / Matrix dependencies compile healthy.

3. **Do NOT introduce a separate "exact one-step image" function**.
   The textbook's Figure 319(ii) framework can be encoded
   abstractly through `HasLocalTruncationErrorBound`'s existential
   `∃ y_step, M.IsRKOneStep … ∧ ‖yex k.succ - y_step‖ ≤ δ k`. This
   is cleaner than defining a non-computable `oneStepImage` function
   that would require its own infrastructure.

4. **Do NOT rename `L_dag` in the existing `lem_319A`**. The
   existential interface is correct; cycle 246 builds on it.

5. **Do NOT add a `(p : ℕ)`-parameter to `accumulation_recurrence`**.
   The order `p` of the method only matters for Phase 2 (where
   `δ_k ≤ C h^{p+1}` is invoked). Phase 1's recurrence is
   order-agnostic.

6. **Do NOT introduce `axiom` or `constant`**. The infrastructure
   needed (`lem_319A` from cycle 245, `Fin` induction lemmas from
   Mathlib) is all in place.

7. **Do NOT touch `IsRKOneStep` or `RKTableau`**. They are stable
   in `Section381.lean` (cycle 202 era).

8. **Do NOT extract `L_dag` from `lem_319A` and rely on
   definitional unification across two calls.** Write
   `lem_319A_extract` per §E.1 Option (b). Saves time vs. debugging
   `Classical.choose`-related goals.

## H. Aristotle batching (optional, low priority this cycle)

The induction is small enough (~80 LOC body) that hand-proving is
preferred. **If** the inductive-step algebraic combine (Step S4)
proves fiddly, a single Aristotle job on the standalone
arithmetic identity

```
∀ (a c : ℝ) (m : ℕ) (g : Fin (m+1) → ℝ), 0 ≤ a → 0 ≤ c →
  c^(m+1) * a + ∑ k : Fin (m+1), c^(m - k.val) * g k
  = c^(m+1) * a + c * ∑ k : Fin m, c^(m - 1 - k.val) * g k.castSucc
    + g (Fin.last m)
```

(or equivalent) could be useful as a side helper. But this is
optional; the recipe is concrete enough to close manually.

Otherwise: no batch this cycle.

## I. Verification checklist (apply at end)

1. `lake env lean OpenMath/Chapter3/Section319.lean` exits 0
   (timeout 10 min — should be much faster).
2. `grep -c sorry OpenMath/Chapter3/Section319.lean` returns 0.
3. `#print axioms
   OpenMath.Chapter3.Section312.RKTableau.accumulation_recurrence`
   returns `[propext, Classical.choice, Quot.sound]` only.
4. `#print axioms` on `IsRKTrajectory` and
   `HasLocalTruncationErrorBound` (definitions; no axioms beyond
   the standard trio).
5. Cycle 244/245 theorems
   (`stage_diff_recurrence`, `output_diff_recurrence`,
   `lem_319A_recurrences`, `lem_319A`) and non-vacuity examples
   (D4 cycle 244, D5 cycle 245) regression-check axiom-clean.
6. Pre-commit faithfulness check (CLAUDE.md):
   * `IsRKTrajectory` — encoding of Butcher's `y_k`-sequence; not
     a textbook-named concept. Document in docstring.
   * `HasLocalTruncationErrorBound` — Butcher's Figure 319(ii)
     local truncation error bound. Faithfulness divergence: the
     textbook defines `δ_k = ‖y(x_k) − ŷ_k‖` as an *equality*; we
     use an *inequality* `‖…‖ ≤ δ k`. This is the right interface
     for accumulation (the *bound* on δ is what propagates).
     Document in docstring.
   * `accumulation_recurrence` — Butcher's intermediate inequality
     "`y(xn) − yn ≤ Chp+1 ∑(1+hL')^k`". Our version is more
     general — it does not pre-specialise `δ_k = C h^{p+1}` and
     ships the corresponding `∑(1+hL†)^{n-1-k} δ_k` bound.
     Phase 2 (cycle 247) will specialise.
   * Faithfulness divergence (smallness): cycle 245's `lem_319A`
     uses Frobenius-norm smallness `‖(h₀ L) • |A|‖_F < 1` instead
     of textbook spectral-radius `h₀ L ρ(|A|) < 1`. Inherited.
     Document in `accumulation_recurrence`'s docstring.
7. Update `extraction/formalization_data/lean_status.json`:
   * `thm:319B` row: `unformalized` → `partial` (Phase 1 only).
   * `lean_file`: `OpenMath/Chapter3/Section319.lean`.
   * `lean_symbol`:
     `OpenMath.Chapter3.Section312.RKTableau.accumulation_recurrence`.
   * `cycle`: 246.
   * `notes`: Phase 1 vs. Phase 2 split, deferral of geometric-sum
     bound, inherited Frobenius-smallness divergence.
8. Update `plan.md`: `thm:319B` row `[ ]` → `[~]` with cycle 246
   closure note.

## J. Task results template

Write `.prover-state/task_results/cycle_246.md` documenting:
* **Worked on**: thm:319B Phase 1 (accumulation recurrence).
* **Approach**: sorry-first scaffold of `IsRKTrajectory`,
  `HasLocalTruncationErrorBound`, `accumulation_recurrence`;
  closure by induction on `n` consuming `lem_319A_extract`.
* **Result**: SUCCESS (axiom-clean) / FAILED (with explanation).
* **Faithfulness check**: per §I.6 above.
* **Discoveries**: any `Fin`/`Nat`-subtraction gotchas, any new
  Mathlib lemmas located.
* **Suggested next**: Phase 2 (cycle 247) — geometric-sum closed
  form yielding the headline `(exp(L^†(x−x₀)) − 1)/L^† · C h^p`
  bound, case-split on `L^† > 0` vs `L^† = 0`.

## K. Backup pivots (only if D3 stalls past 90 min)

If the induction proves harder than expected:

1. **Backup B1 — ship D1, D2, and a *sorry'd skeleton* of D3**.
   Sorry count goes 0 → 1, flagged as Phase 1 scaffold. This
   satisfies CLAUDE.md "minimum: decompose a sorry or write an
   issue" — D1+D2 are real progress and the D3 sorry is one
   focused step from closure. **Do NOT** ship D3 sorry'd without
   the D1/D2 infrastructure also landed.

2. **Backup B2 — pivot to `lem:310B`** (Elementary Differential
   Weight Formula, §310). Pure tree combinatorics consuming cycle
   232+ `elementaryWeight` infrastructure. Single-cycle scope,
   well-isolated from §319. Use only if `accumulation_recurrence`
   induction proves structurally infeasible.

3. **Backup B3 — `thm:443A`** (Order arrows for LMM, §441). NOT a
   viable backup unless GPFS health recovers. Skip if
   `Section441.lean` compile still times out.

Recommended: prefer B1 over B2 to preserve §319 momentum.

## L. Concrete cycle plan (step-by-step)

1. (5 min) Read `lem_319A` signature at line 279; confirm extraction
   strategy (Option (b) recommended).
2. (5 min) Open `section Phase3` block after Phase2's `end Phase2`
   (currently line 409) inside
   `namespace OpenMath.Chapter3.Section312.RKTableau`. Open scopes:
   `open scoped Matrix Matrix.Norms.Frobenius`.
3. (15 min) Write D1 (`IsRKTrajectory`) and D2
   (`HasLocalTruncationErrorBound`) definitions with docstrings.
4. (15 min) Write the internal helper `lem_319A_extract` (§E.1
   Option (b)) by porting cycle 245's body with the `(y₀, z₀)`
   quantifier moved inside the conclusion. ~50 LOC.
5. (10 min) Write D3 sorry-first scaffold: theorem statement +
   `sorry` body, verify it elaborates and the goal type displays as
   expected. Add `obtain ⟨L_dag, hL_dag_nn, h_contract⟩ :=
   M.lem_319A_extract hL hf_lip hh hh_le hh₀ h_norm` + `refine
   ⟨L_dag, hL_dag_nn, ?_⟩` upfront.
6. (45–60 min) Close D3 induction. Base case is one-liner. Inductive
   step is the meat — 60–80 LOC of `Fin.sum_univ_castSucc` +
   `Finset.mul_sum` + `pow_succ` + `omega` + `linarith`.
7. (10 min) Write D4 paddedEuler witness using the cycle 245 `f := id`
   pattern.
8. (10 min) Verification: compile, axiom-check, `grep -c sorry`,
   tautology scanner.
9. (10 min) Faithfulness check (§I.6) + status updates (§I.7, §I.8).
10. (10 min) Task results write-up (§J).
11. (5 min) Commit + push.

Total: ~3 hours of focused work. Within cycle budget.

## M. Cross-references

* `OpenMath/Chapter3/Section319.lean` — file being extended; cycles
  244 (Phase 1 of lem_319A) and 245 (Phase 2 of lem_319A) shipped
  there.
* `extraction/formalization_data/entities/thm_319B.json` — textbook
  statement.
* `extraction/formalization_data/entities/lem_319A.json` —
  prerequisite (axiom-clean per cycle 245).
* `extraction/raw_text/ch03.txt` — §319 paragraphs (search "Figure
  319" or "319B") for the local truncation error definition context.
* `Mathlib.Algebra.BigOperators.Fin` —
  `Fin.sum_univ_castSucc`/`Fin.sum_univ_succ` for the inductive
  step's sum manipulation.
* `Mathlib.Data.Fin.Basic` — `Fin.succ_last`, `Fin.val_last`,
  `Fin.castSucc_lt_last`, etc.
* Cycle 245 task results (`task_results/cycle_245.md`) — recipe
  template and tactical hints for `lem_319A` Phase 2; the §319 work
  pattern is now well-established.

## N. Memory / lesson-of-the-cycle to record

After completion, add to `attempts.md` under cycle 246:
* The Option (b) `lem_319A_extract` pattern (factor out an
  existential-extractor with universal `(y₀, z₀)`) is worth
  remembering for future "use this contraction at many step bases"
  patterns.
* Any `Fin.last`/`Fin.castSucc`/`Fin.succ` interaction lessons.
* Confirm or refute the `Classical.choose` definitional-equality
  concern from §E.1 (would inform future cycles).
