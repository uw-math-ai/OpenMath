# Cycle 004 Results

## Worked on
`thm:123B` — Area invariance for Hamiltonian parallelograms (Butcher §123).

New file: `OpenMath/Chapter1/Section123.lean`. Introduces:
- `HamiltonianVar2D` (structure bundling the four scalar component
  ODEs `v' = J W v` for the 2-D Hamiltonian variational equation).
- `area` (the explicit symplectic form `u₁ x * v₂ x - u₂ x * v₁ x`).
- `area_const` (theorem: this symplectic area has zero derivative
  along any pair of perturbations satisfying the variational
  equation).

Wired the new module into `OpenMath/Chapter1.lean`. (`OpenMath.lean`
only re-exports `OpenMath.Chapter1`, no edit needed there.)

## Approach
1. Read `extraction/formalization_data/entities/thm_123B.json` to
   anchor the Lean statement against `statement_latex`/`context_latex`.
2. Sorry-first file mirroring the cycle-003 `KeplerSystem` pattern —
   four scalar component ODEs in a `Prop`-only structure, scalar
   `area : ℝ → ℝ`, `HasDerivAt … 0` conclusion. Verified
   `lake env lean OpenMath/Chapter1/Section123.lean` compiles
   sorry-only.
3. Submitted the sorry-first file to Aristotle
   (`mcp__aristotle__submit_file`, project
   `e8b1d17b-d312-4206-8943-0f960dbc93e9`). Slept 30 minutes per the
   strategy, then refreshed/extracted once.
4. Aristotle returned `COMPLETE` with the chain-rule + `ring` proof
   that the strategy predicted. Pasted the proof body in (preserving
   the docstring Aristotle had silently downgraded to a regular
   comment).
5. Verified the final file compiles individually, then ran
   `lake build OpenMath` end-to-end — "Build completed successfully
   (2224 jobs)", zero errors, zero warnings.

## Result
SUCCESS — `area_const` is fully proved with no `sorry`. Build clean.
Aristotle handled the `HasDerivAt` chain-rule expansion + polynomial
cancellation in one shot (no manual fallback needed).

Aristotle's proof body verbatim:

```lean
unfold area
intro x
have h_du := (h.d_u₁ x).mul (h.d_v₂ x)
have h_dv := (h.d_u₂ x).mul (h.d_v₁ x)
convert (h_du.sub h_dv) using 1
ring
```

## Faithfulness check

### `HamiltonianVar2D` (structure)

Quoted `statement_latex`:

> In the special case of a two-dimensional Hamiltonian problem, the
> value of \( ( \mathbf{u} )^{\top} J ( \mathbf{v} ) \) can be
> interpreted as the area of the infinitesimal parallelogram with
> sides in the directions \( \mathbf{u} \) and \( \mathbf{v} \). As
> the solution evolves, \( \mathbf{u} \) and \( \mathbf{v} \) might
> change, but the area \( \mathbf{u}^{\top} J \mathbf{v} \) remains
> invariant.

Quoted `context_latex`:

> The theorem concerns a Hamiltonian system $y' = J\nabla H(y)$.
> Perturbations $u$ and $v$ to the initial condition evolve according
> to $v'(x) = JW(y)v(x)$, where $W$ is the Hessian of $H$. […]
> $J$: the $2N \times 2N$ matrix $\begin{bmatrix}0 & -I \\ I & 0
> \end{bmatrix}$ […] $W$: the Wronskian matrix with $(i, j)$ element
> $\partial^2 H/\partial y_i \partial y_j$.

The Lean structure is the explicit 2-D ($N=1$) instance of
`v' = J W v` with `J = [[0, -1], [1, 0]]`. Expanding:

```
v' = [[0, -1], [1, 0]] · [[W₁₁, W₁₂], [W₁₂, W₂₂]] · v
   = [[-W₁₂, -W₂₂], [W₁₁, W₁₂]] · v
   = (-W₁₂ v₁ - W₂₂ v₂, W₁₁ v₁ + W₁₂ v₂)
```

…which matches the four ODE fields (`u` and `v` are independent
solutions, each obeying the same equation):

- `d_u₁`: `u₁' = -(W₁₂ u₁ + W₂₂ u₂)` ✓
- `d_u₂`: `u₂' =  W₁₁ u₁ + W₁₂ u₂` ✓
- `d_v₁`: `v₁' = -(W₁₂ v₁ + W₂₂ v₂)` ✓
- `d_v₂`: `v₂' =  W₁₁ v₁ + W₁₂ v₂` ✓

**Design choice — collapsing `W₁₂`/`W₂₁` into one field.** The Hessian
of a smooth Hamiltonian is symmetric (`∂²H/∂y₁∂y₂ = ∂²H/∂y₂∂y₁`), so
the (1,2) and (2,1) entries of `W` are equal. Encoding them as one
shared scalar function `W₁₂ : ℝ → ℝ` (rather than two functions plus
a separate `W₁₂ = W₂₁` hypothesis field) keeps the structure minimal
and faithful. **Lean statement captures: same content as the
textbook**.

**Higher-dimensional case.** Butcher's `thm:123B` claim of *area*
invariance is explicitly restricted to the 2-D case. The general-N
"Hamiltonian volume" claim is `thm:123A`, deferred to a later cycle.
We do *not* claim it here.

All four ODE fields are *hypotheses* (no conclusion fields). No
extra `IsSymm`/`Differentiable`/smoothness hypotheses on `W`.

Tautology / identity / definition-smuggling / hypothesis-strength
checks: passed.

### `area` (def)

- Entity ID: `thm:123B` (the theorem itself; `area` is the supporting
  definition for the symplectic form).
- Textbook formula: `uᵀ J v = u₁ v₂ - u₂ v₁` (with
  `J = [[0, -1], [1, 0]]`).
- Lean term: `u₁ x * v₂ x - u₂ x * v₁ x`.
- Lean statement captures: **same content** — term-for-term match.
  No `Matrix.det`, no `BilinForm`, no `SymplecticForm` abstraction.

### `area_const` (theorem)

- Entity ID: `thm:123B`.
- Textbook claim: the area `uᵀ J v` "remains invariant" along
  evolutions of the variational system.
- Lean statement: `∀ x, HasDerivAt (area u₁ u₂ v₁ v₂) 0 x`
  (i.e. the derivative of the area is zero everywhere — the standard
  Lean way to state "constant along the trajectory" without choosing
  a particular value).
- Lean statement captures: **same content**. Equivalent to "constant"
  for any continuous `area`, which holds here via the four
  `HasDerivAt` hypotheses.
- Tautology check: conclusion `HasDerivAt (area …) 0 x` does not
  appear among the hypotheses ✓.
- Identity check: proof is genuine chain-rule + `ring`, not
  `exact h.field` ✓.
- Hypothesis-strength check: only `HamiltonianVar2D u₁ u₂ v₁ v₂ W₁₁
  W₁₂ W₂₂` is required — no extras ✓.
- Absent-theorem check: no TODO comments promising future content ✓.

## Dead ends
None. Aristotle one-shot the proof on the first submission, exactly
as the strategy predicted; the manual fallback was not needed.

## Discovery
- Aristotle's recipe for "differentiate a polynomial of derivable
  scalar functions, then cancel by `ring`" continues to be reliable
  on Butcher-style conservation theorems. Cycle 003 (Kepler `H` and
  `A`) and cycle 004 (Hamiltonian area) all closed with a
  `convert … using 1; ring` shape after batch-applying
  `HasDerivAt.mul`/`HasDerivAt.add`/`HasDerivAt.sub`.
- One papercut: Aristotle silently changed the docstring `/-- … -/`
  in `area_const` to a non-doc `/- … -/`. Easy to catch by diffing
  against the sorry-first file, but worth noting for future cycles —
  always preserve the original docstring when pasting back.
- The strategy's "sign-placement sanity check" (negative on
  `d_u₁`/`d_v₁`, positive on `d_u₂`/`d_v₂`, because of the
  `J = [[0, -I], [I, 0]]` convention) was correct on the first try.
  No sign-flip debugging needed.

## Suggested next approach

The cycle 005 planner has a couple of natural follow-ups, in
descending order of attractiveness:

1. **`thm:142D` (Jordan canonical form ⇒ convergence/power-bounded
   characterisation)** — next in plan order. Heavy. Cycle 005 should
   probably scope it as "investigate Mathlib's Jordan-form story
   (`Matrix.toEuclideanLin`/`Matrix.IsHermitian` / spectral theorem
   ecosystem) and produce a sorry-first scaffolding only", since it
   needs eigenvalue/eigenvector machinery the prior cycles haven't
   exercised.
2. **`thm:112B` (one-sided Lipschitz ⇒ solution-difference bound)** —
   still a cleaner "low-risk" alternative if `thm:142D`'s Mathlib
   search turns up dry. Needs `def:112A` (✓ from cycle 002) +
   `gronwallBound`/`norm_inner_le_norm` from Mathlib + a
   `HasDerivAt` computation on `‖y₁ - y₂‖²`.
3. **`thm:123A` (general-N Hamiltonian conservation)** — *not*
   started this cycle (the cycle-004 strategy marked it stretch-only
   and we did not have time/quota for the stretch). It is the natural
   sequel to `thm:123B` once the planner wants more §12x coverage.
   Note the infrastructure gap flagged below.

### Infrastructure gap noted (for future Hamiltonian-N cycles)

When `thm:123A` is attempted, the Lean side will need a "standard
symplectic matrix" `J : Matrix (Fin (2*N)) (Fin (2*N)) ℝ`. As of
this cycle I have not searched Mathlib for it; the planner should
budget 1–2 search rounds (`lean_loogle`,
`lean_leansearch "symplectic matrix"`) before scaffolding, and be
prepared to define it locally if Mathlib lacks a clean definition.
This is a note, not an issue file — there is no current blocker,
just a sign-post.
