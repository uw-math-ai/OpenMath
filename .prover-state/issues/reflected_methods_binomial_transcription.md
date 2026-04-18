# Issue: reflected-method binomial proof transcription

## Blocker
The core reflected-method transfer proofs for Theorem 343B are mathematically straightforward, but
the local transcription into `OpenMath/ReflectedMethods.lean` is stalling on nested finite-sum
rewrites and binomial-expansion normalization, not on the underlying argument.

## Context
Current source status:
- `OpenMath/ReflectedMethods.lean` compiles with 4 focused `sorry`s:
  - `reflect_satisfiesB`
  - `reflect_satisfiesC`
  - `reflect_satisfiesD`
  - `reflect_satisfiesE`
- The file already contains the reflected tableau definition and the easy theorems
  (`reflect_reflect`, `reflect_rowSum`, `reflect_consistent`, Euler reflection).

Scratch discovery:
- In `lean_run_code`, the following helper lemmas *do* prove:
  1. `∑ m in range (n+1), (-1)^m * choose n m / (m+1) = 1 / (n+1)`
  2. `∑ m in range (n+1), (-1)^m * choose n m * (x^(m+1)/(m+1)) = (1 - (1-x)^(n+1)) / (n+1)`
- Using those, I also got scratch proofs for `reflect_satisfiesB` and `reflect_satisfiesC`,
  and the same pattern should handle `reflect_satisfiesD`.

## What was tried
- Direct transcription of the scratch proofs into `OpenMath/ReflectedMethods.lean`.
- Switching between `∑ m in ...` notation and explicit `Finset.sum`.
- Expanding `(1 - x)^n` via `add_pow` with `1 + (-x)`.
- Reorganizing the `C` and `D` proofs with `calc`, `sum_comm`, `mul_sum`, and `sum_sub_distrib`.

## Possible solutions
- Reintroduce the helper lemmas first, in isolation, as explicit `Finset.sum` equalities. Once they
  compile in the file, layer the `B/C/D` proofs on top of them.
- Use the exact scratch proofs as the starting point, but normalize every nested sum through
  explicit `Finset.sum` terms instead of pretty `∑ m in ...` notation.
- If the arithmetic normal forms still fight `simp`, try small intermediary helper lemmas for:
  - `t.b i * ((1 : ℝ) ^ a * (-x)^m * c) = t.b i * ((-1)^m * x^m * c)`
  - splitting `(u - v) * w` inside sums before applying `sum_sub_distrib`
- Leave `reflect_satisfiesE` for Aristotle even after `B/C/D` are done; the current best local
  route is still to close only `B/C/D` manually.
