# Cycle 403 Results

## Worked on
Added `LMM.discrete_gronwall_geometric` to `OpenMath/LMMTruncationOp.lean`
as the next quantitative local-to-global error infrastructure lemma.

## Approach
Followed the sorry-first workflow:

1. Inserted the requested unrolled-sum discrete Gronwall statement immediately
   after `taylorPolyOf_derivative_eval`.
2. Verified the file compiled with the single planned `sorry`.
3. Submitted a five-job Aristotle batch:
   - `1c0756be-2a2d-4ebf-ba0b-2a2a9717ff9c`:
     `discrete_gronwall_geometric` — `COMPLETE`.
   - `c0eab6ac-635d-48f8-8964-302d004b5bd0`:
     inductive step reshaper — `COMPLETE`.
   - `2848da47-5d5e-43c0-8d06-35e48b9ce6ae`:
     geometric-sum successor identity — `COMPLETE_WITH_ERRORS`.
   - `d218a207-eb98-4f4f-8ff2-e547124cae14`:
     zero-initial-error variant — `COMPLETE`.
   - `cce2b582-aba8-4a04-9619-b51ca946d439`:
     `pow_one_add_nonneg` helper — `COMPLETE`.
4. Slept for 30 minutes and performed one refresh pass over the five jobs.
5. Closed the live proof manually during the wait.

The proof is by induction on `n`. The step multiplies the induction
hypothesis by the nonnegative factor `1 + a`, adds `b`, and rewrites the
forcing term using the theorem-local identity

```lean
(1 + a) * (Finset.range n).sum (fun k => (1 + a) ^ k) + 1
  = (Finset.range (n + 1)).sum (fun k => (1 + a) ^ k)
```

proved from `Finset.sum_range_succ'`, `Finset.mul_sum`, `pow_succ`, and
`ring`.

## Result
SUCCESS.

`OpenMath/LMMTruncationOp.lean` compiles with no warnings:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/LMMTruncationOp.lean
```

`lean_verify` for `LMM.discrete_gronwall_geometric` reports only the
standard axioms `[propext, Classical.choice, Quot.sound]` and no source
warnings.

The optional module build also succeeds:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake build OpenMath.LMMTruncationOp
```

That build replayed pre-existing warnings from `OpenMath.MultistepMethods`;
the modified `LMMTruncationOp` file itself is warning-free.

## Dead ends
The Aristotle headline and step outputs compiled, but they were not
transplanted because they relied on broader geometric-sum lemmas such as
`geom_sum_mul`/`geom_sum_succ` and produced unused-variable warnings in the
submitted standalone files. The local proof is shorter in the live context,
uses the planned unrolled-sum identity directly, and keeps the target file
warning-free.

The Aristotle geometric-sum job returned `COMPLETE_WITH_ERRORS`; its file did
compile after extraction, but the local theorem identity was already proved in
the live proof without needing a separate public helper.

## Discovery
`Finset.sum_range_succ` splits off the last term, while the Gronwall
inductive step is cleaner with `Finset.sum_range_succ'`, which splits off the
zero term and leaves a shifted sum. After rewriting with `Finset.mul_sum`, the
shifted summands close by `pow_succ` and `ring`.

The assumptions `0 ≤ b` and `0 ≤ e 0` are part of the textbook Gronwall
surface but are not needed for this unrolled linear recurrence bound; the live
proof references them only to keep the exact requested API warning-free.

## Suggested next approach
Use `discrete_gronwall_geometric` as the scalar recurrence bootstrap for the
cycle-404+ global error theorem. The next proof step should expose a scalar
error recurrence of the form

```lean
e (n + 1) ≤ (1 + a) * e n + b
```

from the local truncation error estimate and the existing zero-stability /
Dahlquist machinery, without changing the current scalar
`localTruncationError` API.
