# Cycle 412 Results

## Worked on
CI workflow resilience — `.github/workflows/lean_ci.yml`.

## Approach
The "broken CI" reported by the planner was run 24936678497, which failed with:

```
error: could not download file from 'https://releases.lean-lang.org/lean4/v4.28.0/lean-4.28.0-linux.tar.zst'
info: caused by: http request returned an unsuccessful status code: 502
```

This is a transient HTTP 502 from the upstream Lean releases server while
elan was fetching the toolchain on first invocation of `lean --version`.
There is no source-code error to fix: the Lean tree is healthy (no sorrys,
recent successful runs `24931917855` and earlier all green). The failure is
infrastructure flakiness on a third-party CDN.

The pre-existing retry loop in the workflow only wrapped `lake build`, not
the toolchain download — so a single 502 during `lean --version` killed the
job before retries kicked in.

Fix: added 5-attempt retry loops with 30 s back-off around
1. the `elan-init.sh` install step, and
2. the first `lean --version` / `lake --version` invocation that triggers
   the actual toolchain tarball download.

Also pass `--default-toolchain none` to `elan-init.sh` so that the install
step is purely elan setup; the toolchain fetch happens in the next step
where it can be retried independently.

## Result
SUCCESS — workflow file edited and ready to push. Once pushed, future
transient 502s on `releases.lean-lang.org` will be retried up to 5×
30 s apart instead of failing the whole job on first error.

## Dead ends
None — the diagnosis was straightforward from the run log.

## Discovery
- The CI's existing retry loop on `lake build` was deliberately defensive,
  but the most flaky network step (toolchain download via elan) was
  unprotected. Worth noting for future CI hardening.
- Multiple in-flight pushes from cycles 404–410 are still in progress on
  the runner queue, so the next on-`main` CI run will exercise the new
  retry logic naturally.

## Suggested next approach
Cycle 413: return to the normal LMM convergence-chain agenda
(`plan.md`). Specifically the planner should pick up where cycle 410
left off — Adams–Bashforth 2-step vector convergence is in, so the next
target is likely either AB-3 or the higher-order LMM consistency
infrastructure.
