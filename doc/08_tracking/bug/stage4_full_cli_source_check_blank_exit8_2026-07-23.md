# Stage 4 full CLI fails official source-check with blank exit 8

- **Status:** OPEN / CANDIDATE REJECTED.
- **Source revision:** `f2b493ec656007b1132e284221e1f68f7891e4d8`.
- **Candidate SHA-256:**
  `765acfa3dceac4c7d28d2c8974a224bef4815dfb017fd2a3ca23134e6ebfc503`.
- **Seed sibling SHA-256:**
  `c89358abfecd63d92e7470a46afd167a03e317287d35fe2112555ba816fed6a9`.

## Evidence

The isolated two-thread native build completed in 190.2 seconds with 4 modules
compiled, 1,373 cache hits, and 0 failures. The official layout's adjacent
`simple_seed` makes `simple -c 'print(1+1)'` print `2`.

The next required bootstrap admission command fails silently:

```text
SIMPLE_BINARY=<candidate> <candidate> check src/app/cli/bootstrap_main.spl
exit=8, stdout/stderr empty
```

The candidate was therefore rejected before frontend admission, redeploy, or
essential-tools smoke. An earlier 0/11 redeploy result was invalid evidence
because the manually assembled layout lacked `simple_seed`; it must not be
interpreted as eleven independent compiler regressions.

## Current diagnosis and next step

The staged seed is older than the current extern surface: when invoked directly
it rejects `rt_process_spawn_guarded` and exits 1. Process tracing shows the
candidate then loses the child's stdout/stderr and changes that delegated exit
to 8, implicating `_cli_run_frontend_delegate` / `_cli_process_run` /
`rt_process_run` tuple transport. These are two separate defects; do not remap
exit 8 or promote this binary.

First build or identify a clean current seed so the source-check can understand
current externs. Separately prove candidate delegation fidelity with one bounded
child marker plus nonzero-exit probe, then fix its tuple transport. Re-run the
exact source-check once only after both prerequisites hold.
