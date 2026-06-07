# SMF Runtime-Pool Closure Lookup Blocker

## Summary

SMF multicore-green workloads can resolve
`multicore_green_set_parallelism` / `multicore_green_parallelism`, but native
runtime-pool worker threads cannot look up the submitted SMF worker function.
The run prints `function not found: worker` from `rt_interp_call` and exits by
segfault.

## Evidence

```text
multicore_green_parallelism = 64/64
rt_interp_call: function not found: worker
Segmentation fault
```

## Impact

SMF multicore-green rows must be classified as
`SMF runtime-pool closure lookup blocker` and must not be used as Go-like M:N
evidence. Native multicore-green rows remain the hosted evidence path and still
must provide `pool_used=N/N` plus `parallelism=requested/actual`.

## Required Fix

Make SMF runtime-pool worker threads resolve submitted closure entry functions
from the SMF module context, or reject the pool submission before worker threads
start so the Simple facade can fall back without crashing.
