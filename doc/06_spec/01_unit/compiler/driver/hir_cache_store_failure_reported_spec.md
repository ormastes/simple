# HIR cache failure diagnostics survive scratch reclamation

Manual companion to
`test/01_unit/compiler/driver/hir_cache_store_failure_reported_spec.spl`.
Authored from the executable scenarios; generator and runtime execution UNRUN.

The public cache store must retain the reason for a failed write or rename
after releasing its temporary encoder allocations. These scenarios exercise
real filesystem failures, then create and release another scratch scope before
reading the diagnostic. They require native execution to qualify lifetime
behavior; a source review or interpreter result cannot establish that evidence.

| Scenario | Setup and action | Required observations |
| --- | --- | --- |
| Write failure | Put the cache directory beneath a regular file and store a real fixture module. Allocate and reclaim 32 dynamic strings afterward. | Store returns false; failure count increases once; successful-store count does not change; summary contains `reason=io-write`; I/O classification is true; no temporary cache file remains. |
| Rename failure | Make the final cache path a nonempty directory in a writable cache parent and store a real fixture module. Allocate and reclaim 32 dynamic strings afterward. | Store returns false; failure count increases once; successful-store count does not change; summary contains `reason=io-rename`; I/O classification is true; no temporary file remains; the blocking marker survives. |

Each scenario restores its cache environment and removes its own fixture.
Scratch assertions occur after reclamation so test-report allocations cannot
escape a temporary scope. The fixture's 256-byte accumulated text length checks
that the subsequent scratch workload executed.

The native qualification must retain a before-fix negative control and an
after-fix result using the same admitted runtime and optional instrumentation
settings. This manual records no PASS, measured memory improvement, or closure
of the historical Phase3 worker crashes.
