# Mimalloc TLS registration collision and retained metadata

Status: source fix reviewed; TEST_BLOCKED for native Simple adapter execution.
Original candidate base: `6d33ed254d4`; isolated review base: `6b4c4940851`.
Applies to gc_async_mut, nogc_async_mut, nogc_sync_mut;
gc_sync_mut forwards to gc_async_mut.

## Problem and acceptance

REQ-MIMALLOC-TLS-LIFETIME: zero returned by the C TLS provider must never
identify a registered heap. A fresh OS thread must not remove another thread's
heap. Reinitialization replaces the caller's previous record, destroy removes
it, generations never repeat, and every registry transition is synchronized.

The old adapter issues registration zero and recognizes only -1 as absent.
An uninitialized second thread therefore looks up or replaces the first
thread's record. Destroy leaves a placeholder and init always appends; N
sequential lifetimes retain N records and perform quadratic aggregate scans.

## Source repair

Registration generations start at one, clear uses zero, exhaustion fails before
wrap. A process-lifetime raw mutex serializes registry creation, registration,
lookup, removal, and diagnostic count. Initialization failure unlocks before
panic. The module initializer must complete before workers enter the adapter.
The raw i64 TLS ABI remains in `src/lib/nogc_sync_mut/runtime/thread_local.spl`;
the three adapters call its typed facade, so this repair adds no direct runtime
call sites outside that allowlisted provider.

Reinit removes the previous record; destroy removes instead of tombstoning.
Retention is proportional to live registrations, including callers that fail
to destroy explicitly. Lookup/removal scan live records; array rebuilding and
mutex contention still require measurements. This is not a claim of automatic
thread-exit cleanup, physical memory reclamation, or allocator page release.
Existing mi_heap_delete is a no-op and allocator shims remain outside this fix.

Native acceptance fixtures (one per family) under
`test/fixture/mem_infra/mimalloc_tls_*_lifetime.spl` assert fresh-worker
isolation, positive increasing generations, 1,000 reinitialization/teardown
cycles with exact registry counts, and two 1,000-cycle workers with a retained
parent registration. Worker handle and return values must be positive.
These fixtures have not executed; they must be built with stub fallback
forbidden and run under an admitted native compiler before acceptance.

## Evidence, 2026-09-23

- The original candidate's `git diff --check` claim was stale after isolation;
  whitespace was repaired and must be checked on the final staged diff.
- `sh scripts/check/check-runtime-thread-local.shs`: PASS, raw i64,
  isolation, stale handles, capacity, retirement, concurrent free; intentional
  negative control detected.
- `/usr/bin/time -l` for that C provider build plus run: 0.50 seconds wall,
  61,145,088 bytes maximum RSS. This is provider-only build/run evidence, not
  adapter latency, memory, or contention evidence.
- Independent Astra static review found no definite sentinel/generation defect.
  Required follow-up: once-only global mutex initialization/publication, family
  import admission, and actual adapter RSS/latency under native execution.
- One bounded check using the installed release path exited 1: it identifies
  itself as a Rust bootstrap seed and reports no admitted cached self-hosted
  check worker. It supplies no acceptance evidence and was not retried.
- The former Stage 2 capsule `fc2fc3a280ed6afc056ac766a7561a0ba5d6d57038bc8bbb33ea474d9f6a4930`
  and its evidence were deleted before this isolated review. No admitted
  native Simple compiler or test-runner is available in this worktree.

## Integration and remaining verification

Cherry-pick this lane's commit onto P0 after publication. Execute all three
native fixtures with a qualified producer; measure sequential churn RSS and
warm lookup plus concurrent churn latency. Run the required core/library,
MCP/LSP checks and smoke gates once the self-hosted tooling is admitted.
Until then this is a reviewed candidate fix, not STATUS: PASS or release
evidence. The source snapshot and unrelated active worktrees were preserved.
