# Mimalloc TLS registration collision and retained metadata

Status: source fix reviewed; TEST_BLOCKED for native Simple adapter execution.
Base: `6d33ed254d4`. Applies to gc_async_mut, nogc_async_mut, nogc_sync_mut;
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

Reinit removes the previous record; destroy removes instead of tombstoning.
Retention is proportional to live registrations, including callers that fail
to destroy explicitly. Lookup/removal scan live records; array rebuilding and
mutex contention still require measurements. This is not a claim of automatic
thread-exit cleanup, physical memory reclamation, or allocator page release.
Existing mi_heap_delete is a no-op and allocator shims remain outside this fix.

Native acceptance fixtures (one per family) under
`test/fixture/mem_infra/mimalloc_tls_*_lifetime.spl` assert fresh-worker
isolation, positive increasing generations, 1,000 reinitialization/teardown
cycles with exact registry counts, and two concurrent 1,000-cycle workers.
These fixtures have not executed; they must be built with stub fallback
forbidden and run under an admitted native compiler before acceptance.

## Evidence, 2026-09-23

- `git diff --check`: PASS.
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
- Stage 2 capsule `fc2fc3a280ed6afc056ac766a7561a0ba5d6d57038bc8bbb33ea474d9f6a4930`
  was located in the P0 macos-enforced-bd544 evidence. Its receipt lists
  check/test unsupported, and stage-scoped compiler/loader admission is not
  general stdlib test-runner admission. No bootstrap or Rust seed fallback ran.

## Integration and remaining verification

Cherry-pick this lane's commit onto P0 after publication. Execute all three
native fixtures with a qualified producer; measure sequential churn RSS and
warm lookup plus concurrent churn latency. Run the required core/library,
MCP/LSP checks and smoke gates once the self-hosted tooling is admitted.
Until then this is a reviewed candidate fix, not STATUS: PASS or release
evidence. The source snapshot and unrelated active worktrees were preserved.

