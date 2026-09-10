# Slang KV Page Manager Specification

> Owner-authoritative admission, identity, reference, prefix, and copy-on-write
> behavior for the bounded paged-KV state machine.

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 19 | 19 | 0 | 0 |

**Requirements:** `doc/02_requirements/feature/slang_paged_kv_backend.md`  
**Plan:** `doc/03_plan/agent_tasks/slang_paged_kv_backend.md`  
**Design:** `doc/05_design/ml/slang_paged_kv_backend.md`  
**Research:** `doc/01_research/local/slang_paged_kv_backend.md`

## Overview

The page manager is the logical owner of page and request state. Provider
handles are opaque payloads; callers cannot publish pages, mutate shared tails,
or reclaim live storage without a successful owner transition.

## Scenarios

### Admission and identity

- Invalid pool geometry is rejected before state allocation.
- Page and byte limits are enforced before reservation.
- Aborted pages invalidate stale generation-safe identities.
- Reclaimed provider handles remain queued until explicitly acknowledged or
  drained.

### Request ownership

- Security namespaces cannot attach each other's pages.
- Duplicate page references and over-capacity block tables are rejected.
- Closed request handles are invalid immediately.
- A request has at most one private writable tail.
- Appends cannot exceed the configured page-row bound.
- A sealed tail requires copy-on-write before further mutation.

### Copy-on-write publication

- A verified partial-tail copy atomically replaces the old sealed tail.
- Copy plus decoded rows can publish as one owner transition.
- Arithmetic overflow is rejected without consuming the reservation.
- Hash mismatch leaves the source authoritative and permits explicit abort.
- Boundary recomputation can retain a shorter verified prefix of the tail.
- Cancellation releases the request-bound reservation and destination page.

### Prefix cache

- Prefix identity includes exact tokens; a matching hash alone is insufficient.
- Published prefix pages are immutable and forked through references.
- Attachment requires a live, empty request in the same namespace.
- Lookup selects the longest exact stored prefix.
- LRU eviction is deterministic and never reclaims pinned live pages.
- An impossible limit shrink fails atomically.

### Telemetry

- Allocated pages, live references, prefix hits/misses, evictions, active
  reservations, and high-water marks reflect committed owner state.

## Expected failures

The suite asserts typed `KvPageError` values for invalid configuration, pool
exhaustion, wrong namespace, invalid/stale handles, invalid transitions, busy
requests, table overflow, invalid occupied rows, required COW, and hash
mismatch. No failure path is accepted through a placeholder assertion.

## Reproduction

Executable source:
`test/01_unit/lib/gc_async_mut/slang/core/page_manager_spec.spl`.

Run with an admitted pure-Simple runtime:

```text
simple test test/01_unit/lib/gc_async_mut/slang/core/page_manager_spec.spl
```

This manual describes the logical owner state machine. It does not claim real
tensor paging, model-output parity, or a performance improvement.
