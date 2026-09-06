# KPF Long-Run No-Allocation and Capacity Evidence

**Date:** 2026-09-03  
**Scope:** `REQ-KPF-005` focused long-run product-path evidence for the fixed noalloc KPF projection.

## What changed

The `std.nogc_async_mut_noalloc.kernel_plugin.KpfFixedRuntime` evidence model now
retains:

- allocator-counter evidence after activation;
- session-table and request-table high-water marks;
- exact session-capacity and request-capacity exhaustion counters;
- cancellation and drain counts for outstanding per-session requests;
- leak and fragmentation indicators at the end of the retained workload window.

The representative workload is exercised by
`test/01_unit/lib/nogc_async_mut_noalloc/kernel_plugin/fixed_runtime_spec.spl`
through `run_representative_workload(32, 2)` and a stricter 64-iteration
mutation guard. The workload opens an activated session, completes one request,
cancels one request, re-fills to the per-session limit, forces `WouldBlock`,
opens a second session to the table high-water, forces an exact
`CapacityExceeded`, drains the outstanding requests, and closes back to the
activation baseline on every iteration.

## Expected retained evidence

For the current fixed configuration (`arena=96`, `sessions=2`, `max_inflight=2`,
`request_table=2`, `persistent=8`, `session_bytes=16`, `request_bytes=4`), the
executable spec asserts:

| Measure | Expected value |
|---|---:|
| iterations | 32 |
| opened sessions | 32 |
| completed requests | 32 |
| cancelled requests | 32 |
| drained requests | 64 |
| session capacity exhaustions | 32 |
| request capacity exhaustions | 0 |
| per-session backpressure events | 32 |
| session table high-water | 2 |
| request table high-water | 2 |
| arena high-water | 48 bytes |
| arena live after drain | 8 bytes |
| leak bytes after drain | 0 bytes |
| fragmentation bytes | 0 bytes |
| post-activation allocations | 0 |
| allocation proof status | `Clean` |

The companion drain test additionally proves `close_session` stays blocked while
requests are live, `drain_session` cancels exactly the outstanding requests, and
arena accounting returns from `24` bytes to the `8`-byte activation baseline.

## Mutation sensitivity

`scripts/check/kernel-plugin-fabric/check-strict-noalloc-proof.shs` now rejects
missing long-run workload, missing capacity/drain/leak assertions, and missing
strict zero-allocation assertions.

`test/01_unit/lib/nogc_async_mut_noalloc/kernel_plugin/strict_noalloc_proof_contract_test.shs`
keeps two fail-closed mutations:

1. disable the allocator delta check in `allocation_probe.spl`;
2. weaken the long-run spec by replacing the strict `0` allocation assertion.

Both mutations must fail the checker.

## Execution status in this worktree

Source-level gates passed:

- `sh scripts/check/kernel-plugin-fabric/check-strict-noalloc-proof.shs .`
- `sh scripts/audit/direct-env-runtime-guard.shs --working`
- `sh scripts/audit/direct-env-runtime-guard.shs --staged`

Executable SPipe rerun is currently blocked in this isolated worktree because
`bin/release/simple` fails its bounded identity probe and `bin/simple-interp`
cannot locate an admitted runtime under `bin/`. No Rust-seed fallback was used.
