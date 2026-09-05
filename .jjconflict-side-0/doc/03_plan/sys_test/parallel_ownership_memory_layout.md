# Parallel Ownership and Storage Layout System-Test Plan

Current executable scope includes the Wave 0 transfer vocabulary and the first
bounded structured owner/task commit slice. The focused lifecycle SSpec is
`test/03_system/feature/usage/structured_owner_task_lifecycle_spec.spl`.

Future SPipe/system scenarios remain blocked on the corresponding executable
waves and must use real transport, not mocks:

| AC | Scenario | Dependency | Required evidence |
|---|---|---|---|
| AC-4 | child-created output through bounded typed thread transport | WP-13..18 | send/receive/cancel receipt |
| AC-4 | process pointer rejection and encoded/object-ref transfer | WP-13, WP-17 | distinct-process identity proof |
| AC-5 | unknown dynamic index overlap and proven disjoint slice | WP-10..12 | compile diagnostics/MIR facts |
| AC-6 | AoS/SoA transformed view parity and ABI rejection | WP-20..25 | `storage_layout_custom_native_execution_spec.spl` exact-byte/canary evidence; currently blocked before execution by `smf_mmap_native.ptr_read_u8` native codegen |
| AC-7 | MDSOC port route with bypass sabotage | WP-30 | route receipt and deliberate bypass failure |
| AC-8 | reverse child completion with canonical parent commit | WP-15 first slice | ordered task receipt and replay rejection |

When these scenarios become executable, create mirrored `test/03_system/...`
SSpec and `doc/06_spec/...` manual artifacts; do not add a passing placeholder
before a real runtime boundary exists.

## Bounded transport provider matrix (2026-08-12)

The focused unit evidence is now
`test/01_unit/common/structural/parallel_transport_provider_matrix_spec.spl`
with the mirrored manual
`doc/06_spec/01_unit/common/structural/parallel_transport_provider_matrix_spec.md`.
It reuses the current pure-Simple owners rather than introducing a second
provider model:

| Matrix row | Current owner/evidence | Status and claim boundary |
|---|---|---|
| capacity+1/backpressure | `GreenChannel`; Rust `concurrent_providers_test.rs` | pure-Simple executable; Rust source-bound until admitted native runner |
| close drains then CLOSED | `GreenChannel.close_drain` and `green_channel_recv` | pure-Simple executable |
| cancellation wakes waiters | `GreenChannel.close_drain` | pure-Simple executable logical scheduler state |
| typed mutable rejection | `admit_dynamic_transport`; native provider test | source-bound; no native/live claim |
| forged/stale/replay capability | `ObjectHandleCapabilityRegistryV1` | pure-Simple executable owner registry |
| scalar/value-channel close and bound | `runtime_native.c`, `value/channels.rs` focused tests | source-bound; no native/live claim |

The native rows must be promoted only by an admitted self-hosted native
provider run. The matrix intentionally does not describe source inspection as
process, native, or device transport evidence.

The single focused interpreter attempt on 2026-08-12 was blocked before the
scenario loaded: the available `bin/simple` identifies itself as a Rust
bootstrap seed and failed repository compilation at
`src/compiler/50.mir/verification_ir.spl` (`Unexpected token: expected Fn,
found For`). This is not a matrix PASS and was not retried.

## Structured lifecycle evidence (2026-08-12)

The focused SSpec exercises real common state transitions and the runtime task
adapter without mocks:

| Scenario | Required evidence |
|---|---|
| capacity+1 and exact-capacity map | overflow leaves zero reservations; exact map joins |
| cancellation | publication lease revoked; handle drained; owner unchanged |
| child failure | explicit failure wire and owner-visible failure notification |
| channel reuse | 80 sequential task groups exceed/reuse the 64-slot native registry |
| actor result | same wire record through capacity-one `ActorMailbox` |
| reverse completion | canonical task-ID ordering and stale replay rejection |
| conflict and apply error | deterministic rejection and unchanged owner digest/values |

Process, physical cancellation, and runtime trap-catching evidence remain
separate prerequisites. The actor row covers the bounded same-runtime mailbox
adapter; it is not an OS-thread or process-isolation claim.

The single lifecycle SSpec attempt on 2026-08-12 did not reach the scenario:
the current `bin/simple` reported that it is a Rust bootstrap seed and failed
on pre-existing `src/compiler/50.mir/verification_ir.spl` parsing
(`Unexpected token: expected Fn, found Var`). It was not retried. Execution
requires an admitted pure-Simple self-hosted binary that compiles the tree.
