# Reserved process observation V4 — E3

Source base c5a0200393c. This is containment E3 after E1/E2, not a new retry budget. Source authored; native controls, Simple facade specs and consumer qualification NOT_RUN. No overall HIR/tool-broker completion claim.

## Authority and lifecycle

The canonical process owner reserves one of 16 slots before any spawn. A positive monotonic scalar token identifies that reservation generation, never a PID. Exhaustion refuses; counter overflow refuses rather than reusing authority. The Simple reservation retains executable/cwd pin objects. The caller retains the reservation before calling start and closes pins only after successful confirmation; failed pin closes remain retryable on their original objects.

States are exported as READY=1, ATTEMPTING=2, NO_CHILD=3, OWNED=4, ACKED=5 constants. State inspection can return busy/error; a negative is never no-child evidence. One attempt is irrevocable even if it fails. The request digest and pin identities are bound before spawn; repeated or concurrent starts refuse. Underlying V4 slot association is installed before child creation and legacy ticket lookup cannot access reserved slots. This is process-local trusted API authority, not a sandbox against arbitrary foreign code in the same address space.

Scalar start returns1 for retained child authority and0 for definitive no-child. NULL observation or malformed receipt preserves authority. Observe optionally requests retirement and freezes terminal capture through existing V4 collection. No-child/unused reservations require no fabricated observation/ack: confirm directly. Every decoded observation and acknowledgement verifies its request/ticket identity against the native reservation through a scalar predicate. The decoder remains authoritative for packet invariants.

Ack preserves exact frozen owner state and can replay after allocation/decoding failure. A wrong digest refuses without changing ownership. Explicit scalar confirmation frees both bounded slots only after no-child or terminal acknowledgement; the Simple owner additionally requires successful Ack/CleanupAck decoding. Repeated confirmation on the same released Simple object succeeds locally; stale native tokens refuse and cannot touch a replacement. Unconfirmed reservations consume bounded capacity rather than creating unbounded tombstones. The provider does not promise to recover from process termination or malicious mutation of private owner fields.

## ABI and support

Canonical declarations live in process_ops.spl, native declarations in runtime.h; runtime_process_owned.c includes runtime_process_observation_reserved_v4_impl.h. Functions: reserve_value, reserved_state_value, reserved_start_pinned_value, reserved_observe_value, reserved_ack_value, reserved_matches_value, reserved_confirm_release_value, all under rt_process_observation_v4_. Observe/ack are nullable tuples. Native host admission follows existing V4 capabilities (Linux leader-only; Darwin admitted leader/group policies, no unsupported memory-cap claims). Other hosts return unsupported; Rust interpreter registration explicitly refuses new reserved operations. Rust codegen maps are ABI bookkeeping, not interpreter qualification.

## Compatibility limitation

Old public start/ack APIs are unchanged and retain the documented decode-loss risk. Exact release caller inventory: app/build/scheduler/dist_exec_worker.spl90; parallel_transport_process_session_v1.spl231; lib/nogc_async_mut/container/providers/linux/oci_exact_logs_v1.spl229; lib/nogc_sync_mut/sosix/memory_executable_v1.spl43/47. Their migrations remain open; adding this API does not repair all canonical callers. The current HIR adapter migration is owned by lsp_revision_review and must retain reservation before start. Generic external-tool brokerage remains separate and open.

## Focused controls

Native harness src/runtime/test/runtime_process_observation_reserved_v4_darwin_selfcheck.c reuses the existing executable snapshot fixture but runs only new controls: real child, lost initial postspawn tuple publication with retained scalar authority, concurrent duplicate launch, changed-request refusal, deliberately malformed postspawn packet, exact/mismatched identity, retryable pre-consumption collection, wrong-digest refusal, malformed Ack/replay, stale generation, bounded reservation exhaustion, no-child release and FD/slot retirement. Compile-time-only injection hooks are absent from production; no environment knob. C corruption does not execute the Simple decoder, and FD/slot checks are not whole-heap qualification. Actual Simple decode-failure persistence and HIR consumer tests remain required.

The harness contains an exact compile invocation and requires an external30-second process-tree watchdog. Child leak backstop is5seconds. Only one finite child is launched, with two short concurrent start callers; no compiler/build execution is authorized by this document. Coordinator must admit the native slot before compiling/running. No checks were rerun or marked PASS here.
