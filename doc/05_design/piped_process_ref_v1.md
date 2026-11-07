# Canonical piped process generation reference V1

Status: **AWAITING_VERIFICATION**. Base 5149a588e1261794d77d1c416a01628253686759,
branch `work/piped-generation-owner-20261107`. Root/Astra/Caret/Podman agreed the
Ref stream surface plus registry-only validation. No builds or test execution are claimed here.

## Owner and contract

PPIPE-01: `PipedProcessRefV1 {pid: i64, generation: i64}` is process-local trusted
metadata over the existing runtime_process.c registry, not remote authority,
persistent identity or restart recovery. Copying it does not create another
reader. Caret remains its pane stream's sole reader; Podman retains its process
reference. Existing legacy PID APIs remain adapters over the same registry.

PPIPE-02: `process_spawn_piped_ref_v1(cmd, args)` requires an absolute executable
and at most 64 arguments (command excluded). It rejects empty commands, original
and translated command NUL, argument NUL, and relative paths before effects.
Only host path spelling translation occurs; no PATH/tool/script resolver picks a
different program. Windows absolute paths use the existing host-path owner,
which rejects drive-relative paths and accepts drive-absolute/UNC forms.
Canonical counted UTF-8 bytes (`str_len`, `boxed_text_bytes_checked`) provide byte
lengths/NUL admission; text character count is not used for offsets. Native spawn
rechecks counted command/argument bytes and 64 limit before slot reservation.
The 64 bound is new to Ref; the legacy piped API's argument policy is unchanged.

PPIPE-03: every actual read/write/state/liveness/close/validation operation validates both
fields under the same registry critical section. Exact lookup scans both fields
across all slots. The selected slot pointer goes directly into the shared reader
or writer; no second PID-only lookup can select an earlier retained generation
with a reused PID. No descriptor or registry pointer escapes the action lock.
TLS text buffers retain the existing provider lifetime/copy convention.

PPIPE-04: `process_read_stdout_ref_v1` returns `Ok(Some(chunk))` for framed text,
`Ok(nil)` for deferred/no complete text, and `Err("process_stdout_eof")` only for
observed EOF with the UTF-8 tail drained. A nonempty read returns immediately.
An empty read queries state for the same exact reference. Close between these
calls may yield stale, never data from a successor. Liveness false is not EOF.
Partial write offsets/progress/max_bytes are UTF-8 bytes; zero is backpressure.
No implicit retry or transfer of sole reader ownership occurs in the facade.
`process_validate_piped_ref_v1` (and its SOSIX alias) separately observes exact
registry ownership only. It neither probes kernel liveness nor reads stdout;
exited/drained retained slots remain valid. It is not validation followed by a
PID action: every actual action still independently validates both fields.

PPIPE-05: explicit invalid/zero Ref is rejected before FFI. A retired or changed
registry generation is `stale_process_reference`. Windows process/job handles
support checked cleanup, preserving closing/retiring claims across long cleanup
outside the registry lock and revalidating generation before freeing. Duplicate
Windows close and all later operations on the retired Ref fail stale.

## POSIX liveness and close are intentionally unsupported

A registry generation is not an exact kernel process-group incarnation handle.
No new POSIX Ref liveness or close path waits/reaps or sends a signal. An
externally reaped leader could have a stale `leader_reaped` flag and its PID
could name a successor; a registry match alone cannot authorize waitpid either.
Valid POSIX Ref liveness returns native -3 / `Err("process_liveness_unsupported")`.
Valid POSIX Ref close returns native -3 / `Err("process_close_unsupported")`,
retaining slot/descriptors, whether live or EOF/drained. Repeating it remains unsupported, not a fabricated successful close.
Legacy PID cleanup retains its historical behavior; the Ref facade never falls
back to it. A live unsupported-close child must remain alive and exchange data.

The inherited PID/PGID tree mechanism is not new group authority. Generic legacy
wait/reap APIs are not expanded by this patch; arbitrary mixed use cannot be
claimed safe incarnation supervision. Before making POSIX Ref lifecycle operations operational,
an exact group-owner mechanism and coordinated reaping are prerequisites. This
is a real missing capability. Retained slots/descriptors, and an exited child that has not otherwise been
reaped, persist until the owning host/fixture process exits. Retained slots
consume the bounded 16-slot registry
until the owning host/fixture process exits; a long-lived host must not treat this draft as admitted
unbounded launch/cleanup support. There is no reset/restart ownership promise.

## Native ABI and generation policy

Scalar ABI avoids a new aggregate/out-parameter language ABI:

| Symbol | Contract |
|---|---|
| rt_process_spawn_piped_generation_v1(cmd,cmd_len,args) | Positive reserved-slot generation; -1 failure |
| rt_process_piped_pid_for_generation_v1(generation) | PID for that exact generation; -2 absent, -1 runtime failure |
| rt_process_read_stdout_ref_v1(pid,generation) | Existing TLS framed text, empty on no chunk/error |
| rt_process_stdout_state_ref_v1(pid,generation) | 0 deferred,1 observed/drained EOF,-2 stale,-1 error |
| rt_process_write_stdin_some_ref_v1(pid,generation,data,data_len,offset,max_bytes) | Nonnegative accepted byte count,-2 stale,-1 error |
| rt_process_is_piped_alive_ref_v1(pid,generation) | 0 stopped,1 running,-2 stale,-3 POSIX unsupported,-1 error |
| rt_process_validate_piped_ref_v1(pid,generation) | 0 retained/current registry owner,-2 stale/closing,-1 lock failure; no I/O/liveness |
| rt_process_close_piped_ref_v1(pid,generation) | 0 cleanup complete,-2 stale/duplicate,-3 POSIX unsupported,-1 error |

Windows captures generation while the exact slot remains spawn-reserved. POSIX
captures its actual reserved slot generation inside the private spawn helper;
a private optional C out parameter carries it through publication. Public spawn
returns this scalar, never adopts a generation via PID lookup after legacy spawn.
The generation-only PID accessor cannot select a reused slot. If another owner
closes before access, it fails stale. Shared counters refuse allocation at
INT64_MAX before increment; generation zero is never an identity.

## Focused tests and provenance

All production changes are authored on clean fetched base. Dirty shared-tree
runtime/process facade edits were inspected but not copied. Owned source paths:
`src/runtime/runtime_process.c`, `runtime.h`,
`src/lib/nogc_sync_mut/io/process_ops.spl`, `sosix/process.spl`.
No duplicate registry, supervisor, compiler patch or app facade is added.

- `src/runtime/test/piped_process_ref_v1_selfcheck.c` includes the actual owner.
  Native fixtures create real pipes/child processes, retain an earlier same-PID
  slot, prove exact-generation slot selection, stale cross-operation refusal,
  byte partial progress, actual pipe saturation/zero backpressure, invalid write
  bounds, independent legacy PID compatibility, post-exit UTF-8 tail/EOF,
  generation cap and counted
  input rejection. POSIX signal observation forwards actual syscalls and asserts
  no signal or wait during valid live/retained/EOF Ref lifecycle queries,
  including a stale unreaped flag pointing at a reused target. The child
  exchanges data after unsupported close. Only the explicit native TEST owner
  reaps its known actual child after EOF; this is not a production fallback. Windows tests actual close
  then duplicate/stale operations. POSIX test-only descriptor retirement exists
  solely to construct replacement generations and clean native fixtures. It is
  not a supported production cleanup path or a synthetic treeStopped bypass.
- `test/fixtures/piped_process_ref_v1.spl` contains actual facade oracles, shared
  by unit spec and `test/fixtures/native_piped_process_ref_v1/main.spl`. The shared
  fixture uses direct assertions and imports no SSpec runtime. Missing
  `SIMPLE_PIPED_REF_CHILD` fails explicitly. A POSIX Simple fixture performs one
  bounded spawn, observes unsupported close and retains it until the owning host/fixture process exits.
- `test/01_unit/lib/io/piped_process_ref_v1_spec.spl` and its manual cover invalid
  and stale refs, pre-effect input rejection, stream byte progress, deferred/EOF
  and platform close outcomes. Same-PID coexistence/reuse is a native white-box
  case, not a claim that an actual OS PID-reuse race has executed.

## Pending verification commands

No supported producer/build slot is allocated. All commands must retain the
shared `taskset -c 0-4` CPU cap, private cache/TMPDIR, outer timeout and exact
producer/runtime/provider identities. Do not repeat earlier unqualified runs.

1. Build the C selfcheck against the normal CoreC value/runtime/fork providers
   with runtime_process.c supplied by its included production translation unit;
   do not link another runtime_process.o. Run it under `timeout 30s`. The concrete
   archive/provider command must be selected from the allocated build receipt,
   not guessed from an older producer path.
2. `<admitted-runtime> test test/01_unit/lib/io/piped_process_ref_v1_spec.spl`,
   with `SIMPLE_PIPED_REF_CHILD` set to that actual absolute native selfcheck path.
3. `<allocated-producer> native-build --source src --entry-closure --entry
   test/fixtures/native_piped_process_ref_v1/main.spl --output <private>/probe`;
   run probe with the same child fixture and outer timeout.
4. Run required core/library/MCP checks and MCP stdio smoke on an admitted runtime
   before any runtime-gate PASS. Windows source requires independent native
   execution; Linux execution cannot establish Windows cleanup/overlapped proof.

Draft disposition: awaiting source review and verification, not merged/admitted.

## Pending verification isolation

Each SDK Simple facade fixture invocation intentionally retains exactly one
POSIX registry slot and its child ownership until the owning fixture host
process exits. The independent Caret fixture retains two. Run each SSpec or
native diagnostic in a separate host process; never repeat them against a shared
16-slot registry. Intentional exhaustion from unsupported POSIX lifecycle
cleanup is a known capability limit, not a retry bug or a reason to rerun the
same diagnostic. The native C harness explicitly retires its own test fixtures;
that test-only ownership is not a production Ref cleanup fallback.
