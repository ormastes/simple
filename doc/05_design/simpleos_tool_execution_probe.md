# SimpleOS installed-tool execution probe component

Status: implementation written; runtime qualification **BLOCKED**. This is a
kernel-side integration component, not a standalone boot/VM execution adapter.
The matching unit specification has not been executed with an admitted runtime.

## Required behavior

- REQ-TOOL-PROBE-001: use the actual staged installed artifact and the canonical
  sealed catalog, manifest, trust root, signed per-open admission and ELF checks.
- REQ-TOOL-PROBE-002: check its admitted image SHA-256, canonical path and target
  before handoff; execute the exact full argv through the authenticated owner.
- REQ-TOOL-PROBE-003: consume the scheduler's one-shot, reaped command evidence;
  compare complete stdout/stderr bytes and the independent exit code. Reject
  truncated output or either stream exceeding its declared bound (at most 64 KiB).
- REQ-TOOL-PROBE-004: unavailable media/admission/output evidence must not qualify
  a tool. A synthetic record accepted by a pure comparison helper grants no
  execution authority and is not guest evidence.

The requested user scope remains lint and test runner execution on all six
SimpleOS CPUs with both lld and the internal linker. This component alone does
not fulfill that scope or establish any compiler generation's qualification.
Its initial request route is x86_64; other CPUs explicitly return BLOCKED until
their process-owned stream capture is reviewed. In particular the existing
RV64 merged-stdio buffer cannot satisfy an independent stdout/stderr oracle.

## Integration

`simpleos_tool_probe_run_installed_v1` accepts the boot owner's live scheduler,
mount table lease, authority registry, caller capability set and migrated spawn
recipe. It does not construct a fake mount, mint a token, or seed capabilities.
The caller must preserve canonical VFS lease ownership across its synchronous
call and restore the returned scheduler on every outcome.
The result also transports pending opaque evidence/admission tokens after an
indeterminate consume or revoke. A failed evidence consume can mean either a
stale token or scheduler serialization failure before consumption; it does not
prove retirement. The caller must retain the original registry/mount lease and
resolve those tokens through their canonical consume/revoke owners, without
rerunning the child. This component performs no automatic retry loop. Successful
evidence consumption clears pending evidence ownership; failed admission cleanup
keeps its token even when execution evidence was successfully consumed.

1. `authenticated_fs_exec_prepare_installed_artifact_online_v1` opens the actual
   staged `/bin/...` ELF and obtains catalog-bound, signed loader admission.
   Before this call, `mount_path_canonical` (the same filesystem-owner predicate
   used by MountTable) rejects traversal, dot components, repeated/trailing
   separators, backslashes and control-character aliases. argv[0] must equal
   that canonical path; no normalization is deferred until after execution.
2. `executable_authority_snapshot_armed_preparation_v1` checks the admitted
   digest/path/target against the requested artifact before any execution.
   A mismatch revokes the unused authority through the loader owner.
3. `authenticated_fs_exec_submit_v1` invokes the existing CPU-specific owner;
   x86_64 uses `x86_64_fs_exec_spawn_authenticated_with_launch_v1`. That service
   preserves failed-submission cleanup, exact argv, exit, reap and delivery.
4. `scheduler_execution_evidence_consume_once_v2` consumes real issued evidence.
   Comparison accepts no caller-supplied token substitute or host serial marker.

The image digest must be independently bound by the boot/test owner to the real
Phase-2 compiler and actual selected linker receipt. The probe does not infer
linker provenance from an ELF filename or a caller's linker label. Oracle bytes
come from the real lint finding/help or test-runner fixture contract; they must
not be injected into the guest program as a success marker. A nonzero expected
lint finding exit is compared exactly, rather than collapsed into success zero.

## Explicit missing owners and qualification dependencies

The x86_64 capture integration is owned beside the real write route:
`src/os/kernel/ipc/syscall_file.spl::_handle_file_write`, the descriptor owner,
`src/os/kernel/fd_io.spl`, and `src/os/sosix/io_rw.spl`. Capture must bind the
current task's generation, retain bytes actually emitted, and distinguish
redirected descriptors from their numeric fd spelling. The scheduler supplies
bounded observation in `process_execution_observation.spl`; its legacy implicit
child sink remains a deliberate no-op and must not be used. Existing RV64
capture combines fd 1 and 2 and is not admitted by this initial probe route.

The agreed canonical evidence fields are `stdout_capture_complete` and
`stderr_capture_complete`. The probe requires BOTH owner-issued outcomes,
including for empty expected streams. It never infers capture readiness from a
nonempty oracle, matching prefix, stream length, or caller flag. Pending or
failed protected writes make the relevant stream incomplete. An ambiguous
observation lookup must return EAGAIN before emission; an append/finish failure
must poison completeness or retain its pending lease. Incomplete capture is
BLOCKED even if all currently retained bytes match the expected output.

Empty expected stdout/stderr are legitimate and compare exactly once both
owner outcomes prove completeness. The matching unit spec constructs explicit
synthetic complete/incomplete records to exercise these checks; those booleans
are fixture inputs, never evidence of actual guest capture or owner lifecycle.

Still required: actual compiler/linker products, signed mounted tool manifests,
kernel startup constructing the real scheduler/VFS/authority context, a qualified
kernel without fabricated runtime stubs, and a real-firmware QEMU adapter with
external wall-clock termination. This synchronous component does not implement
VM boot, timeout cancellation or filesystem fixture staging. Host Linux
qemu-user execution cannot replace any of these SimpleOS guest requirements.

The unit spec covers pure comparisons and a pre-admission rejection only.
Fixtures are explicitly synthetic. No source inspection, mock result, or
unexecuted spec counts as kernel, compiler, linker, or guest execution evidence.
