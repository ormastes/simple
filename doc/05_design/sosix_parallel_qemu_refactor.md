<!-- codex-design -->
# SOSIX Parallel Refactor and QEMU Proof — Detailed Design

**Architecture:** `doc/04_architecture/sosix_parallel_qemu_refactor.md`
**Requirements:** `doc/02_requirements/feature/sosix_parallel_qemu_refactor.md`

## 1. Frozen types

```text
SosixOperationId { slot: u32, generation: u32 }
SosixCapabilityRef { slot: u32, generation: u32 }
SosixBufferRef { slot: u32, generation: u32 }
SosixCompletion<T> { operation, state, value, transferred, error }
SosixDeadline { monotonic_ns }

QemuLaneSettingsV1 {
  host, guest, emulator, machine, cpu, firmware,
  accelerator, memory, kernel, image, serial, qmp,
  timeout_ms, required_markers, artifact_root
}

QemuEvidenceBundleV1 {
  schema_version, descriptor_hash, run_nonce, source_revision,
  compiler_provenance, qemu_provenance, media_hashes, executed_argv,
  host, guest, accelerator, status, reason, transcript_paths,
  boot_receipt, mount_receipt, listing_receipt, program_receipt
}
```

Raw backend handles remain private. Shared requests carry slot/generation
references and bounded scalar fields only.

## 2. SOSIX algorithms

### Submission

1. Validate capability rights, buffer generation/domain, offsets, length, and
   deadline without mutating external state.
2. Allocate a free slot and return its current generation.
3. Attach a completion notification before transport publication when a
   compatibility waiter exists.
4. Publish the request once. Submission failure finishes the same operation as
   error; it never leaks a pending slot.

### Completion

1. Resolve `(slot, generation)` and require `pending`.
2. Record status, transferred count, and typed result.
3. Advance file offset by successful transferred bytes only when the request
   uses compatibility cursor semantics.
4. Publish terminal state, then signal the attached notification.
5. Reject duplicates and stale generations without changing the stored result.

### Cancellation and deadline

Cancellation is a request, not retroactive erasure. The winner of completion,
cancellation, or timeout owns the one terminal transition. Backend cancellation
is attempted when supported. A late backend reply is discarded by generation
and state checks. Reset increments the queue epoch and completes or cancels all
accepted operations exactly once.

### Compatibility wait

The sync adapter creates a notification, attaches it before submission, checks
for immediate completion, performs one bounded wait, rechecks state, destroys
the notification, and releases the slot. Notification creation/wait failure
returns a defined errno and never falls back to unbounded polling.

### VFS transport split

`read_at_async`/`write_at_async` submit IPC and return. A VFS completion worker
owns reply receive, copy/DMA completion, typed finishing, and wakeup. The
current immediate IPC receive is not a viable compatibility transport: syscall
20/21, the VFS service, SOSIX client, and bare-metal shim implement mutually
incompatible payload and reply ABIs.

The migration therefore uses a new versioned owned-copy surface. Its request
envelope authenticates source/reply endpoints and carries API ID, operation
slot/generation, request token, flags, and deadline. `READ_AT`/`WRITE_AT`
descriptors carry capability and registered-buffer references plus explicit
resource/buffer offsets and length. A completion carries the same correlation
key, status, transferred count, and bounded payload length. The kernel copies
bytes into owned queue storage; legacy metadata-only syscall 20/21 is never
used as proof of the new transport.

One completion pump owns each reply endpoint, receives nonblocking, validates
source, ABI, lengths, API ID, token, and generation, and publishes exactly one
typed completion before signaling its wait set. POSIX shared-offset sequencing
is above `read_at`/`write_at`; it is never encoded as `SEEK + READ`.

## 3. Host-service interfaces

```text
HostDisplayService
  open_session_async(config, deadline)
  create_surface_async(session, descriptor, deadline)
  present_async(surface, generation, frame_sequence, frame, deadline)
  readback_async(surface, generation, frame_sequence, buffer, deadline)
  resize_async(surface, generation, extent, deadline)
  close_async(capability, deadline)

HostInputService
  next_event_async(stream, deadline)
  try_take_event(stream)

HostTimerService
  monotonic_now()
  deadline_async(deadline)

HostConfigurationSnapshot
  display_backend, input_backend, gpu_backend, evidence_policy,
  motion_policy, qemu_storage_root
```

File, process/IPC, and library services use the same operation model. Backend
dispatch tables are constructed once after successful library loading and are
immutable during frame processing.

`SosixInputStreamState` is the canonical input queue owner. Producers publish
strictly increasing sequence numbers and non-regressing timestamps. Capacity
is bounded. Only an adjacent newest pointer-motion event may be replaced when
full; key, text, and button events apply backpressure and are never silently
coalesced. Close rejects publication but permits queued events to drain.

Present completion keys are `(surface slot, surface generation, frame
sequence)`. Resize creates a new generation. Stale readback/present completion
cannot update current WM state. Frame queues apply explicit backpressure;
dropping/coalescing is allowed only when the selected display profile says so.

`SosixDisplaySurfaceState` is the canonical pure transition owner. It records
the next submission sequence, oldest in-flight sequence, bounded in-flight
count, surface generation, and closed state. Completion is ordered; resize and
close require the queue to be drained. Backend adapters store native handles
beside this state but may not duplicate or weaken these transitions.

## 4. QEMU settings and runner

The Simple descriptor is authoritative. Shell helpers only resolve host paths,
preflight binaries/media/accelerators, prepare isolated overlays, and invoke
the shared runner. Required behaviors:

- `--print`: deterministic resolved settings with no mutation;
- `--check`: validate emulator, firmware, media, storage, and accelerator;
- `--prepare`: create only the selected lane's directories/overlay;
- `--run`: bounded execution and evidence retention;
- exact argv is serialized before spawn and copied into the final receipt.

Media under the repository may be inputs; large downloads, overlays, cache,
and retained evidence live below the resolved big-storage root. No script may
recursively delete the root or another run directory.

## 5. Guest proof protocol

Each run generates an unpredictable nonce and requires these correlated guest
records in order:

```text
SOSIX_QEMU_BOOT host=<h> guest=<g> nonce=<n> ...
SOSIX_QEMU_FS_MOUNT host=<h> guest=<g> nonce=<n> filesystem=<id>
SOSIX_QEMU_FS_LS host=<h> guest=<g> nonce=<n> path=<p> entries=<digest>
SOSIX_QEMU_PROGRAM host=<h> guest=<g> nonce=<n> path=<p> rc=0 stdout=<digest>
```

The listing must name the chosen filesystem payload. The program path must be
on that mounted filesystem and its output must match a per-run challenge, so a
fixed kernel response cannot pass. Compiler-bearing rows add version, compile,
and executable receipts for `hello.spl`.

## 6. Matrix scheduling

The matrix is 4 hosts by 6 guests. A current host runner executes guests
sequentially by default to avoid memory/disk contention. An operator may select
`--all-guests --parallel` on a prepared host: every child receives an isolated
log, no child writes the aggregate receipt, and the parent waits for all six
before recording deterministic row results. Independent hosts and build-only
lanes may also run in parallel. Each cell is attempted once per unchanged
criterion and at most three distinct repair cycles.

Linux runs TCG for all six and applicable KVM acceleration. Windows runs the
same descriptors through WHPX/TCG. macOS uses HVF/TCG and remains blocked when
no native executor is available. FreeBSD setup starts with
`scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`, then invokes the
shared matrix. A nested FreeBSD VM proves that host lane only when its receipt
records the actual FreeBSD environment and executed QEMU.

## 7. Evidence validation

Validation is pure and ordered:

1. schema and contract hash;
2. source/compiler/QEMU/media provenance;
3. host/guest/accelerator agreement with executed argv;
4. nonce and marker ordering;
5. boot and mount identity;
6. listing payload;
7. arbitrary program path, challenge output, and zero exit;
8. optional compiler version and hello compile/run;
9. absence of fallback/fixed-response markers.

After these checks, the collector emits a closed verified-row receipt. Matrix
classification recomputes admission from that receipt; it must reject
path-only evidence, forged `verified` flags, non-PASS receipt status, dirty
source identity, unbound transcript/program digests, placeholder firmware,
relative firmware paths, invalid firmware hashes, or missing/out-of-order boot
stages before evaluating the row's remaining fields.

Any failure produces a stable reason and retains raw artifacts. Aggregation
passes only when every required cell passes; blocked cells remain visible and
red at umbrella level.

## 8. File and ownership plan

| Owner | Files/directories | Rule |
|---|---|---|
| integration | `io_state.spl`, `io_rw.spl`, QEMU façade/exports | shared choke points only |
| core | `src/os/sosix/core/**` | no QEMU or renderer dependency |
| filesystem | `src/os/sosix/fs/**` | VFS transport and POSIX parity |
| host seam | `src/os/sosix/host/**` | traits/state machines only |
| compositor adapter | `src/os/compositor/host_services/**` | no Draw IR ownership change |
| QEMU settings | private descriptor modules and `scripts/qemu/**` | consume canonical schema |
| evidence | `src/os/sosix/qemu_evidence/**` | pure classifier/receipt logic |
| tests | SOSIX/QEMU test trees | no production edits |

The merge owner removes legacy `src/os/sosix/io.spl` only after symbol/import,
dynamic-entry, and parity gates prove it dead. No agent deletes shared or dirty
files owned by another session.

## 9. Test design and traceability

| Requirement | Required evidence |
|---|---|
| REQ-SQ-001, REQ-SQ-009, REQ-SQ-013 | settings precedence, deterministic argv, malformed input and lane isolation specs |
| REQ-SQ-002, REQ-SQ-010, REQ-SQ-015 | lifecycle, stale generation, partial progress, cancel race, notification wait, POSIX offset/errno specs |
| REQ-SQ-003, REQ-SQ-004, REQ-SQ-012 | 24-cell classification with explicit blocked/native-host receipts |
| REQ-SQ-005 | board-specific boot and ordered nonce marker evidence |
| REQ-SQ-006 | target-side mount and listing transcript |
| REQ-SQ-007, REQ-SQ-008 | challenged arbitrary program and optional target compiler proof |
| REQ-SQ-011 | provenance/hash/argv/accelerator sabotage tests |
| REQ-SQ-014 | host-service adapters against absolute input/frame/pixel oracles |

System scenarios use the six frozen operator steps from the agent plan. Manual
generation must report zero stubs and no executable spec may appear beneath
`doc/06_spec`.

## 10. Performance and observability

- No per-pixel/per-primitive SOSIX calls or hot-frame environment/process I/O.
- One present operation per frame/surface; input is queued and optionally
  motion-coalesced.
- Warm host-service calls do not spawn subprocesses or rescan the repository.
- Counters record submitted/completed/canceled/timed-out operations, queue high
  water, notification wakeups, stale completions, frames dropped/coalesced,
  staged/direct bytes, and QEMU phase durations.
- Receipts expose timings and maximum RSS for realistic QEMU runs. Native
  latency claims require the native accelerator in executed argv.

## 11. Error mapping

Invalid/stale capability is `EBADF`; invalid buffer/range is `EINVAL`; queue
capacity is `EAGAIN`; deadline is `ETIMEDOUT`; cancellation is `ECANCELED`;
transport/device reset is `EIO` with reset generation. Compatibility adapters
translate typed errors once at the POSIX boundary.

## 12. Integration gates

1. Typed lifecycle and notification tests pass.
2. VFS async worker proves submission returns before reply.
3. POSIX parity and deliberate duplicate/stale sabotage pass.
4. Host-service contract and Linux/headless adapter parity pass.
5. Linux x86_64 boot/mount/list/program vertical slice produces fresh receipt.
6. Remaining guests and external native hosts produce receipts.
7. Direct environment/runtime guards and required full verification pass using
   the deployed pure-Simple binary.

The feature remains incomplete while any required row is blocked or evidence
comes only from the bootstrap seed.

## 13. Documentation and capability receipt

AC-13 requires the local/domain research, selected requirements/NFRs,
architecture, detail design, QEMU guide, all three SPipe integration surfaces,
and SOSIX/QEMU feature/layer expert pages to name the same canonical wrappers
and evidence boundary. The 2026-08-16 release status is 3 PASS / 21 non-PASS:
Linux x86_64, ARM64, and RV32 retain canonical producer bundles; other Linux
and external-host diagnostics remain blocked/postponed until their complete
collector admission. Documentation review is repeated when a wrapper,
descriptor, marker, storage resolver, or blocked-row resume command changes.
