<!-- codex-design -->
# SOSIX Refactor and Multi-Host QEMU Architecture

**Status:** implementation architecture  
**Requirements:** `REQ-SQ-001` through `REQ-SQ-015`  
**Date:** 2026-08-11

## Decision

SOSIX is the sole host-service boundary for SimpleOS and hosted application
code. QEMU remains an execution backend driven by one typed descriptor, while
WM, GUI, Web, Draw IR, and Engine2D retain their existing semantic ownership.
Deferred host work uses typed operations and notification-backed completion;
configuration is snapshotted once and rendering hot paths submit batches.

```text
portable application / WM / renderer orchestration
                         |
       typed SOSIX host-service capabilities
                         |
       operation + completion + deadline + cancel
                         |
        +----------------+----------------+
        |                                 |
 hosted OS adapters                SimpleOS services
        |                                 |
 winit/SDL/Cocoa/Win32             display/input/VFS/IPC

QEMU matrix -> QemuLaneSettingsV1 -> QemuRunner -> serial/evidence collector
```

This replaces parallel raw-FD/request-table, host-call, and copied-QEMU-argv
paths incrementally. POSIX is a compatibility projection over SOSIX, not a
second native I/O model.

## MDSOC ownership

| Capsule | Public-to-next-layer contract | Private implementation |
|---|---|---|
| `os.sosix.core` | operation IDs, typed completions, cancellation, deadlines | slots, generations, transition checks |
| `os.sosix.fs` | capability `read_at`/`write_at` | VFS transport and registered buffers |
| `os.sosix.host` | display, input, timer, configuration, process and library traits | hosted/SimpleOS adapters |
| `os.sosix.compat` | bounded synchronous and POSIX adapters | errno/offset translation |
| `os.qemu_systest_contract` | `QemuLaneSettingsV1` and evidence schema | per-ISA descriptors and argv lowering |
| `os.sosix.qemu_evidence` | receipt validation | marker parsing and sabotage rejection |
| compositor/Engine2D | scene, Draw IR, raster, GPU submission semantics | backend resources and transient caches |

Sibling capsules communicate only through these contracts. SOSIX never owns
Draw IR nodes, layout, font atlases, raster algorithms, or backend GPU state.

Cross-cutting evidence, timeout, and cancellation policy is a feature
transform over operations and QEMU runs: it adds correlation and receipts but
does not change service semantics.

## Canonical asynchronous model

`SosixOperationId(slot, generation)` identifies one allocation lifetime.
Completion is a one-way transition:

```text
free -> pending -> complete
                -> error
                -> canceled
```

Only `pending` may transition. Every accepted request yields at most one
terminal completion. Slot reuse increments generation; stale completion,
cancellation, notification, surface generation, frame sequence, or QEMU nonce
is rejected. Compatibility waits attach one notification before submission,
sleep once with a deadline, then recheck terminal state. They never spin.

Filesystem offsets advance only by successful transferred bytes. Partial
progress is retained even when a later stage reports an error. Resource rights
and deployment capabilities are checked independently.

## WM and renderer boundary

The public host seam is composed rather than inherited:

```text
HostServicesV1
    configuration: HostConfigurationSnapshot
    display: HostDisplayService
    input: HostInputService
    timer: HostTimerService
    files: HostFileService
    process: HostProcessService
    libraries: HostLibraryService
```

Display operations use `(surface capability, surface generation, frame
sequence)`. Resize invalidates the old generation. `present_async` accepts one
frame/composition submission, never one request per primitive or pixel.
Input is a sequenced event stream; only declared motion events may coalesce.
Environment/backend selection is immutable after bootstrap. Library loading
and process/QMP control are startup/control-plane operations.

Hosted adapters may call winit, SDL, Cocoa, or Win32 privately. SimpleOS
adapters use SOSIX services. Headless adapters implement the same traits and do
not pretend to be native window systems.

## QEMU execution architecture

One descriptor owner lowers each of six guest identities (`x86_32`, `x86_64`,
`arm32`, `arm64`, `riscv32`, `riscv64`) into exact emulator, machine, CPU,
firmware, accelerator, memory, disk, serial, QMP, timeout, and marker settings.
Host overlays select only proven KVM/HVF/WHPX/NVMM support; TCG is correctness
evidence, never native-performance evidence.

Large storage resolves in this order:

1. `SIMPLE_BIG_STORAGE_ROOT`;
2. workspace `.simple-big-storage-root`;
3. `$HOME/.simple`.

This workspace selects `/mnt/data/.simple`. Each run owns an isolated overlay
and writes beneath
`<root>/qemu/artifacts/sosix-qemu/<host>/<guest>/<run-id>/`. Cleanup is explicit
and lane-scoped.

Every row is `pass`, `failed`, `blocked`, or `unsupported`. Missing media,
firmware, host access, or evidence is never converted to skip/pass. macOS may
remain blocked only with prerequisites, exact resume command, artifact path,
owner, and reviewer.

## Evidence trust boundary

A passing bundle binds source revision, compiler path/hash/provenance, kernel
and image hashes, QEMU path/version, exact argv, executed accelerator, host and
guest identities, nonce, timestamps, exit status, serial transcript, and
filesystem/program receipts. Guest markers prove boot, mount, `ls`, and an
arbitrary target-native filesystem program. Compiler-bearing images also prove
`/usr/bin/simple --version` and compile/run `hello.spl`.

The pure matrix evaluator never treats an evidence pathname or a caller-set
boolean as proof. It parses the collector's bounded canonical admission record:
exactly 41 ordered scalar keys followed by 1 through 13 literal, ordered
artifact path/hash pairs; a release PASS is valid only for the canonical 9 or
13 artifact set. The parser rejects reordered or duplicate fields,
padded artifact indices, noncanonical decimal counts, unknown fields, and
oversize records or lines. A passing row is derived from that parsed receipt
rather than duplicating caller-selected host, guest, policy, and evidence
fields.

Parsing proves only structural consistency; `SosixQemuParsedBundleAdmission`
does not claim that supplied hashes describe retained bytes. The collector
publishes independent evidence-snapshot and admission-record SHA-256 values in
the matrix manifest. The typed row checks the manifest evidence-hash claim
against the receipt. The production `trusted_importer` owner accepts a collector
root rather than caller-supplied record text: it snapshots `matrix.env`, parses
the selected row fields, requires canonical base64 and cell-relative admission
paths, canonicalizes the root and record path, rejects non-regular or escaping
paths, hashes the exact admission bytes against the manifest's
`admission_record_sha256`, and parses those same bytes before constructing a
typed row. The importer consumes the closed matrix wire—two headers, 24
sequential 42-field row descriptors, and one bundle ID—and rejects any extra,
missing, reordered, duplicate, or noncanonical field. It imports and byte-binds
both PASS and non-PASS records, preserving BLOCKED/FAILED/UNSUPPORTED reason,
resume, and ownership data.

Every raw and base64 manifest field is canonical-decoded and cross-bound to the
same hashed admission record, including source/compiler lineage, kernel/image,
QEMU argv/accelerator, firmware, nonce, transcript, and program identities.

The public raw-record constructor is explicitly named `structural` and is not
re-exported by the package admission surface. It yields only the structural
`SosixQemuMatrixResult`. No trusted result or capability crosses the module
boundary: the only release API is
`sosix_qemu_collector_root_is_release_admissible(collector_root)`, which performs
trusted import and the exact all-24-PASS gate internally. Caller-authored rows or
results therefore cannot be supplied to the release gate. The importer exists
in source, but typed runtime provenance remains **HOLD** until it executes with
a current self-hosted compiler.

Fixed responses, host-side `ls`, replayed nonces, stale descriptor hashes,
missing native accelerators, and nonzero program exits fail closed.

## Deployment sequence

1. Consolidate typed core and compatibility notification waits.
2. Freeze a versioned owned-copy VFS envelope and wire new IPC syscalls; legacy
   metadata-only syscall 20/21 remains isolated.
3. Move VFS reply handling out of submission into a source- and
   generation-validating completion worker.
4. Freeze host-service traits and bootstrap configuration snapshot.
5. Migrate evidence/QMP/file/timer/input paths, then display control and
   present/readback.
6. Remove raw host calls and dead request owners only after parity tests.
7. Prove Linux x86_64 vertical slice, remaining six guests, then native host
   rows. External blocked rows keep the umbrella result incomplete.

## Rejected alternatives

- Unrestricted POSIX or raw pointers in asynchronous/shared contracts.
- A second renderer inside SOSIX.
- Per-frame environment reads or per-pixel host requests.
- Copied QEMU argv in each test.
- File-presence, fixed transcript, or bootstrap-seed results as release proof.
- Declaring unavailable macOS/Windows/FreeBSD rows skipped or passed.

## Release invariants

- No live SOSIX compatibility busy-spin or duplicate request pool.
- No migrated compositor file directly reads environment, runs processes, or
  writes evidence outside its assigned facade.
- Every required matrix cell has fresh correlated evidence.
- Direct/staged/native accelerator claims match executed argv and receipts.
- Production evidence is produced by the pure-Simple deployed toolchain.

## Current admission snapshot (2026-08-12)

The immutable 4-host × 6-guest matrix is **0 PASS / 24**. x86_32, ARM32,
RISC-V32, and RISC-V64 have strong Linux diagnostic transcripts with exact
target-read nonce, real FAT dirent listing, filesystem program execution, and
successful completion. They remain outside the release trust boundary because
the retained source/firmware/compiler lineage is not yet clean and complete.
x86_64 is blocked before boot by image payload capacity; ARM64 is blocked in
FAT/VFS directory-buffer handling after the three-cycle cap. External-host
non-PASS receipts remain required. This snapshot describes admission, not an
absence of implemented guest capability.
