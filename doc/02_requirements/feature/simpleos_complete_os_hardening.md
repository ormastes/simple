# SimpleOS Complete OS Hardening — Feature Requirements

Status: **Selected** (2026-08-20)

## Selection record

The user selected “full implementation, robustness first, performance, and the safe way to implement.” This resolves the option groups as:

- `F-1A`: dependency-ordered convergence.
- `F-2A`: strict portable filesystem core plus declared backend extensions.
- `F-3B`: authenticated-only executable loading.
- `F-4B`: separate least-privilege compiler, interpreter, and loader payloads.
- `F-5B`: full C/C++ LLVM developer profile.
- `F-6C`: expanded base userland.
- `F-7B`: full modern web/server profile.
- `F-8A`: complete SimpleOS-native production WM; external EWMH/Wayland compatibility is not claimed by this feature.

All x86_64, AArch64, and RISC-V 64 rows remain required. “Implemented,” staged artifacts, host execution, fixed-command responders, source presence, emulated evidence, and physical-board evidence are distinct states and may not substitute for one another.

## Functional requirements

### REQ-001 — Capability ledger

SimpleOS shall publish one versioned `SimpleOsCapabilityLedger` that maps boot, process/task, memory, filesystem, execution, toolchain, userland, networking, servers, security, drivers, WM, observability, recovery, architecture, and evidence capabilities to one canonical owner and one or more executable acceptance rows. Every required row is `PASS` or `BLOCKED`; missing, skipped, inferred, or unsupported rows do not satisfy completion.

### REQ-002 — Three-architecture system execution

Reproducible x86_64, AArch64, and RISC-V 64 images shall boot through their canonical firmware paths and retain image/binary hashes, compiler/runtime identity, guest ISA/ABI, firmware/board identity, executed argv, native/accelerated/emulated classification, ordered logs, and machine-readable receipts. Each architecture shall pass the same behavior IDs; architecture-specific differences are declared capabilities rather than silent forks.

### REQ-003 — Shared filesystem contract

Existing `FsDriver`, `DriverInstance`, `MountTable`, and `FsError` shall be the canonical implementation boundary corresponding to the provisional `SimpleOsFileSystem` name. FAT32, DBFS, and NVFS shall implement one strict portable core: mount/unmount, create/open/close, read/write, positional I/O, seek/truncate, rename/delete, directory iteration, metadata, free-space reporting, flush/sync, typed errors, capability queries, and executable lookup. Backend-only semantics shall be declared extensions with negative capability tests.

### REQ-004 — FAT32 interoperability and recovery

FAT32 shall implement and test the selected UEFI-compatible FAT32 profile, long filenames, path/case rules, allocation chains, duplicate FAT handling, reserved-field preservation, the 4 GiB file limit, dirty/error reporting, atomic replacement where promised, mount-time validation, and bounded rejection/recovery for malformed BPBs, invalid/cyclic/cross-linked chains, orphaned clusters, inconsistent sizes, damaged FAT copies, malformed LFN sequences, and interrupted metadata updates.

### REQ-005 — DBFS durability and recovery

DBFS shall expose the portable filesystem core while preserving WAL, checkpoint, replay, MVCC, namespace, device-blob, and committed-data guarantees. Tests shall prove explicit commit/flush boundaries, clean and crash recovery, corrupted/truncated/checksum-invalid metadata handling, bounded replay, reboot persistence, and no fabricated committed data.

### REQ-006 — NVFS durability and recovery

NVFS shall expose the portable filesystem core without delegating unsupported behavior through unbounded process-global mirrors or silently returning fabricated capacity/offset semantics. Native and POSIX providers shall declare their true capabilities, prove remount persistence and recovery, and share one canonical owner with legacy parallel implementations removed or routed through an adapter.

### REQ-007 — Authenticated executable loading

Every filesystem executable shall be admitted from an already-open handle only after mount policy, executable permission, file size/range, format, target ISA/ABI, manifest role, content digest, and signature/trust-root validation. System images may carry authenticated executable manifests; removable or unauthenticated mounts default to `noexec`. Path replacement, wrong ISA, malformed/corrupt content, revoked signatures, missing dependencies, and untrusted media fail before execution with typed diagnostics and no host/PATH/fixed-command fallback.

### REQ-008 — Backend-neutral program execution

On every architecture, a real program shall be copied to, discovered on, admitted from, and executed from FAT32, DBFS, and NVFS through the canonical executable loader. The run shall preserve argv, environment capability policy, working directory, relative path behavior, stdout, stderr, exact exit status, cancellation, cleanup, and post-reboot behavior. Cache entries shall invalidate on create, edit, truncate, replace, rename, delete, mount, unmount, and trust-manifest change.

### REQ-009 — Target-native Simple roles

Separate least-privilege target-native compiler, interpreter, and loader payloads and their declared dependencies shall be embedded at all required canonical paths: `/usr/bin/simple(.smf)`, `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`, `/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`, `/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`. Every guest shall run `/usr/bin/simple --version`, interpret a filesystem source, compile it, load the target artifact, delete the source, and rerun the artifact with exact output and exit 0.

### REQ-010 — Full target-native LLVM/Clang profile

Every architecture image shall contain guest-native Clang C/C++, LLD, selected LLVM utilities, target headers, startup objects, libc/OS runtime, compiler runtime, libc++, unwinder, development libraries, and an explicit SimpleOS target triple/sysroot layout. In each booted guest, filesystem-resident `clang`/`clang++` and `ld.lld` shall compile, link, and run freestanding C plus hosted C and C++ hello-world programs from the mounted filesystem. Host tools, cross-build staging, wrappers, prebuilt output, or file inspection do not satisfy this requirement.

### REQ-011 — Expanded Simple userland

A versioned manifest shall truthfully classify every primary Linux-compatible utility as supported, partial, unavailable, or blocked and record source owner, artifact, capabilities, target ISAs, filesystems, version/help contract, and evidence. The supported set shall include the core administration tools plus archive/compression, networking, checksums, text processing, process monitoring, and package-management tools. Every supported tool shall be implemented in Simple without fabricated stubs and execute one representative real operation plus an error path from FAT32, DBFS, and NVFS on every supported architecture.

### REQ-012 — Unified bounded server lifecycle

Filesystem-resident web, database, and SSH servers shall use one `SimpleOsServerLifecycle` contract for authenticated image admission, bind/listen, readiness, foreground/service operation, bounded worker/task ownership, cancellation, graceful drain, terminal close, restart, and receipt capture. Child workers shall return fresh results through bounded transports; the lifecycle owner validates and commits them deterministically. Repeated start/stop shall reclaim tasks, sockets, handles, files, credentials, leases, and queues.

### REQ-013 — Full modern web protocols

The web server shall implement and advertise versioned production profiles for HTTP/1.1, HTTP/2, and HTTP/3 over QUIC; TLS and ALPN; selected WebSocket and WebTransport behavior; streaming compression; proxy/application handlers; and cross-version interoperability. It shall implement the applicable framing, settings, header-list, stream, flow-control, congestion, retransmission, timeout, backpressure, connection-close, extension-negotiation, and downgrade rules. A helper/parser without its transport and lifecycle is not protocol support.

### REQ-014 — Database protocols

The database server shall advertise a versioned native Simple DB protocol and RESP profile, each naming transport/TLS/ALPN, framing, authentication, operations, batch/range/response limits, transactions/isolation, cancellation, timeouts, extensions, and error mapping. Unknown mandatory features, unsupported auth, downgrade attempts, malformed/oversized/truncated input, stalled peers, and replay/substitution of unauthenticated capability manifests shall fail closed.

### REQ-015 — Production SSH v2

Simple SSHD shall implement the selected SSH v2 transport, user-authentication, and connection profiles with current allowlisted algorithms, authenticated host keys, password/public-key policy, bounded packets/auth attempts/time, channel/window/output backpressure, shell and filesystem exec, rekey thresholds, extension negotiation, disconnect, cancellation, and terminal cleanup. Hardcoded production users, passwords, host keys, silent algorithm downgrade, unbounded synchronous admission, and shallow fixed-command execution are forbidden.

### REQ-016 — Server confinement and malformed-input safety

All servers shall enforce explicit filesystem, network, process, bind, credential, and privileged capabilities plus configured request/header/body/message/query/result/connection/task/queue/session/time limits. Tests shall prove bounded behavior for traversal, injection, unauthorized access/bind, secret disclosure, malformed framing, fuzzed input, slow clients, exhaustion, disconnects, interrupted shutdown, and repeated lifecycle campaigns. Retained logs, diagnostics, traces, and manuals shall contain no credentials or private key material.

### REQ-017 — Production SimpleOS window manager

The canonical SimpleOS WM owner and framebuffer/input/render adapters shall launch after clean boot on all three architectures and prove desktop presentation; two-window open/close; focus/stacking; move/resize; keyboard/pointer routing; clipping/expose/redraw; scene submission and framebuffer readback; clean restart; and bounded failure when display/input/compositor dependencies fail. Headless, showcase-only, fabricated event/handle, static-source, zero-frame, or screenshot-only evidence is insufficient. This feature does not claim EWMH or Wayland protocol compatibility.

### REQ-018 — Observability and performance ownership

Boot, filesystem mount/I/O/exec, loader verification, compiler phases, LLVM compile/link, server lifecycle/request paths, SSH sessions, primary tools, and WM input/render/presentation shall emit bounded counters/timings and stable receipt fields. Hot paths shall not perform repeated full-tree scans, raw-source execution, unbounded capture, per-request compiler/process startup, or stale cache reads; every mutable cache declares invalidation.

### REQ-019 — Canonical ownership and duplicate removal

Filesystem dispatch/backend ownership, executable loading, server lifecycle, DB transport, WM lifecycle, input routing, and render submission shall each have one canonical mutable owner. Parallel implementations shall be removed or reduced to thin adapters. Cross-domain values shall be classified as copy, frozen share, owned move, scoped loan, handle, encoded payload, or lease; raw pointers and unknown dynamic transport are forbidden at safe external boundaries. Child-created results shall be validated and committed by the parent owner in deterministic order.

### REQ-020 — Evidence, manuals, and knowledge

Every requirement shall map to executable SSpec scenarios with real typed/captured evidence and the shared step vocabulary. Generated manuals shall be usable without opening source. Research, requirements, architecture, UI/detail design, test/agent plans, guides, feature/layer expert wikis, workflow contracts, reports, and every found-but-unfixed bug shall remain current. No release/umbrella PASS is allowed while a required architecture, physical host/board, backend, protocol, tool, security, performance, or WM row is blocked.

## Dependency order

1. Evidence/capability ledger and canonical ownership contracts.
2. Shared filesystem semantics, durability, authenticated execution, and cache invalidation.
3. Per-ISA loader/process execution and target-native Simple roles.
4. Full LLVM/Clang target profile and expanded userland.
5. Unified server lifecycle, complete protocols, and security campaigns.
6. Canonical production WM and cross-architecture visual/interaction evidence.
7. Performance/duplication convergence, physical campaigns, whole-release verification.

