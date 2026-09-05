<!-- codex-architecture -->
# SimpleOS Complete OS Hardening Architecture

## Status

Accepted for implementation after the 2026-08-20 full/robust/performance/safety selection. This document defines target ownership and migration; it does not claim implementation or verification PASS.

## Context

SimpleOS already has substantial filesystem, loader, server, toolchain, evidence, and WM code, but several sibling-private implementations duplicate mutable authority. Filesystem execution is FAT32-specific, target payload staging is confused with guest execution, protocol helper presence is confused with server support, and static/skip-capable evidence has promoted stale claims. The architecture must converge those paths without creating another abstraction stack.

## Decision summary

1. Reuse `FsDriver`, `DriverInstance`, `MountTable`, `FsError`, and `WmService` as canonical owners.
2. Migrate the existing `SimpleArtifactManifest` in `src/os/kernel/loader/artifact_manifest.spl` into the single shared `ExecutableManifestV1` definition, then make the loader file a re-export/adapter and delete its duplicate storage/codec; add the other shared contract nodes without parallel schemas: `ExecutableAdmissionV1`, `ExecutableImageHandleV1`, `ServerLifecycleV1`, `ProtocolCapabilityManifestV1`, `SimpleOsCapabilityLedgerV1`, and `SimpleOsEvidenceReceiptV1`.
3. Resolve and authenticate an already-open filesystem handle before process creation; per-ISA adapters consume the admitted handle.
4. Separate child work from mutable owners: workers create bounded results; filesystem, lifecycle, WM, and ledger owners validate and commit deterministically.
5. Keep QEMU, native-host, and physical-board evidence distinct and fail closed on missing/stale rows.

<!-- sdn-diagram:id=simpleos_complete_os_hardening.architecture -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_complete_os_hardening.architecture hash=sha256:3023dccf render=ascii
@layout dag
@direction LR

filesystems -> executable_admission
filesystems -> evidence_receipts
executable_admission -> toolchains_userland
executable_admission -> server_lifecycle
executable_admission -> wm_service
executable_admission -> evidence_receipts
toolchains_userland -> evidence_receipts
server_lifecycle -> evidence_receipts
wm_service -> evidence_receipts
evidence_receipts -> capability_ledger
capability_ledger -> release_gate
```

</details>

<details class="sdn-ascii" open>
<summary>Architecture</summary>

```ascii generated-from=simpleos_complete_os_hardening.architecture hash=sha256:3023dccf
                    +----------------------+      +---------------------+
+-------------+ --> | executable_admission | ---> | toolchains_userland | --+
| filesystems |     +----------+-----------+      +---------------------+   |
+------+------+                |                                             |
       |                       +------------> server_lifecycle ---------------+
       |                       +------------> wm_service ---------------------+
       |                       |                                             |
       +-----------------------+------------> evidence_receipts              |
                                               ^          |                   |
                                               +----------+-------------------+
                                                          v
                                                capability_ledger
                                                          |
                                                          v
                                                     release_gate
```

</details>
<!-- sdn-diagram:end -->

## Layer list

| Layer | Canonical path/owner | Responsibility |
|---|---|---|
| Shared execution contracts | `src/lib/common/contracts/execution/` | Frozen executable, server, protocol, target/profile records and codecs |
| Shared digest/receipt/invalidation | `src/lib/common/structural/{digest,receipt,invalidation,parallel_commit}/` | Stable hashes, evidence/result envelopes, generation invalidation, deterministic commit vocabulary |
| Filesystem contract | `src/lib/nogc_async_mut/fs_driver/` | `FsDriver`, dispatch, mounts, handles, capabilities, errors |
| Filesystem implementations | FAT32 `src/lib/nogc_async_mut/fs_driver/{fat32_core,fat32_stub}.spl`; DBFS `src/lib/nogc_sync_mut/db/dbfs_driver/`; NVFS `src/lib/nogc_sync_mut/fs_driver/{nvfs_driver,nvfs_posix_driver}.spl` | FAT32/DBFS/NVFS portable-core implementations and declared extensions |
| VFS service | `src/os/services/vfs/` | Sole mounted namespace owner and syscall/IPC facade |
| Loader | `src/os/kernel/loader/` | Manifest validation, open-handle admission, bounded format loading, per-ISA entry adapters |
| Target construction | `src/os/port/`, `scripts/os/` | Per-target sysroots, role builds, image closure, external admission receipts |
| Toolchain/userland | `src/compiler/`, `src/app/`, `src/os/apps/`, `src/os/services/fs_apps/` | Target-native Simple roles, LLVM/Clang profile, truthful utility implementations |
| Server capsule | async HTTP `src/lib/nogc_async_mut/http_server/`; DB `src/lib/nogc_sync_mut/database/server/`; RESP `src/lib/nogc_sync_mut/redis/server.spl`; SSHD `src/os/apps/sshd/` | Authenticated launch, lifecycle, protocol manifests, bounded worker results |
| WM capsule | `src/os/services/wm/wm_service.spl` | Sole window/focus/geometry/lifecycle authority and revisioned scenes |
| Evidence service | `src/os/services/evidence/` (new runtime owner) | Receipt validation, capability-ledger transition, artifact index |
| Evidence runners | `scripts/check/`, `scripts/qemu/`, SSpec | QEMU/native/physical campaign production without ledger mutation authority |

## Tree encapsulation and visibility

Tree-private is the default. No sibling may import another sibling's implementation subtree. Shared format, contract, diagnostic, codec, and receipt nodes move upward to `common`; mutable runtime owners remain in their service/kernel tree.

Each populated cell uses `P:` for the surface public to the parent node and `S:` for the explicit surface public to the immediately consuming sibling. `—` means no access.

| Raw layer | `common/contracts/execution` | `common/structural/digest` | `common/structural/receipt` | `common/structural/invalidation` | `common/structural/parallel_commit` |
|---|---|---|---|---|---|
| Filesystem backend | P: `FsDriver` results/capabilities; S: bound handle descriptor to VFS | — | — | P: content-generation event; S: VFS invalidation input | — |
| VFS service | P: mount/handle facade; S: `open_for_execute` to loader | — | — | P: mount/namespace generations; S: loader invalidation event | P: mount mutation candidate; S: committed frozen lookup snapshot |
| Loader | P: admission/process facade; S: opaque generational token to the loader-owned consumer | P: verified content/manifest digests; S: digest identity to evidence | P: admission/process receipt; S: immutable candidate to evidence | P: loader-cache generation; S: cache invalidation observation | P: child-result candidate; S: scheduler commit receipt |
| Toolchain/image builder | P: closed image/profile/role manifest; S: external admission record to loader/image packer | P: source/compiler/sysroot/image digests; S: identities to admission/evidence | P: construction receipt; S: immutable candidate to evidence | P: build-cache dependency edge; S: invalidation key to target lane | P: target result batch; S: sorted aggregate receipt |
| Server capsule | P: lifecycle/protocol facade; S: admitted listener/worker capability | P: config/cert/content hashes; S: receipt identities | P: readiness/terminal/protocol receipt; S: candidate to evidence | P: config/trust/cache generation; S: worker snapshot invalidation | P: bounded worker result; S: deterministic lifecycle commit |
| WM capsule | P: action/scene/present facade; S: frozen scene to renderer | P: scene/frame/readback hashes; S: receipt identities | P: state/frame/restart receipt; S: candidate to evidence | P: service/scene generation; S: render invalidation | P: render result; S: presentation commit receipt |
| Evidence runner | P: bounded evidence candidate; S: candidate to evidence service | P: artifact hashes; S: hash index to validator | P: `SimpleOsEvidenceReceiptV1`; S: validator input only | — | — |
| Evidence service | P: ledger snapshot/transition; S: read-only projection to dashboard/release | P: validated receipt/artifact identities; S: ledger row identity | P: acceptance/rejection receipt; S: immutable audit projection | P: evidence freshness generation; S: dashboard invalidation | P: ledger transition candidate; S: committed transition receipt |

### Common relative tree-node paths

- `src/lib/common/contracts/execution/simpleos_executable_v1.spl` — the moved/extended single definition replacing `SimpleArtifactManifest`; `src/os/kernel/loader/artifact_manifest.spl` re-exports/adapts during migration and contains no second record/codec afterward.
- `src/lib/common/contracts/execution/simpleos_server_v1.spl`
- `src/lib/common/contracts/execution/simpleos_capability_v1.spl`
- `src/lib/common/structural/digest/hash256.spl` and `hash256_codec.spl` — existing canonical `Hash256` value/codec composed by every new contract; no new digest type or encoder.
- `src/lib/common/structural/receipt/simpleos_evidence_receipt_v1.spl`
- `src/lib/common/structural/invalidation/simpleos_generation_v1.spl`
- `src/lib/common/structural/parallel_commit/simpleos_ledger_commit_v1.spl`

These are contract nodes, not mutable service implementations. Existing digest, execution-profile, receipt, invalidation, transfer, and parallel-commit types shall be reused by composition. The manifest migration is atomic at the contract boundary: add shared definition/codecs and compatibility decoding, change all producers/consumers, remove the loader-private record/codec, then enable the duplicate-schema guard. No period may permit two authoritative encoders.

## Public surfaces to the next layer

### Filesystem to loader

`MountTable.open_for_execute(path, role)` returns a bounded owned file binding or typed failure. The binding includes mount ID/generation, backend handle, file identity/content generation, size, capabilities, and mount trust policy. The loader may read through it but cannot mutate the namespace or backend.

### Loader to per-ISA process entry

The common loader verifies mount policy, role, target, ABI, format, bounded ranges, dependencies, digest, signature, trust generation, and revocation against the same open handle. Because Simple classes and structs are value types, a copied `ExecutableImageHandleV1` is never authority. The loader now owns a bounded generational singleton capsule behind the canonical checked raw mutex; copied public owners carry only its epoch, and lock/unlock failure returns `SerializationUnavailable`. Shared `executable_image_prepare.spl` validation re-reads the retained handle, checks its digest and ELF/process-image equality, and enforces W^X, congruence, overflow, range aliases, entry, stack overlap, and page budgets without creating authority. `Scheduler.adopt_authenticated_executable_pid_v1` is the canonical privileged consumer: it accepts only registry owner/token coordinates, prepares and maps an x86_64 child result, then publishes the TCB, exact `ProcessVmSpace`, capability record, and ready entry synchronously through the same mutable `Scheduler.me` owner boundary as all existing task/ready mutations. It returns only PID plus receipt. No adoption-private mutex competes with that owner. A pure owner transition records `CommitIndeterminate` as queryable `Quarantined` state with authorization false. Pre-publication failure destroys the whole address space; post-publication close failure retains runnable-task ownership and quarantines only the retryable handle close. The older loader-owned map/release compatibility path remains non-authorizing and reports `legacy-loader-mapped-lease-not-scheduler-adoptable`. ARM64/RISC-V mapping is rejected before allocation because their address-space destroy paths do not yet reclaim mappings. Cryptographic token issuance and admitted runtime serialization evidence remain required before release admission.

### Construction to guest

The image builder produces a sorted embedded `ExecutableManifestV1`, closes/hashes the image, and produces a non-circular external `ExecutableAdmissionV1`. Separate compiler/interpreter/loader payloads remain distinct even if aliases intentionally share bytes. The guest never trusts host path names or a source marker.

### Server capsule to protocol siblings

The async HTTP owner at `src/lib/nogc_async_mut/http_server/`, DB owner at `src/lib/nogc_sync_mut/database/server/`, RESP owner at `src/lib/nogc_sync_mut/redis/server.spl`, and SSH owner at `src/os/apps/sshd/` consume the shared lifecycle/protocol facades. Sync HTTP becomes a policy/compatibility adapter; `src/os/apps/dbd/` becomes the freestanding adapter to the canonical DB owner; no adapter owns lifecycle or durable mutation state.

### WM capsule to renderer/input siblings

Input adapters publish bounded copied events to `WmService`; the service publishes frozen revisioned scenes to Engine2D; compositor/framebuffer adapters return readback/presentation receipts. No sibling receives mutable focus/window arrays.

### Evidence runner to service and release

Runners publish bounded immutable candidates only. The evidence service validates and commits the ledger. Dashboards and release gates consume read-only snapshots; neither may mutate or promote rows.

### Workers to parent owners

Server workers, build workers, render workers, and evidence runners receive immutable snapshots/capabilities and return bounded encoded results tagged with owner generation, request/region sequence, nonce, and hashes. The parent rejects stale/replayed/conflicting candidates and commits in deterministic order.

## Filesystem and authenticated execution capsule

### Portable core

`FsDriver.capabilities()` is intersected with requested capabilities; assigning the requested set without provider proof is forbidden. Mount and file generations increase monotonically and fail closed on exhaustion. Unmount returns `Busy` while owned handles/leases exist.

NVMe keeps one canonical mutable `NvmeDriver`; semantic sibling modules extend
that owner without duplicating controller, queue, reset, or generation state.
Generation advancement and queue-owner counters are bounded, and bulk I/O uses
subtraction-based LBA checks plus checked byte/DMA-address arithmetic. Durable
promotion remains closed because the current SimpleOS `spl_mutex_*` provider is
a documented no-op and therefore cannot serialize reset against write+flush.
The apparent `AtomicI64` alternative is also inadmissible: the SimpleOS
`rt_atomic_int_compare_exchange` provider is an ordinary load/conditional-store
single-core stub, while kernel IRQ/preemption controls are CPU-local and not
available as a user-driver cross-core exclusion port. The required next-layer
port is real acquire/release CAS over shared Simple-owned storage or a
scheduler-owned exclusion syscall.

FAT32, DBFS, and NVFS implement the same portable operations and errors. Backend extensions remain explicit:

- FAT32: selected UEFI FAT32 interoperability, bounded chain walk, dual-FAT consistency, LFN validation, dirty/error handling, flush ordering.
- DBFS: WAL-before-commit, bounded/checksummed replay, checkpoint/MVCC/namespace persistence.
- NVFS: real arena/device capacity and persistence; no process-global mirror as authority, no zero-capacity success, no silent unsupported offsets.

### Admission algorithm

1. Resolve and open once through `MountTable` with read+execute intent.
2. Snapshot mount/file/trust generations and effective capabilities.
3. Reject `noexec`, untrusted, oversized, unsupported, or stale bindings.
4. Parse bounded ELF/SMF metadata and validate ISA/ABI/role/ranges/dependencies.
5. Stream SHA-256 through the open handle; verify signed manifest and revocation epoch.
6. Register the verified open handle in the private generational loader owner and return an opaque token; close on every failure.
7. Stream bounded load ranges; never authorize cached bytes or a pathname.

### Cache and invalidation

Only path-resolution and verified metadata may be cached. Keys include mount ID/generation, namespace/content generation, file identity, size, role, target, digest, and trust generation. Create, write, truncate, replace, rename, delete, mount, unmount, remount, manifest update, key rotation, and revocation invalidate affected entries. Cached executable bytes never become authority.

## Toolchain and userland capsule

`platform_target_catalog.spl` gains a canonical SimpleOS userland triple separate from the kernel/bare-metal triple. Each target lane owns an isolated sysroot/artifact cache keyed by source, admitted compiler, target/ABI/features, role transform, sysroot manifest, linker flags, and schema.

The image contains distinct target-native Simple roles, Clang/Clang++, LLD, LLVM utilities, headers, CRT/startup objects, libc/OS runtime, compiler-rt, libc++, unwinder, and development libraries. Build tools may be hosted during construction, but acceptance starts only when target-native tools execute inside the guest and compile/link/run filesystem sources.

The primary-tool manifest is a frozen projection consumed by the capability ledger. `simpleos_primary_tool_manifest_v1.spl` declares the seven selected categories as a closed set and performs no source-tree discovery or runtime probing. Administration, archive/compression, networking, and package management remain `Unavailable`. Checksums (`/usr/bin/sha256sum`, `/usr/bin/md5sum`), text processing (`/usr/bin/grep`), and process monitoring (`/usr/bin/ps`) are `Blocked`: each names a real pure-Simple/VFS owner and one canonical filesystem identity, but none carries admitted target bytes, a digest, an evidence receipt, or a live loader-owned authority token. Their package projections feed one shared fail-closed launcher-result contract; its path/digest/receipt/authority-state fields are diagnostics and cannot authorize execution. Shell direct, alias, background, pipeline, and `which` paths cannot bypass these gates, and the generic launcher rejects the four exact canonical paths before process spawn. A tool becomes `Supported` or `Partial` only when its exact target artifact performs its representative operation and error path from all selected filesystems/architectures, the evidence owner admits the receipt, and the loader consumes its live token. Source ownership or unit vectors cannot promote it.

## Server capsule

`ServerLifecycleV1` states are `Created`, `Validated`, `Bound`, `Ready`, `Draining`, `Closed`, with typed `Failed` and `Cancelled`. It owns generation, quotas, cancellation, listener leases, readiness, and terminal receipt. HTTP, DB/RESP, and SSH are adapters; none owns a competing lifecycle.

`ProtocolCapabilityManifestV1` declares protocol/profile version, transport, TLS/ALPN, authentication, limits, operations, extensions, downgrade policy, and evidence identity. Advertisement requires a live transport/implementation probe. HTTP/3 is unavailable until QUIC transport, loss recovery, congestion control, stream lifecycle, QPACK, backpressure, and close semantics exist end-to-end.

Workers return bounded results. DB mutation stays with one durable owner. HTTP response caches include route/config/content/trust generations. Proxy pools and retries are bounded and invalidated on configuration/trust changes. SSH keys/credentials are configured authenticated resources and never hardcoded.

## Window-manager capsule

`WmService` owns window IDs/ownership, geometry, focus/z-order, input dispatch, lifecycle generation, and restart. The flow is:

`InputBackend` → bounded `HostInputEvent` → `WmService` → frozen revisioned scene → `Engine2dWmFrameExecutor` → compositor/framebuffer → readback receipt.

`DesktopShell`, compositor facades, host seams, `WmWorld`, z-order storage, and action appliers become adapters/projections; they cannot hold parallel lifecycle/focus/window authority. Presentation succeeds only after correlated scanout/readback. Missing devices, stale revisions, invalid handles, or failed readback cannot emit readiness/presented markers.

## Capability ledger and evidence

`SimpleOsEvidenceReceiptV1` is a bounded immutable candidate containing schema, source/image/binary/config hashes, target/ABI, firmware/board/accelerator, nonce, exact argv, ordered artifact hashes, capability observations, resource/performance samples, owner, and reviewer. The evidence service validates freshness, nonce, target, artifact existence/hash, required fields, and result semantics before an atomic ledger transition.

`SimpleOsCapabilityLedgerV1` is the sole mutable capability-status owner. Runners cannot mutate it. A blocked row retains reason, TODO, prerequisite, exact resume command, artifacts, owner, and final reviewer. QEMU system-emulation, native-host, and physical-board rows are three separate environment classes; no combined `physical/native` status exists.

The source implementation at `src/os/services/evidence/verifier_owner.spl` now keeps all trust-root, nonce, generation, challenge, verified-handle, admitted-row-expiry, and canonical ledger state behind one private canonical raw Mutex. Public values are registry references or ledger snapshots, never owner authority; conflicting initialization and duplicate nonce issuance linearize to one winner. Every unlock result is checked: failure permanently quarantines the owner, retains any already-applied mutation to prevent replay, and suppresses every success handle or ledger payload because its linearization is indeterminate. `artifact_snapshot.spl` re-hashes bounded source-manifest, image, binary, configuration, fixture, and ordered artifact bytes rather than accepting caller digest outcomes. A minted registry entry retains the SHA-256 of the complete canonical unsigned receipt, so consume cannot substitute a different internally valid receipt while replaying the same signature text and row key. `ledger_transition.spl` only prepares a non-authorizing value; consume validates the registry handle, constructs the next handle/admission/ledger roots off-root, then assigns all three under the same lock. Separate false release gates cover privileged boot trust-root ownership, service-owned campaign policy, and canonical freshness time, so first-writer structural initialization and copyable performance/time inputs cannot become authority. Cryptographic admission remains disabled until Ed25519 passes authoritative executable vectors and native constant-work review, so no verified handle is currently minted and caller booleans, prepared ledger values, or copied handles cannot promote a row. Self-hosted concurrent runtime evidence for this mutex path is still required before release admission.

## Current implementation boundary (2026-08-20)

- `src/os/kernel/fs/vfs_handle_table.spl` uses a bounded 4,096-slot generational table with O(1) lookup/release; stale handles cannot alias reused slots.
- `src/os/kernel/loader/executable_authority_registry.spl` owns a bounded checked-mutex slot capsule with opaque generation/nonce tokens, exactly-once commit/retrieval, deterministic exhaustion, generation retirement, and retryable close quarantine. Its mint/close leases are package-private. `src/os/kernel/loader/executable_admission_pipeline.spl` independently returns `CryptographicVerifierUnavailable`, so no production token is minted yet. `executable_load_plan_v1.spl` owns the pure bounded lifecycle model; `executable_image_prepare.spl` owns shared non-authorizing re-read/hash/ELF/process-image validation; `executable_load_consumer.spl` retains the non-adopting private map/release compatibility path. `scheduler_executable_adoption.spl` is the only path that may change `execution_authorized` to true, and only after exact token consumption and scheduler publication.
- `src/os/port/initramfs_validate.spl` performs bounded zstd/newc parsing, canonical SMF trailer validation, and exact `SYS/SIMPLETOOL.SDN` role/path/payload-digest binding. The packer requires an explicit target-native init artifact, a bounded single inventory, and pre-read newc sizing. Sequence-compressed zstd blocks are rejected; the packer emits raw/RLE blocks.
- The initramfs validator reaches CPIO through the minimal exported `cpio_parse_bounded`/`CpioEntry` surface and reaches SMF only through `smf_admit_explicit_simpleos_executable`; it does not depend on private SMF header representation.
- `src/os/port/guest_toolchain_execution_gate.spl` validates structural in-guest workflow continuity, but cannot return READY without cryptographically admitted evidence.
- `src/os/apps/dbd/dbd.spl` owns listener/lifecycle/WAL and per-session budget state and refuses network readiness until DBFS, boot credential, and TLS provisioning owners exist. One `DbdLiveClientSessionV1` owns the TLS fixed-ring stream, mutable auth owner, session budgets, and `DbdAuthenticatedRespIngressV1` fixed-ring command framer for an accepted connection; ingress/commit/reject/seal mutate those authoritative fields directly, so neither ring is copied per fragment or reply. `dbd_auth_ingress.spl` is its single mutable wire-credential owner: after TLS record authentication it incrementally recognizes bounded RESP AUTH bytes, hashes principal/credential bytes through its owned `DbdAuthSession`, and wipes owner-held auth material on every terminal path. After identity admission, `dbd_command_ingress.spl` advances one byte-domain framing state machine over decrypted RESP, identifies repeated AUTH before text conversion, wipes consumed ring storage, and materializes immutable text exactly once only for a complete non-credential frame passed to the canonical parser. The absent boot credential source and certificate/private-key/typed-entropy owner remain exact fail-closed blockers.
- `src/lib/common/net/tls_application_record_stream_v1.spl` is the single bounded TLS application-record framing owner shared by HTTP and DBD. One mutable fixed-ring owner accepts one-byte fragmentation without prefix recopying, exposes exact byte-work evidence, and advances receive sequence only through a generation-bound authenticated commit. HTTP removes a stream from its dictionary before mutation and reinserts it after commit; DBD mutates its live-session field directly, avoiding value/COW copies of the ring.
- `src/os/installer/image_package_payload_policy.spl`, `image_bounded_file_reader.spl`, and `image_builder_payloads.spl` admit only canonical ELF or canonical SMF-with-embedded-ELF executable payloads, reject bootstrap seed provenance, and default missing package bytes to blocked inventory rows. The hosted APIs do not expose a canonical no-follow open plus fstat plus bounded byte read on the same descriptor. The bounded-reader owner therefore returns `bounded-nofollow-fd-reader-unavailable` for every regular changeable host artifact instead of using a stat/read or subprocess snapshot race. Kernel, toolchain, build-stamp, and install-package inputs fail closed until that descriptor owner exists. Installer-generated content remains limited to exact `/SYS` metadata.
- Shell tool names route only to canonical guest absolute paths; diagnostic metadata is non-authorizing and exits 78.
- `MountTable.fsync` and `fdatasync` require the `DurableSync` capability. FAT32 now promotes it per mounted instance only after its device owner acknowledges a real flush, and sync orders dirty-cluster writeback before another acknowledged flush. NVFS arena/superblock recovery now shares one device owner and uses checksum-valid replicated commit records, but the mounted NVFS/NVFS-POSIX file paths remain fail-closed until wired to that owner. RamFS remains volatile.
- SSH session-channel admission is bounded and stateful at `ChannelTable`; duplicate local/remote IDs and full tables produce protocol `OPEN_FAILURE`, and only successful admission may update the session's active remote ID.
- `simpleos_performance_v1.spl` freezes the selected native workload budgets, percentile direction, stable ten-sample policy, identity fields, checked exact CV threshold, overflow checks, and exact five-percent metric/RSS regression rule. The bounded verified artifact set must contain the distinct fixture, binary, image, configuration, and baseline identities; per-repetition RSS samples are retained and the maximum is recomputed rather than trusted from a scalar claim. Accelerator identity remains separately bound. The contract validates receipts but supplies no live benchmark measurements.

These are fail-closed safety foundations, not AC-4–AC-17 completion. Backend durability, privileged execution, target-native artifacts, full protocols, physical/QEMU evidence, and runtime/performance campaigns remain release blockers.

## Ownership classification

| State/data | Owner | Boundary class |
|---|---|---|
| Driver/backend state | VFS/backend owner | handle/scoped loan |
| Mount namespace | `MountTable` | frozen lookup snapshot; owner commit for mutation |
| Executable manifest/admission | image/loader owner | frozen share/encoded payload |
| Executable image binding | private serialized loader capsules | x86_64 map/release owner exists; crypto issuance, scheduler lease transfer, non-x86 reclamation, and runtime concurrency evidence remain blocked |
| Process state | parent scheduler | child fresh result then owner commit |
| Server lifecycle/listener | `ServerLifecycleV1` owner | handle/lease; bounded result ingress |
| Protocol manifest | server capsule | frozen share |
| Window/focus/scene root | `WmService` | copied input, frozen scene, receipt result |
| Evidence candidate | runner | bounded encoded payload |
| Capability ledger | evidence service | parent-authoritative deterministic commit |

Raw pointers and unknown dynamic transport are forbidden at safe external boundaries. Unknown access/layout classifications are overlapping and conservative; they cannot authorize `noalias`, disjoint loans, transfer, or scheduling.

## Error model

Each capsule returns typed errors with stable codes and safe context:

- filesystem: invalid media, unsupported capability, stale handle, busy mount, durability/recovery failure;
- admission: noexec, untrusted, unsigned, revoked, digest mismatch, wrong role/ISA/ABI, malformed/range/dependency failure;
- process: map/entry/start/wait/reap/cancel/resource failure;
- lifecycle/protocol: invalid state, bind, quota, negotiation, framing, auth, timeout, backpressure, drain/close failure;
- WM: invalid handle/revision/input/geometry, missing backend, scanout/readback/restart failure;
- evidence: stale, nonce/target/hash/artifact/schema/semantics/reviewer failure.

Errors never include credentials, private keys, raw secret buffers, or unbounded peer input.

## Startup and hot paths

- Startup validates closed manifests once and caches only generation-bound metadata.
- Executable loading streams only declared ranges plus digest coverage; large LLVM images are never whole-file buffered.
- HTTP/DB/SSH request paths perform no full-tree scan, source compile, or per-request server spawn.
- WM uses bounded event ingress, revisioned dirty regions, and one render/present owner.
- Evidence publication indexes retained artifacts once; dashboard reads immutable projections.

Selected native budgets are defined in `doc/02_requirements/nfr/simpleos_complete_os_hardening.md`. Timings/counters cover admission, bytes/read calls, cache hits/invalidations, compile phases, lifecycle queues, requests, WM event-to-present, max RSS, and cleanup.

## Migration sequence

1. Move/extend `SimpleArtifactManifest` into the single shared `ExecutableManifestV1`, migrate all producers/consumers, delete the private record/codec, then land the remaining common contracts/codecs and capability/evidence owner without promoting capabilities.
2. Fix capability negotiation, generations, handle lifecycle, durability, and three-backend conformance.
3. Add authenticated open-handle admission and remove direct FAT32/host/registry authority.
4. Complete per-ISA mapping/entry and target-native Simple roles.
5. Complete full LLVM/Clang/sysroot and expanded userland.
6. Route HTTP/DB/SSH through one lifecycle and complete advertised protocols/security.
7. Collapse WM/input/render duplicates under `WmService` and prove presentation.
8. Run QEMU then physical campaigns, strict performance/soak/fuzz/duplication gates, and final verification.

## Consequences

### Positive

- One mutable owner per capability; staging and execution become impossible to conflate in the ledger.
- Filesystem execution becomes backend-neutral, authenticated, TOCTOU-resistant, and generation-safe.
- Per-architecture code is reduced to genuine ABI/device differences.
- Protocol and WM claims require live end-to-end probes rather than helper/source presence.

### Negative

- Existing FAT32, NVFS, HTTP, DB transport, WM, and evidence duplicates must be migrated and deleted.
- Full guest-native LLVM/C++ plus physical campaigns are large, hardware-dependent work and remain release blockers until proven.
- Strict performance, fuzz, and soak targets require stable runners and long campaigns.

### Neutral

- No new grammar is required. Visibility is enforced through tree-private modules, common contract extraction, facades, manifests, and review gates.
