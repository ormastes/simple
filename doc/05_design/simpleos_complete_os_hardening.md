<!-- codex-design -->
# SimpleOS Complete OS Hardening — Detail Design

## Design objectives

Implement REQ-001–REQ-020 and NFR-001–NFR-014 in dependency order. Every component below is either a frozen shared contract, one mutable owner, or a thin adapter. A new type may not duplicate an existing filesystem, loader manifest, lifecycle, WM, receipt, or invalidation schema.

## Shared records

### `ExecutableManifestV1`

This is the versioned successor and single definition of the existing `SimpleArtifactManifest` at `src/os/kernel/loader/artifact_manifest.spl:198`, not a parallel record. Implementation moves/extends that definition under `src/lib/common/contracts/execution/simpleos_executable_v1.spl`, migrates its `LaunchMetadata` projection and all codecs/callers, leaves a temporary re-export/decoder adapter in the loader file, then deletes the old record/encoder in the same wave.

Frozen sorted image record:

- schema/version, manifest ID, target triple/ABI/features, role, canonical path, optional `alias_of`;
- format, ELF class/machine/type, entry, `PT_INTERP` state, bounded load ranges;
- byte size, content SHA-256, dependency IDs/digests, required capabilities;
- source/compiler/sysroot provenance, signer/key ID, signature, trust/revocation epoch.

The embedded manifest never hashes its containing image. Image closure produces an external admission record.

### `ExecutableAdmissionV1`

Immutable decision record binding closed image hash, embedded manifest hash, kernel hash, trust root/epoch, target/firmware profile, compiler/source/config identities, file/mount generations, effective capabilities, decision, and typed rejection. It is not a mutable policy owner.

### `ExecutableImageHandleV1`

Immutable diagnostic record containing the already-open `FileHandle` identity, mount ID/generation, file identity/content generation, size, role, target/ABI, verified range table, digest/admission ID, trust generation, and read counters. It is not authority because Simple values are copyable. The loader capsule keeps live handles in private mutex-serialized generational state and exposes only epoch/token coordinates. Lock failure returns `SerializationUnavailable`; issue/close leases are package-private. No token is minted through the public admission path until cryptographic verification exists. Shared image preparation reads and re-hashes the exact retained handle, rebuilds and matches the ELF process image, and produces only copyable non-authorizing mapping inputs. The scheduler-owned `me` adoption method consumes the registry token exactly once, maps x86_64, commits the TCB and exact `ProcessVmSpace` through the canonical mutable scheduler owner, and returns only PID plus receipt. It has no separate mutex. Its pure owner-state transition makes an indeterminate commit queryable as `Quarantined` and never authorizes it. Failure before publication destroys the whole address space; failure to close the retained source after publication leaves the task authorized and the close retryable. The older loader-owned mapping receipt remains `execution_authorized=false` with reason `legacy-loader-mapped-lease-not-scheduler-adoptable`. ARM64/RISC-V fail before allocation until address-space destruction can reclaim them.

### `ServerLifecycleV1`

Owner state:

`Created → Validated → Bound → Ready → Draining → Closed`, plus terminal `Failed`/`Cancelled`.

Fields: lifecycle ID/generation, admitted executable ID, listener/credential/config leases, quotas, cancellation state, worker registry, bounded result inbox, readiness receipt, terminal receipt, counters/timings.

### `ProtocolCapabilityManifestV1`

Frozen versioned record for protocol/profile, transport, TLS/ALPN, auth/algorithms, operations, framing, request/stream/channel limits, timeout/backpressure policy, extensions, downgrade policy, implementation probe ID, and evidence identity.

### `SimpleOsEvidenceReceiptV1`

Bounded immutable candidate: schema, receipt ID, nonce, source/image/binary/config hashes, target/ABI/firmware/board/accelerator, exact argv, ordered artifact hashes, observed steps/outcomes, exit codes, performance/resource samples, timestamps, owner, reviewer, and signature.

### `SimpleOsCapabilityLedgerV1`

Single evidence-service owner. A row key is `(requirement, capability, target, environment, filesystem, protocol/profile)`; status is `Pass` or `Blocked`. Transitions require a validated fresh receipt or a complete blocker record. Status never derives from source presence.

## Filesystem design

### Portable-core capability negotiation

`effective = provider.capabilities().intersect(requested)`; required capabilities missing from `effective` return `Unsupported`. Mount entries store backend, options, mount generation, namespace generation, trust generation, open-handle count, and durability state.

### Open binding

`OpenFileBinding` contains mount/file generations and backend identity. Namespace mutations increment bounded generations. Execute-open is rejected on `noexec`, untrusted policy, missing capability, pending recovery, or incompatible backend state. Unmount returns `Busy` while a binding/lease survives.

### Durability

- FAT32: dirty data then metadata ordering, duplicate-FAT policy, bounded chain/LFN validation, explicit non-journaled crash boundary.
- DBFS: WAL record durability precedes commit success; bounded checksum replay; checkpoint advances atomically.
- NVFS: arena/device owns capacity and persistence; hosted compatibility is a thin adapter, never a global byte mirror.

Each backend implements deterministic fault points for corruption/power-cut campaigns and reports typed recovery outcomes.

## Executable admission and loading

### Algorithm

1. VFS resolves and opens one handle with execute intent.
2. Loader captures immutable mount/file/trust generations.
3. Loader parses bounded manifest/ELF/SMF headers through `pread`.
4. Validate role, target, ABI, format, ranges, dependencies, mount policy, and required capabilities.
5. Stream content digest; verify signer, signature, trust root, revocation, and admission binding.
6. Register the verified open handle in the private bounded generational owner; return only an opaque token and record admission timing/read counters.
7. The privileged architecture adapter atomically consumes that token, maps bounded ranges, applies ABI rules, starts the child, and returns a process handle.
8. Parent scheduler owns wait/reap/cancel and commits the bounded child result.

Every failure closes/releases exactly once. Loader cache keys bind all generations and trust identity. Invalidation events are sourced from the canonical namespace/trust owners.

The NVMe implementation is organized as one `NvmeDriver` class plus cohesive
method-extension modules for lifecycle/ownership, queue construction, sector
I/O, bounded bulk I/O, and probe/query work. Extensions carry no duplicate
mutable root. Queue submission failure is checked before completion waits;
bulk LBA, byte-length, and DMA slot arithmetic rejects overflow. The durability
adapter must continue returning `ResetNotSerialized` until SimpleOS provides a
real exclusion primitive or an enforced single-owner reset/I/O service. The
current diagnostic is
`missing-simpleos-atomic-compare-exchange-or-scheduler-exclusion`; it is checked
before durable read, write, and ordered flush submission.

## Target construction

### Target catalog

Kernel targets and SimpleOS userland triples are separate catalog fields. Canonical userland targets are selected once; every builder, manifest, sysroot path, and receipt derives from the catalog. RISC-V feature/ABI spelling is frozen before implementation and must match actual hardware/toolchain support.

### Role construction

Per-target isolated workspaces produce separate compiler, interpreter, loader, and dispatcher artifacts. Aliases may share bytes only through explicit manifest `alias_of`. A pure-Simple admitted compiler receipt is required; Rust seed or unsupported Stage 2/3 commands fail closed.

### LLVM profile

Build/install guest-native `clang`, `clang++`, `ld.lld`, selected LLVM tools, headers, CRT/startup objects, libc/OS runtime, compiler-rt, libc++, unwinder, and development libraries. Driver search uses the canonical target/sysroot layout. Guest tests invoke absolute filesystem paths and prove emitted ELF target/ABI before execution.

### Tool inventory

Generate one manifest from declared tool descriptors, never a source scan at runtime. A supported tool record includes implementation owner, artifact digest, capabilities, targets, filesystems, representative command, expected output/exit, error command, and evidence IDs. Partial/unavailable/blocked records are visible and cannot launch as supported.

## Server design

Production owners are explicit:

- async HTTP: `src/lib/nogc_async_mut/http_server/`;
- DB/native protocol: `src/lib/nogc_sync_mut/database/server/`;
- RESP: `src/lib/nogc_sync_mut/redis/server.spl`;
- SSHD: `src/os/apps/sshd/`.

`src/lib/nogc_sync_mut/http_server/` supplies hardened policy and becomes a compatibility adapter to the async production owner. During the freestanding DBFS migration, `src/os/apps/dbd/dbd.spl::DbdServer` is the single temporary owner of its listener FD, `ServerLifecycleV1`, engine, and bounded WAL state; one `DbdLiveClientSessionV1` owns each accepted connection's TLS fixed-ring stream, `DbdMutableAuthRequestOwnerV1`, session budgets, and `DbdAuthenticatedRespIngressV1`. The production hot path and focused tests mutate that live owner directly; no by-value DBD TLS ingest wrapper is exported. Auth ingress accepts only bounded RESP `AUTH principal credential` array framing after TLS authentication, keeps the credential in mutable byte storage, performs digest-only identity admission through its owned `DbdAuthSession`, and wipes auth storage on all exits. The authenticated command owner keeps incomplete RESP in a fixed mutable byte ring, advances its framing state once per byte, classifies repeated AUTH before conversion, and copies only a complete non-credential frame once into the canonical text parser. Taking or closing wipes owned ring bytes. Rejection is encrypted and consumes the existing four-attempt lockout budget. Durable mutations use bounded `ChecksummedBase64V1` journal records: canonical base64 preserves empty, whitespace, control-bearing, Unicode RESP values without line injection, and SHA-256 binds the exact encoded argument sequence before replay applies any command. Production replay admits J1 records only; unsigned pre-J1 scalar records fail closed. A future legacy importer must be an offline, one-shot migration owner that rewrites and verifies the complete journal before production replay. It cannot become Ready while DBFS, a boot mutable-credential source, and certificate/private-key/typed-entropy TLS owners are unavailable. The final migration moves this state behind the canonical DB service facade before `src/os/apps/dbd/` becomes a stateless adapter; the two owners must never be live concurrently.

### Lifecycle

Authenticated executable admission occurs before bind. The lifecycle owner creates listeners and immutable worker configuration, admits bounded work, and assigns monotonic request sequences. Workers return bounded encoded outcomes; the owner rejects stale generation/sequence/replay and orders observable commits. Drain stops admission, cancels or finishes bounded work, closes resources, and emits one terminal receipt.

### HTTP

- H1: incremental octet parser, ambiguous framing rejection, explicit limits/deadlines, keep-alive/drain.
- H2: ALPN/prior knowledge, continuation/padding, HPACK bounds, SETTINGS, per-stream/connection flow control, concurrency, GOAWAY.
- H3: UDP/QUIC connection IDs, loss recovery/congestion, stream lifecycle/flow control, QPACK, WebTransport, timeout/backpressure/close.
- TLS: owned encrypted stream from accept through send; no unwired helper path.
- WebSocket/compression/proxy: bounded frame/message/stream/pool/retry/cache state, hop-by-hop stripping, SSRF allowlists, generation invalidation.

### DB/RESP

One durable mutation owner consumes bounded native DB/RESP requests. Capability/policy decisions are deny-wins. Protocol manifest declares framing, auth, operations, transaction/isolation, limits, cancellation, extensions, and error mapping. MCP-shaped compatibility is an adapter, not another transport owner.

### SSH

Generated/authenticated host keys and configured credential providers replace hardcoded identities. Transport/userauth/connection layers enforce packet/auth/channel/window/output/rekey/timeout bounds. Shell and exec use authenticated filesystem admission; each session is a bounded owned task, not a synchronous global accept-loop stall.

## WM design

Input delivery is a parent-authoritative commit. The adapter submits a copied
`WmInputEvent` plus lifecycle generation and monotonic sequence. `WmService`
checks generation, nonzero/owned target, equality with the canonical focused
window, sequence freshness, committed-text size, and bounded queue capacity in
that order. Only then does it advance `last_input_sequence` and reserve one
queue slot. This ordering makes retry after a stale focus target deterministic.
`send_input_to_owner` is the production wrapper around this reservation; it
always releases the slot after synchronous IPC, while a send failure consumes
the sequence as an anti-replay fence and records `input-delivery-failed`.

Focus changes reorder the fixed-capacity bottom-to-top stack and damage both
old and new window regions. Owner death removes the window, exposes its damaged
region, and focuses the surviving stack top. Restart advances the lifecycle
generation and clears focus, damage, queues, input sequence, presentation
receipt, ECS windows, and owner registries. Host/manual evidence labels its
domain; unavailable live guest, architecture, or physical rows remain BLOCKED.

The shell configures damage bounds from the compositor framebuffer once.
Admission first rejects malformed/stale candidates, then clips each rectangle,
coalesces touching/overlapping regions transitively, and commits only if the
normalized result remains within 64 regions. Restart preflights generation
exhaustion and destroys the old IPC port before changing canonical state;
either teardown fails with the old owner intact or the reset commits fully.

`WmService` owns window identity/owner, geometry, focus/z-order, input dispatch, lifecycle generation, and restart. Raw input adapters submit bounded typed events. Accepted actions mutate once and publish an immutable revisioned scene. Renderer consumes a frozen scene, returns a generation/revision/frame receipt, and presentation succeeds only after scanout/readback correlation.

Create/focus/move/resize/redraw/close and owner-death cleanup are real service transitions. Pointer capture and keyboard focus are separate. Restart closes old ingress/resources, increments generation, rebuilds state, and requires a new first-frame receipt. Host seams and stores are adapters/projections only.

## Evidence and performance design

Evidence runners write immutable per-run directories under `build/evidence/simpleos/<target>/<environment>/<nonce>/`. The evidence service accepts a bounded immutable byte snapshot and independently SHA-256 re-hashes its source manifest, image, binary, configuration, performance-fixture selection, and ordered artifacts against the signed receipt. Public records and the pure prepared-ledger transition are copyable data, never owner authority; one private raw-Mutex capsule serializes roots, nonce history, generations, challenge slots, verified handles, admitted-row expiry, and the canonical ledger. Tables are bounded, expiry reuses slots without reusing nonces, and successful consume constructs all next roots before atomically spending the handle and publishing the exact ledger revision in the same critical section. A failed unlock marks a queryable permanent quarantine, preserves any mutation already applied, and returns a non-authorizing `serialization-indeterminate` result with no handle or ledger payload. Crypto verification is still fail-closed, so the capsule currently issues challenges but never mints a verified handle. Physical rows require board identity and boot/download path; QEMU rows retain firmware and accelerator/TCG classification.

Environment is an exact enum: `QemuSystem`, `NativeHost`, or `PhysicalBoard`. Physical visual evidence uses a board/profile-specific scanout path plus an identified HDMI/DP capture device or a board framebuffer/JTAG readback path. Its receipt correlates flashed image hash, board/CPU/display identity, capture-device identity, boot/download command, serial/SSH markers, scene/frame revision, framebuffer/readback hash, visual artifact hash, and reviewer. QMP is valid only for `QemuSystem`.

The primary-tool manifest is declaration-only and closed over seven categories. Administration, archive/compression, networking, and package management are `Unavailable`. Checksums (`/usr/bin/sha256sum`, `/usr/bin/md5sum`), text processing (`/usr/bin/grep`), and process monitoring (`/usr/bin/ps`) are `Blocked`: their real pure-Simple/VFS implementations and canonical launcher gates exist, while target bytes, digests, loader tokens, and admitted FAT32/DBFS/NVFS execution receipts do not. One shared launcher result contract carries the canonical path plus empty digest/receipt and explicit absent loader-authority state; this copied diagnostic record is never authority. Direct, alias, background, pipeline, `which`, and PATH paths must resolve through those gates. Promotion still requires an artifact digest, exact three-target and three-filesystem bindings, representative operation/error evidence, evidence-owner admission, and consumption of the live loader-owned token.

Performance receipts contain warmup, at least ten raw timing samples paired with raw RSS samples, p50/p95/p99/max, a recomputed maximum RSS, exact centered CV evidence, CPU/frequency/noise metadata, and applicability. Their bounded verified artifact set contains the distinct fixture, configuration, binary, image, and baseline identities. A read-only projection reports performance applicability and contract admission for dashboards, but carries no cryptographic or ledger authority and fails closed when runtime inputs are absent. The ledger rejects a native budget claim from TCG or a comparable claim with CV >5%.

Counters:

- FS: operations, bytes, flushes, recovery steps, cache hits/misses/invalidations.
- loader: admission/read/hash/map/start/wait/reap time, bytes/reads, rejection code.
- toolchain: phase times, cache reuse, output size, RSS.
- server: admission, queue depth/rejections, request/session latency, bytes, timeout/backpressure, cleanup.
- WM: event sequence, scene/frame revision, dirty/full work, scanout/readback, input-to-present.

## Error handling

All public functions return `Result<T, E>` with typed stable errors. Boundary decoders validate schema, size/count, identifiers, generations, ranges, enum values, hashes, and trailing bytes before allocation/retention. Unknown required fields/capabilities reject. Diagnostics redact secrets and bound peer-controlled text.

## Parallel ownership rules

- VFS, loader admission cache, scheduler, server lifecycle, DB mutation, WM, and ledger each have one owner.
- Children create fresh results; owners validate/commit.
- Boundary state is classified as copy, frozen share, owned move, scoped loan, handle, encoded payload, or lease.
- Bounded transport, generation/replay defense, cancellation, and exact-once close are mandatory.
- Unknown access/layout is overlapping and conservative; it cannot justify transfer, parallel scheduling, or alias metadata.

## Implementation order and gates

| Wave | Deliverable | Admission gate |
|---|---|---|
| 0 | Shared records/codecs, owner map, ledger validator | codec negative tests, no duplicate schemas |
| 1 | FS capability/generation/durability convergence | three-backend hosted conformance/corruption |
| 2 | Authenticated backend-neutral exec and ISA adapters | wrong-ISA/trust/stale-handle tests; QEMU FS exec |
| 3 | Target Simple roles, LLVM profile, expanded tools | guest absolute-path compile/link/run receipts |
| 4 | Unified server lifecycle and full protocols | protocol/malformed/fuzz/restart receipts |
| 5 | Canonical WM and UI evidence | structured transitions + correlated readback |
| 6 | Physical/perf/soak/dedup convergence | selected NFR budgets and release checker |

No wave promotes an umbrella PASS. Unimplemented shared helpers call `fail("UNIMPLEMENTED: <REQ-ID>")` until their real oracle exists.

## Bounded continuation status (2026-08-20)

- CPIO parsing now has a minimal exported entry/parser surface, while SMF exposes a narrow executable-admission facade. Initramfs code no longer imports private SMF headers or duplicates its format rules.
- SSH channel-open state is committed only by the mutable `ChannelTable` owner. Duplicate IDs and capacity exhaustion return exact wire failures; callers update active-channel state only after confirmation.
- `DurableSync` is vocabulary plus a VFS admission gate, not a claimed backend capability. FAT32, DBFS, NVFS, NVFS-POSIX, and RamFS return `Unsupported` until a real device flush/FUA owner and recovery evidence exist.
- The performance contract now has exact canonical native budgets and checked percentile/regression admission. Live per-architecture receipts remain required before REQ-14 can pass.

Backend dispatch is extracted into `mount_driver_dispatch.spl`, leaving
`mount_table.spl` at 736 lines. `dbfs_driver.spl` remains above the 800-line
maintainability limit; splitting its durability/replay owners is still a
release blocker rather than a license to expand it further.

## Wave 4 bounded-owner and evidence addendum (2026-08-21)

The FAT facade delegates cohesive operations to `_Fat32Filesystem` modules, but
the boot owner retains and publishes one mounted value. NVMe boot state and
leases feed dedicated DMA and positioned-I/O owners; VFS performs bounded
backend-neutral dispatch and mutation. These splits reduce file size and copy
hazards without creating another mount namespace.

Every x86_64/AArch64/RV64 server entry follows:

```text
authenticated media parse -> execute-open binding -> ISA task adoption
-> scheduler wait/collect -> bounded exit/server receipt
```

No path-only compatibility call may bypass that chain. RV64 loads program
ranges directly from FAT with bounded traversal, allocation checkpoint rollback,
aggregate-size and W^X rejection. The retained legacy symbol is a fail-closed
compatibility surface, not an executor.

Target build scripts select the common `simpleos_tool` closure and validate the
admitted builder plus target ELF. LLVM provisioning additionally validates
static target binaries, sysroot inputs, and receipt digests, then explicitly
records `execution_claim=false`. Promotion requires a fresh guest process to
open the exact mounted paths and produce the compile, link, run, protocol, and
exit oracles; static/source checks cannot fill those fields.
