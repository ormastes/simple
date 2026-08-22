# Feature Expert: SimpleOS Complete OS Hardening

## Role

Own the cross-subsystem knowledge for the selected x86_64, AArch64, and RISC-V
SimpleOS hardening program. Preserve fail-closed capability claims: source,
staging, structural receipts, QEMU fixed responses, and host tools never promote
a guest or physical capability row.

## Canonical owners

- Requirements/NFRs: `doc/02_requirements/{feature,nfr}/simpleos_complete_os_hardening.md`
- Architecture/design: `doc/04_architecture/simpleos_complete_os_hardening.md`
  and `doc/05_design/simpleos_complete_os_hardening.md`
- State: `.spipe/simpleos_complete_os_hardening/state.md`
- Filesystem namespace/dispatch: `MountTable`; backend state stays with each
  driver owner. `DurableSync` requires a real device flush/FUA barrier.
- Executable admission: canonical manifest/parsers plus a future serialized
  loader capsule; current registry/token APIs are inert and non-authorizing.
- Evidence: future serialized evidence-service capsule and sole capability
  ledger owner; current verifier is stateless and fails closed.
- SSH channels: mutable `ChannelTable`; server lifecycle: canonical lifecycle
  owner; windows/focus/scene: `WmService`.
- Performance policy: `simpleos_performance_v1.spl`; live native benchmark
  runners own samples and retained receipts.

## Current boundary

The repository has bounded generational VFS handles, strict initramfs
newc/zstd/SMF admission, bounded SSH channel-open failures, canonical guest-path
tool routing, and exact receipt-policy validation. No current filesystem backend
proves durable sync, no loader/evidence serialized authority exists, and no
target-native multi-architecture or physical/performance campaign is admitted.
Umbrella verification must remain FAIL.

## Evidence and update rules

Every PASS binds exact target/environment/filesystem/protocol, executable and
image hashes, argv, outputs, exit status, artifact hashes, owner, and reviewer.
Keep BLOCKED rows linked to a concrete tracker and resume condition. Update this
expert, the SimpleOS platform layer expert, architecture/design, guide, and
state whenever a canonical owner, blocker, evidence schema, or admission rule
changes. Never substitute the Rust seed or an unadmitted self-hosted runtime.

## RV64 stdout evidence batching (2026-08-22)

Authenticated RV64 stdout keeps the scheduler observation slot as canonical
64 KiB evidence and the architecture capture as a 4 KiB compatibility prefix.
The capture owner forwards ordered fixed 256-byte batches and must seal and
flush its tail before scheduler exit; stale/exited handles reject atomically.
The only nested lock edge is capture -> scheduler observation, whose batch
append has no callback or reverse capture dependency. Structural evidence
reduces scheduler commits from `N` to `ceil(N / 256)` but does not reduce
logical retention: the bound is 65,536 + 4,096 + 256 = 69,888 stdout bytes.
Keep `PERF-SIMPLEOS-002` open until an admitted Stage-4 optimizer and identical
fixture timing/RSS campaign is retained.

## Cross-architecture initial-stack construction (2026-08-22)

The canonical x86_64/AArch64/RV64 process-image path shares one ELF64LE,
16-byte-aligned initial-stack builder. It materializes each validated argv/envp
text once, exact-allocates the final frame, and serializes with indexed writes;
the process-image owner projects the accepted `sp` and bytes directly. Keep the
legacy x86 physical-memory emitter separate until freestanding byte-array writes
are proven safe. Public limits, error precedence, pointer order, auxv order,
terminators, and entropy ownership are compatibility requirements. Runtime
allocation/COW, timing, optimizer, and RSS evidence remains open under
`PERF-SIMPLEOS-003`.
# Protocol honesty update (2026-08-21)

For web/SSH hardening, use `doc/07_guide/os/simpleos_server_protocol_status.md`.
Capability claims must flow through
`std.common.contracts.execution.simpleos_server_protocol_capabilities`; do not
infer reachability from framing modules or client SFFI declarations.
The TCP/TLS HTTP owner rejects unknown ALPN and H3 without H1 downgrade. SFTP
now routes bounded filesystem operations through the canonical capability-gated
VFS; fresh live OpenSSH/QEMU evidence remains blocked on an admitted runtime. Never
promote `check-simpleos-servers-qemu.shs` while it uses the Rust seed/password.
# SSH filesystem-exec fail-closed boundary (2026-08-22)

The production SSH daemon has real filesystem launchers only on x86_64 and
RISC-V 64. Its x86_32, ARM64, ARM32, and RISC-V 32 target branches must return
the shared unavailable-launcher status `126`, never `0`. Keep `127` distinct
for a real command/PATH miss on an implemented launcher. Source contract coverage is
not target-native or QEMU execution evidence.

## Server credential image authority (2026-08-22)

Filesystem-server images require externally supplied KEY, DER X.509 CRT, and
Ed25519 PKCS#8 material. The image owner validates type, bounds, permissions,
format, and key match from private immutable snapshots; stages exact
`/SYS/SRVDB.{KEY,CRT,PK8,MAN}` paths; verifies their physical completed-image
bytes; and publishes by same-directory atomic no-clobber only after verification.
Never log secret bytes, overwrite an existing output, or treat generated test
credentials as deployment provenance. Windows staging remains fail-closed until
a no-reparse descriptor owner exists.

## Second-medium server-data contract boundary (2026-08-22)

The canonical architecture is
`doc/04_architecture/os/storage/simpleos_server_data_namespace_owner.md`.
Phase A owns only the scalar contract in
`src/lib/common/contracts/os/server_data_namespace_v1.spl` and reserved syscall
ordinals 116–119. Preserve the exact seven rights, five-state graph, and numeric
caps. A lease-shaped record is never self-authenticating: later authorization
must look it up by task ID, task generation, owner epoch, generation, and both
nonce words. Do not add SDK call wrappers, dispatcher branches, device/media
owners, or readiness claims until the unique owner and launcher grant boundary
land atomically. Source parity is not QEMU, persistence, timing, allocation, or
RSS evidence.

## Server-data media identity codec (2026-08-22)

`std.common.contracts.os.server_data_media_v1` is only the canonical bounded
512-byte identity codec and corrupt/duplicate/root-alias rejection policy. It
does not provision, publish, attach, mount, or admit media. The pure-Simple
provisioner remains fail-closed until the narrow bounded binary and atomic
no-replace host capability in
`doc/08_tracking/bug/simpleos_server_data_atomic_publication_primitive_2026-08-22.md`
exists. Never replace that missing boundary with whole-image text conversion,
overwrite rename, shell `ln`, or a readiness claim.

## Shared filesystem execute-open evidence (2026-08-22)

`MountTable.open_for_execute` is the sole shared execute-open seam for FAT32,
DBFS, and NVFS. Hosted integration coverage now checks real FAT32 and DBFS
bytes, exact stat size, backend identity, generation-current bindings,
positioned reads through the returned handle, close, and side-effect-free
missing paths; NVFS has the corresponding no-regression coverage. This proves
shared interface behavior only. It is not evidence of a native DBFS guest
spawn, mounted NVFS durability, target artifact admission, or three-architecture
QEMU execution.

## SimpleBox bounded-output policy (2026-08-22)

Filesystem-launched `echo` and `seq` must cap requested stdout at 65,536 bytes
before writing. `echo` retains bounded parts and joins once, avoiding quadratic
immutable-prefix copies. `seq` validates at most 64 input bytes with checked
decimal admission, rejects counts above 12,773 before calling the unchecked
libc accumulator, then requires the libc result to match and preflights exact
line bytes before its first requested output. Do not expose the existing
`dd`, `timeout`, or `chown` parser/core helpers as applets: they still lack the
filesystem, process/signal, and ownership authority required by those tools.
