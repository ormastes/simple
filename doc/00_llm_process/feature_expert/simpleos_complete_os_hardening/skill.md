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
# Protocol honesty update (2026-08-21)

For web/SSH hardening, use `doc/07_guide/os/simpleos_server_protocol_status.md`.
Capability claims must flow through
`std.common.contracts.execution.simpleos_server_protocol_capabilities`; do not
infer reachability from framing modules or client SFFI declarations.
The TCP/TLS HTTP owner rejects unknown ALPN and H3 without H1 downgrade. SFTP
now routes bounded filesystem operations through the canonical capability-gated
VFS; fresh live OpenSSH/QEMU evidence remains blocked on an admitted runtime. Never
promote `check-simpleos-servers-qemu.shs` while it uses the Rust seed/password.
