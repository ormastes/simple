# SimpleOS Complete OS Hardening

This guide is the operator-facing index for the selected full SimpleOS hardening program. It does not advertise completion: the current authoritative verification remains FAIL until every required QEMU and physical x86_64, AArch64, and RISC-V 64 row is fresh and passing.

## Selected production profile

- strict shared FAT32/DBFS/NVFS core with explicit extensions;
- authenticated-only, open-handle executable loading;
- separate least-privilege Simple compiler/interpreter/loader payloads;
- full guest-native C/C++ Clang, LLD, runtime, and development profile;
- expanded Simple userland with truthful per-tool status;
- HTTP/1.1, HTTP/2, HTTP/3/QUIC, WebSocket/WebTransport, DB/RESP, and SSH v2 capability manifests;
- complete SimpleOS-native WM behavior without an EWMH/Wayland compatibility claim;
- strict native performance budgets, mission-critical robustness, static core bounds, deterministic parallel ownership, and zero unexplained subsystem duplication.

Authoritative requirements:

- `doc/02_requirements/feature/simpleos_complete_os_hardening.md`
- `doc/02_requirements/nfr/simpleos_complete_os_hardening.md`

Research:

- `doc/01_research/local/simpleos_complete_os_hardening.md`
- `doc/01_research/domain/simpleos_complete_os_hardening.md`

## Dependency order

1. capability/evidence ledger and canonical owners;
2. filesystem durability, authenticated backend-neutral exec, and invalidation;
3. per-ISA process execution and target-native Simple roles;
4. target-native LLVM/Clang and expanded userland;
5. bounded server lifecycle, complete protocols, and security;
6. production WM and structured/visual interaction evidence;
7. performance/duplication convergence, physical campaigns, and release verification.

## Evidence rule

Presence in an image proves staging only. A QEMU PASS must identify and execute the guest payload through the mounted filesystem. A physical PASS additionally identifies the board/native host and boot/download path. Host `bin/simple`, Rust seed binaries, fixed-command responders, placeholder apps, source scans, stale reports, and `SKIP` never prove a SimpleOS capability.

## Current implementation and blockers

The first safety wave now provides bounded generational VFS handles, backend-close rollback, strict initramfs role/path/digest/SMF validation with a required explicit target-native init artifact, structural guest-toolchain workflow validation, private mutex-serialized evidence and loader source owners, a lifecycle-owning fail-closed database service, canonical absolute-path shell routing, and tighter HTTP/WM ownership and cleanup. The initramfs loader boundary independently rejects noncanonical or duplicate newc paths, special entries, ambiguous hardlinks, and directory payloads; every compiler, interpreter, and loader binding must name an exact canonical role path, contain a bounded native ELF or executable SMF, and match the manifest SHA-256 digest. Evidence admission now re-hashes exact bounded source/image/binary/config/fixture/artifact byte snapshots and couples verified-handle consumption to the canonical ledger transition under one lock. Evidence crypto, loader token issuance/mapping, and concurrent runtime proof remain disabled or blocked, so none of these source changes alone authorizes a PASS.

The continuation wave closes canonical ELF/SMF parsing but keeps hosted installer file identity fail-closed. `image_bounded_file_reader.spl` returns `bounded-nofollow-fd-reader-unavailable` because neither `FileHandle` nor the older descriptor API provides no-follow open, fstat, and bounded bytes on one retained descriptor. Do not replace this with stat-then-read, `dd`, `cp`, or another path-reopening snapshot. It also makes SSH channel-open admission stateful, bounded, and wire-fail-closed; freezes exact native performance receipt budgets and the five-percent regression policy; and adds `DurableSync` as an honest VFS gate. Every current filesystem backend rejects sync because no implementation can yet prove a block-device flush/FUA barrier. The closed seven-category primary-tool manifest reports administration, archive/compression, networking, and package management unavailable, while checksum, text, and process rows are blocked behind exact target artifacts, loader tokens, and execution receipts. These are contract and safety improvements, not durability, tool, or performance evidence.

Release remains blocked by the admitted cryptographic verifier and privileged loader mapping consumer; real FAT32/DBFS/NVFS durability/recovery; three target-native SimpleOS role binaries; guest LLVM/Clang compile/run; expanded userland; TLS-backed HTTP/2 and HTTP/3/QUIC; DBFS/TLS/auth for `dbd`; complete SSH credential handling; production WM visual capture; all x86_64/AArch64/RISC-V QEMU/native/physical receipts; and performance/fuzz/soak evidence. The admitted self-hosted runtime is also required to execute the focused and release suites—Rust/bootstrap output is not substitute evidence.

## Canonical non-bootstrap acceptance

After the environment and admitted self-hosted `bin/simple` are ready, run:

```sh
sh scripts/check/check-simpleos-nonbootstrap-acceptance.shs
```

The entrypoint fails fast through static contract checks and the focused loader,
guest-toolchain, userland, DBD, SSH/SFTP, WM, multi-architecture filesystem,
and HTTP/2 specs. Its live phase then snapshots and collects signed evidence,
admits x86_64/AArch64/RISC-V QEMU bundles, runs the guest toolchain, server,
WM capture/readback, and performance/fuzz/soak matrix producers in dependency
order, and finally performs authentic umbrella receipt admission. Required
external provision inputs are reported by environment-variable name instead of
being silently skipped; inspect the exact order with `--print-graph`.

The runner only consumes an existing runtime, provisioned images, kernels, and
raw evidence: it does not build, bootstrap, select a seed, or fall back. Server
and WM producers are forced into their reuse-existing-artifact modes. Its final key/value lines and
`build/test-artifacts/simpleos-nonbootstrap-acceptance/summary.json` are the
machine-readable verdict. `--static-only`, `--focused-only`, and `--live-only`
support diagnosis; none weakens the default `--all` acceptance command.

Target-toolchain artifact candidates bind the canonical target ABI, exact
role-specific ELF/SMF output path, unique target/output argv pairs, independently
hashed build materials and rebuild bytes, plus a frozen whole-record digest.
Guest workflow candidates bind canonical role/alias ordering, deterministic
argv, role/alias manifest digest, and a whole-record digest without recopying
bounded output text. These are mutation-detection contracts only: deployment
remains `BLOCKED` until an authoritative producer signature and a loader-owned
consume-once authority token are verified against actual mounted-image bytes.

The filesystem sync unblock contract is tracked in
`doc/08_tracking/bug/simpleos_filesystem_durable_sync_barrier_gap_2026-08-20.md`.

## Wave 4 operator status (2026-08-21)

- FAT32 mount state now remains with one boot publication owner; FAT internals,
  NVMe DMA/lease/positioned I/O, and VFS dispatch/write responsibilities are
  split into bounded modules. This is ownership/static evidence, not three-FS
  durability or live execution evidence.
- x86_64, AArch64, and RV64 filesystem-server builds select authenticated media
  entries. Path-only spawn/capture adapters are rejected; each entry must
  consume loader-issued authority, wait, and collect. Complete live server
  receipts are still required.
- RV64 streams large FAT ELF ranges, bounds chain traversal and aggregate load
  bytes, enforces W^X, and rolls back its allocation checkpoint. Its legacy
  unauthenticated executor is fail-closed with
  `missing-loader-authority-token`.
- Architecture runtime shims are bounded single-owner units, and the three
  64-bit builders converge on `src/app/simpleos_tool/main.spl`. Build output is
  not proof that interpreter/compiler/loader launched from a mounted filesystem.
- Real x86_64 target Clang/LLD/llvm-ar files exist and pass structural static
  inspection. AArch64/RV64 provision remains artifact-dependent, and no live
  filesystem hello receipt is claimed.
- A fresh admitted host compiler and adjacent receipt exist at the path and
  digest recorded in `doc/07_guide/os/simpleos_llvm_toolchain.md`; only its
  four-argument environment ABI and 33-check core-C capsule are green. Because
  it lacks `test`/`check` and recovery produced no deployable release runtime,
  it does not unblock the full acceptance runner.

## Server-data namespace Phase A boundary (2026-08-22)

`std.common.contracts.os.server_data_namespace_v1` freezes the pointer-free V1
namespace, grant, lease, commit, and recovery records; the seven rights; the
five-state transition graph; and the architecture limits. Its pure decision
helpers validate shapes and compare a future kernel-table lookup result against
presented identities; caller-provided records never authenticate themselves.
They reject stale task/owner/lease generations, rights escalation, illegal
transitions, and capacity overflow without owning mutable kernel state. Syscall
ordinals 116–119 are renamed reservations only. The SDK
labels them explicitly non-callable, and no shared or ISA dispatcher enables
them. This is contract evidence, not a namespace, DBFS medium, syscall,
service-readiness, persistence, QEMU, performance, or memory claim. Those
claims remain blocked until Phases B–F and admitted-runtime evidence complete.
