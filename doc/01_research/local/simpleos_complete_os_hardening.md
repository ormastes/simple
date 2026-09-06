<!-- codex-research -->
# Local Research: SimpleOS Complete OS Hardening

## Scope and method

This research maps `.spipe/simpleos_complete_os_hardening/state.md` AC-1 through AC-18 to current source, tests, scripts, plans, and reports. Four lower-model read-only lanes covered toolchains, filesystems, servers, and OS/WM/tools; a fifth audited prior evidence. The primary Codex pass reconciled contradictions against current files and treated a newer explicit failure as authoritative over an older PASS claim.

## Current verdict

The repository contains substantial implementations for all requested areas, but the complete-OS claim is not currently supported. The authoritative umbrella report remains `STATUS: FAIL` because filesystem execution, target-native payload deployment, and in-guest toolchain execution are incomplete (`doc/09_report/verify_simpleos_filesystem_toolchain_servers.md:13-23,230-234`). The expected target-native binaries are absent at `bin/release/{x86_64,aarch64,riscv64}-unknown-simpleos/simple` in this worktree.

| Requested lane | Existing strength | Current blocking truth |
|---|---|---|
| x86_64/AArch64/RISC-V 64 | Boot scripts, target builders, QEMU specs, config profiles | No single complete three-architecture receipt matrix; several tests can skip; RISC-V real-firmware gate is firmware-only |
| FAT32/DBFS/NVFS | Shared `FsDriver`, concrete backends, broad unit/integration coverage | Executable loading remains FAT32-specific; backend semantics and durability evidence differ |
| Simple compiler/interpreter/loader | Payload roles, receipt parser, x86 loader paths | No three target-native binaries; AArch64 source says genuine EL0 execution is not yet proven |
| LLVM/Clang | Cross-build plans and staged artifacts | No guest-native Clang/LLD/sysroot compile-and-run receipt on any complete three-arch matrix |
| Primary tools | Package/launcher registries and many Simple utilities | Inventory mixes contracts, placeholders, and unproven target payloads; no three-FS launch matrix |
| Web/DB/SSH servers | Real HTTP/1.1, partial H2/H3, DB protocols, SSH v2 | Async TLS is unwired, H3 lacks QUIC, SSH has hardcoded default credentials, lifecycle is not unified |
| Window manager | Production service/framebuffer adapter and x86 evidence gates | Overlapping WM layers and false-success sites; current all-architecture structured+visual evidence is absent |
| Performance/duplication | Design targets and duplicate-check tooling | No institutionalized per-architecture baselines; known duplicated FS/WM/server seams remain |

## Existing filesystem and execution surfaces

- `src/lib/nogc_async_mut/fs_driver/ops.spl:16-139` defines the canonical `FsDriver` trait with lifecycle, I/O, namespace, sync, metadata, and capability operations using `Result<..., FsError>`.
- `src/lib/nogc_async_mut/fs_driver/instance.spl:37-200` provides enum dispatch across FAT32, NVFS, NVFS POSIX, RamFS, and DBFS; the large repeated dispatch arms are a duplication and maintenance hotspot.
- `src/lib/nogc_async_mut/fs_driver/mount_table.spl:201-299` implements longest-prefix mount resolution and virtual handle tracking.
- FAT32 is implemented by `src/lib/nogc_async_mut/fs_driver/fat32_core.spl:18-110,219-251` and its wrapper in `fat32_stub.spl:1-75` despite the stale “stub” name.
- DBFS persistence, replay, WAL, device blobs, namespace, and I/O live in `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:1-117,268-398,641-849,1078`.
- NVFS wrappers in `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl:1-87` and `nvfs_posix_driver.spl:1-42,279-363` delegate much hosted behavior to DBFS; the POSIX path also keeps process-global mirrors and text conversions.
- Legacy/parallel NVFS implementations remain under `src/os/services/nvfs/driver/fs_driver_impl.spl:146-217` and `src/os/services/nvfs/posix/fs_driver_impl.spl:31-116`.
- `src/os/userlib/fs.spl:1-70,203-347` exposes the user-facing IPC/raw-syscall facade for read, write, stat, readdir, mount, and unmount.
- `src/os/kernel/boot/boot_fs_mount.spl:93-111,136-268` probes FAT32/NVFS/DBFS through provider-neutral boot selection.
- Execution does not yet use that shared backend boundary: `src/os/kernel/loader/fs_exec_resolve.spl:1-49` hard-codes `simpleos_fat32_stream_open`; its path cache at `:59-119` has no invalidation contract.
- x86_64 has bounded and heap FAT32 streaming plus ring-3 entry (`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:13-185`). AArch64 and RISC-V bridges prepare payloads (`arm64_fs_exec_spawn.spl:69-99`, `riscv64_fs_exec_spawn.spl:12-29`), but DBFS/NVFS loader paths were not found.
- `scripts/check/check-simpleos-dbfs-root-qemu.shs:6-28,114-162` proves DBFS root reboot persistence and FAT32 non-regression while explicitly excluding DBFS-backed executable loading.
- Cross-ISA filesystem-exec specs exist under `test/03_system/os/qemu/sys_qemu_*_fs_exec_spec.spl`; `scripts/os/build_simpleos_fs_exec_probe.shs:4-147` recognizes x86 32/64, ARM 32/64, and RISC-V 32/64. Their presence is not a complete fresh PASS matrix.

## Toolchain and filesystem-resident programs

- The install receipt contract in `scripts/check/lib/simpleos-compiler-filesystem-receipt.shs:109-167` expects the canonical compiler/interpreter/loader roles and `/usr/bin/simple --version` evidence.
- `doc/03_plan/os/simpleos/in_guest_simple_toolchain_multiarch_plan.md:1` and `doc/07_guide/os/simpleos_llvm_toolchain.md:3` describe the open multi-architecture work rather than completed execution.
- x86 loader mechanics are real, but generic dispatch, fallback handling, and proof remain incomplete (`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:23-185`).
- A boot-mounted FAT32 live-caller gap is documented in `src/os/kernel/ipc/syscall_file.spl:248`; AArch64 loader comments at `src/os/kernel/loader/arm64_fs_exec_spawn.spl:69-99` do not claim genuine EL0 payload completion.
- The current `build/os/clang_static/bin/clang_static` is a tiny staged artifact, not sufficient evidence of target-native Clang. The current report explicitly lacks guest `ld.lld` and a guest compile/run (`doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md:13-16`).
- Valid firmware paths differ: x86 acceptance requires OVMF pflash plus GRUB EFI, AArch64 uses virt/EDK2 or its documented real firmware path, and RISC-V uses virt/OpenSBI. A direct `-kernel` smoke is not equivalent.

## Servers and protocol surfaces

- `src/lib/nogc_async_mut/http_server/server.spl:100-274` implements a master/supervisor and worker model with graceful drain. `worker.spl:119-273` owns listener, I/O driver, and connection maps.
- `src/lib/nogc_sync_mut/http_server/server.spl:49-202` refuses production plaintext unless an audited development capability is supplied and enforces request, header, body, iteration, timeout, and connection bounds.
- The async HTTP/1.1 parser in `src/lib/nogc_async_mut/http_server/parser.spl:52-195` is incremental and bounds request/header/body/chunked input before growth.
- HTTP/2 has ALPN and substantial frame/state machinery (`protocol_handler.spl:19-46`, `h2_connection.spl:1-25,167-218`), but continuation/padding/priority coverage, flow-control enforcement, and stream concurrency are incomplete; the sync implementation documents these gaps in `src/lib/nogc_sync_mut/http_server/h2_server.spl:14-31`.
- HTTP/3 currently provides framing/QPACK helpers but no QUIC/UDP transport, multiplexing, retransmission, congestion control, or accept loop (`src/lib/nogc_sync_mut/http_server/h3_server.spl:6-41,63-75`).
- Async TLS record helpers are explicitly not wired into receive/send paths (`src/lib/nogc_async_mut/http_server/worker.spl:1102-1161`). Compression and proxy/application handlers also retain placeholder/future paths.
- `src/lib/nogc_sync_mut/database/server/server.spl:1-17,78-106,547-586` implements a bounded sequential DB server capsule. Its closed line protocol has explicit 8 KiB messages, 64 arguments, 4096 rows, and 128-byte commit IDs (`protocol.spl:1-15,46-51,86-97`). Capability evaluation is deny-wins and credentials use digest-based constant-time comparison (`capability.spl:67-76,138-154`).
- `src/os/apps/dbd/dbd.spl:1-68,91-123,171-220` is the freestanding daemon; it uses bounded buffers and VFS WAL but falls back because a DBFS engine handle is not reachable.
- `src/os/apps/sshd/sshd.spl:406-658` implements SSH v2 negotiation, KEX, host keys, encryption/MAC, authentication, shell and exec routes, but sessions are synchronous and capped at 16. `ssh_packet.spl:18-20,74-79,129-146` bounds packets and checked strings.
- `src/os/apps/sshd/ssh_auth.spl:121-130` contains hardcoded `root/simpleos` and `user/password` defaults. This is a production security blocker.
- SSH filesystem resolution uses `/bin:/usr/bin:/usr/local/bin` and the same FAT32-oriented resolver (`src/os/kernel/loader/fs_exec_resolve.spl:46-120`); architecture launch remains shallow and target-specific.

## Architecture, tools, WM, and evidence

- `src/os/simpleos_config_matrix.spl:338-372` has explicit RISC-V desktop and FPGA serial profiles, but not one complete three-architecture capability ledger.
- x86_64/RISC-V boot specs under `test/system/qemu/os/boot/` can print `SKIP` when prerequisites are absent, which cannot satisfy fail-closed umbrella evidence.
- `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs:1-25,82-164` uses an actual FAT ESP and EDK2/AAVMF. `scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs:7-14,62-84` is intentionally firmware-only.
- The production WM is `src/os/services/wm/wm_service.spl:63-214,575-649`; the SimpleOS framebuffer/input adapter is `wm_host_2d_simpleos.spl:5-25,105-155,213-313`.
- x86 static preflight and live marker/QMP capture exist in `test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl:13-46` and `wm_input_qemu_smoke_spec.spl:309-390`, but known-linker and missing-QEMU branches prevent those sources alone from proving fresh live acceptance.
- `doc/04_architecture/ui/wm_host_platform_matrix.md:16-29,136-147,374-398` records six overlapping WM layers and 31 false-success sites across six clusters. Linux evidence is headless on this host; other graphical host rows remain environment-dependent.
- `src/os/x86_64_fs_loaded_tool_apps.spl:11-44`, `src/os/services/fs_apps/launcher_tool_apps.spl:47-119`, and `src/os/packages/os_packages.spl:190-236,282-300` define six filesystem tool-app contracts/paths, but `doc/08_tracking/test/x86_64_tool_apps_e2e_gap.md:1-15` says real in-guest process launch and target payloads remain missing.
- The broader utility tree includes placeholders or partial behavior for tools such as `free`, `df`, `gzip`, checksum, and ping paths; a generated inventory must distinguish implemented, partial, and unavailable tools.
- WM performance targets exist in `doc/05_design/wm_glass_theme_host_simpleos.md:383-385`, but `doc/08_tracking/todo/startup_perf_open_items_2026-08-18.md:8-25` says multi-sample p50/p95 admission is not institutionalized and the deployed `bin/simple` identity is still problematic.

## Reusable components

| Need | Reuse |
|---|---|
| Shared filesystem operations | `FsDriver`, `DriverInstance`, `MountTable`, `FsError` |
| Boot-time backend selection | `boot_fs_mount.spl` provider probes |
| Filesystem executable lookup | `fs_exec_resolve.spl` after removing FAT32 coupling and adding invalidation |
| Per-ISA process entry | existing x86_64/AArch64/RISC-V spawn bridges |
| Target receipt validation | `simpleos-compiler-filesystem-receipt.shs` |
| HTTP parsing/server lifecycle | async parser, supervisor/worker/drain surfaces |
| DB capability/policy | `DbServerCapsule`, deny-wins capability model, bounded protocol |
| SSH framing/security | checked packet/string parsing, KEX/host-key/auth modules |
| WM production owner | `wm_service.spl` plus `wm_host_2d_simpleos.spl` |
| Matrix publication | existing SimpleOS QEMU settings/admission/producer/collector scripts |

## Gaps that must remain visible

1. Reconcile the provisional `SimpleOsFileSystem` name to existing `FsDriver`/`DriverInstance`; do not create a competing filesystem stack.
2. Make executable resolution backend-neutral and define cache invalidation, mount trust, wrong-ISA, corruption, and no-host-fallback behavior.
3. Produce actual target-native Simple and LLVM/Clang/LLD/sysroot payloads, then prove booted compile-and-run on all three architectures.
4. Define a truthful primary-tool manifest and remove placeholder/contract-only entries from supported claims.
5. Wire TLS, complete the selected HTTP/2 profile, implement QUIC before advertising HTTP/3, remove hardcoded SSH credentials, and unify bounded server lifecycle evidence.
6. Collapse duplicate FS and WM owners, eliminate false-success sites, and quantify the performance effects.
7. Replace stale/static/skip-capable evidence with nonce-bound current guest receipts and keep every unavailable row blocked.

## Open questions

The implementation questions are expressed as selectable feature and NFR options in the companion requirement documents; no unresolved factual question blocks requirement selection.

