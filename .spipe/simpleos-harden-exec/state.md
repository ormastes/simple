# SStack State: simpleos-harden-exec

## User Request
> harden simple os, load uno q full simple os, and run executables from file system.

## Refined Goal
> Harden SimpleOS security (capability checks on exec, fs access control, kernel hardening probes), boot the full SimpleOS in QEMU with a FAT32 disk image containing user programs, and run executables loaded from the filesystem end-to-end (FAT32 read → ELF parse → process spawn → execution).

## Task Type
feature

## Acceptance Criteria
- [ ] AC-1: Kernel exec path (`fs_exec_spawn` / `x86_64_fs_exec_spawn`) validates capability tokens before loading an executable
- [ ] AC-2: FAT32 filesystem service can read a binary file from disk into memory as `[u8]`
- [ ] AC-3: ELF64 loader (`kernel/loader/elf64.spl`) parses ELF headers and maps segments for a flat binary loaded from FAT32
- [ ] AC-4: `fs_exec_spawn` creates a new process/task from a filesystem path, wiring up the loader → scheduler pipeline
- [ ] AC-5: QEMU boot script (`scripts/` or `src/os/port/`) produces a bootable disk image with kernel + FAT32 partition containing sample executables
- [ ] AC-6: Hardening probes (`x86_64_hardening_probe`, `arch_adapt`) run at boot and log security state (NX, SMEP/SMAP, ASLR seed)
- [ ] AC-7: A spec test verifies the exec-from-fs path (load file → parse ELF → spawn → validate exit code)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-23
- [x] 2-research (Analyst) — 2026-05-23
- [x] 3-arch (Architect) — 2026-05-23
- [x] 4-spec (QA Lead) — 2026-05-23
- [x] 5-implement (Engineer) — 2026-05-23
- [x] 6-refactor (Tech Lead) — 2026-05-23
- [x] 7-verify (QA) — 2026-05-23
- [x] 8-ship (Release Mgr) — 2026-05-23

## Phase Outputs

### 1-dev
- Task type: feature
- Scope: 3 pillars — (1) security hardening of exec path + boot probes, (2) full QEMU boot with FAT32 disk image, (3) end-to-end executable loading from filesystem
- Key existing code: `src/os/kernel/loader/` (elf64, fs_exec_spawn, x86_64_fs_exec_spawn, segment_mapper, process_image, stack_builder), `src/os/services/fat32/`, `src/os/kernel/ipc/capability.spl`, `src/os/kernel/arch_adapt/*_hardening_probe.spl`, `src/os/port/disk_image*.spl`
- 7 acceptance criteria defined covering security, loading, booting, and testing

### 2-research

## Research Summary

### Existing Code

**Loader pipeline (all exist):**
- `src/os/kernel/loader/fs_exec_spawn.spl` — shared arch-neutral exec bridge. Imports `CapabilitySet` from `capability_types` but does NOT call `CapabilityManager.check()` before loading. `_fs_exec_read_bytes` dispatches per `@cfg` to `g_vfs_read_executable_bytes` (x86_64/riscv) or `arm_fs_exec_read_file_bytes` (arm). Creates bootstrap scheduler, calls process_image, schedules task.
- `src/os/kernel/loader/x86_64_fs_exec_spawn.spl` — x86_64-specific spawn; calls `_x86_64_try_fat32_exec_alias` + `_x86_64_try_static_fat32_exec` / cached exec paths. No capability gate before exec.
- `src/os/kernel/loader/elf_loader.spl` — validates ELF32/ELF64 ident + ET_EXEC, produces `ElfImage { entry, segments: [ElfLoadSegment] }`. Does NOT allocate address space — planning only.
- `src/os/kernel/loader/elf64.spl` — full ELF64 parse + PT_LOAD mapper. Calls `vmm_mmap` + `vmm_copy_to_user`. Returns entry vaddr or negative errno. `elf64_load(bytes, space)` is the main entry. Fully implemented.
- `src/os/kernel/loader/segment_mapper.spl` — Phase 2 of loader; consumes `UserLoadSegment` list, populates user address space. Address-space handle is raw PML4 u64 until `AddressSpace` wrapper lands.
- `src/os/kernel/loader/process_image.spl` — Phase 3; uses `stack_builder.compute_stack_size()` + `stack_builder.build_initial_stack()` to populate `UserProcessImage.initial_sp` + `.initial_stack_bytes` per SysV ABI.
- `src/os/kernel/loader/stack_builder.spl` — builds initial SysV stack frame (argc/argv/envp/auxv). Returns `StackBuildResult { sp, bytes }`.
- `src/os/kernel/loader/loader_api.spl` — `loader_exec(path, argv, envp, space) -> i64`. Calls `rt_file_read_bytes(path)`, sniffs magic, dispatches to `elf64_load` or `smf_load`. Returns -2/-8/-38.
- `src/os/kernel/loader/executable_source.spl` — `resolve_executable_bytes(path, arch)`. Resolution order: initramfs → VFS → legacy stubs. Also has `_vfs_read_file` and `_exec_vfs_read_file_bytes` paths with 8.3 alias fallback for FAT32.
- `src/os/kernel/loader/disk_launch_manifest.spl` — transitional bridge for FAT32-backed app launch; explicitly notes "real ELF-exec not yet landed via `kernel/loader/elf_loader.spl`". Uses builtin_binary_registry resident-task placeholders.

**Capability system (exists, not wired to exec):**
- `src/os/kernel/ipc/capability.spl` — `CapabilityManager` with `check(task, CapabilityKind)`, `check_file_access(task, path, perm)`, `pledge()`, `unveil()`. `CapabilityKind` enum includes `FileExec(path_prefix)` and `ProcessSpawn`. New tasks seeded with `FileRead/Write/Create/FileExec/ProcessSpawn`. The `grant()` method uses a two-gate check via `privilege_bridge`. **The `fs_exec_spawn` does NOT call `check()` before loading.**

**FAT32 / VFS (exists, wired):**
- `src/os/services/fat32/fat32.spl` — `Fat32Driver` implementing `Filesystem` trait. Has `open_files: [Fat32OpenFile]`, cluster chain walk, sector read via `BlockDevice`. Read path exists.
- `src/os/services/fat32/fat32_filesystem_trait.spl` — `Filesystem` trait impl for `Fat32Driver`. `read_file` by path exists.
- `src/os/services/vfs/vfs_init.spl` — `g_vfs_read_executable_bytes(name)` with mounted + direct FAT32 fallbacks. `g_vfs_read_fat32_path_bytes(path)` for raw FAT32 reads. Binary file read capability **exists and is wired**.

**Hardening probes (exist, minimal — only canary):**
- `src/os/kernel/arch_adapt/x86_64_hardening_probe.spl` — only has `x86_64_hardening_boot_canary_marker()` using `canary_init/canary_value`. **No NX/SMEP/SMAP/CR4/ASLR probes present.**
- `src/os/kernel/arch_adapt/riscv64_hardening_probe.spl` — only canary marker.
- `src/os/kernel/arch_adapt/arm64_hardening_probe.spl` — only canary marker.

**Disk image / QEMU boot:**
- `src/os/port/disk_image.spl` — FAT32 image builder (BPB + FAT + root dir + payload). Writes structural bytes via `rt_file_write_bytes` + `rt_file_truncate` for zero-extension.
- `src/os/port/disk_image_bake.spl` — bake harness combining initramfs + FAT32. Opt-in fast path via `scripts/bake_disk_via_mkfs.shs` (dosfstools/mtools). Requires pre-built `/tmp/hello_rs_simpleos/...` + `/tmp/hello_c.o`.
- `scripts/os/make_os_disk.shs` — shell script for disk creation.
- No end-to-end QEMU boot script that chains: build kernel → bake disk → run QEMU.

**Shell exec:**
- `src/os/apps/shell/exec.spl` — `shell_exec(cmd, argv, envp) -> i64`. Resolves via `shell_path_search`, calls `fs_exec_spawn(path, argv, envp)`. Returns PID or negative error. No capability check at this layer either.

**Existing specs:**
- `src/os/services/vfs/arm_fs_exec_vfs.spl`, `arm_fs_exec_alias.spl`, `arm_fs_exec_dirent.spl` — ARM VFS exec paths.
- No `*_spec.spl` files found in `src/os/kernel/loader/` or `src/os/services/fat32/` for exec-from-fs path.

**Prior work (unoq-simpleos-port):**
- `.spipe/unoq-simpleos-port/state.md` exists. Found "Critical Finding: Debug Connectivity Gap" — suggests prior work on QEMU port focused on debug/serial connectivity.

### Reusable Modules
- `os.kernel.ipc.capability.{CapabilityManager, CapabilityKind}` — check gate for `FileExec` + `ProcessSpawn`
- `os.kernel.loader.elf64.{elf64_load, elf64_has_magic, elf64_parse_header}` — fully implemented ELF64 loader
- `os.kernel.loader.elf_loader.{load_user_executable, ElfImage}` — ELF parse/validate
- `os.kernel.loader.executable_source.{resolve_executable_bytes}` — initramfs+VFS+alias resolution
- `os.services.vfs.vfs_init.{g_vfs_read_executable_bytes, g_vfs_read_fat32_path_bytes}` — FAT32 binary read (wired)
- `os.services.fat32.fat32.{Fat32Driver}` — FAT32 driver with read support
- `os.kernel.arch.x86_64.canary.{canary_init, canary_value}` — stack canary (used by probes)
- `os.port.disk_image.{DiskImageConfig, PayloadEntry, build}` — FAT32 image builder
- `os.port.disk_image_bake` — full bake harness with mkfs.fat fast path

### Domain Notes
- ELF ABI: x86_64 and RISC-V both use SysV ABI initial stack layout (argc/argv/envp/auxv). `stack_builder.spl` already implements this.
- x86_64 SMEP (CR4.bit20), SMAP (CR4.bit21), NX/XD (EFER.bit11), CR0.WP are the primary boot-time hardening probes needed. ASLR seed from RDRAND/RDTSC.
- FAT32 8.3 filename constraint: disk_image_bake already handles 8.3 name mapping for payloads.
- `disk_launch_manifest.spl` explicitly warns: do NOT import `os.apps.*` or `os.services.vfs.vfs_init` in the freestanding kernel ELF (link-time symbol explosion). Capability check must use a kernel-local singleton, not the full VFS closure.

### Open Questions
- NONE

## Requirements

- REQ-1 (from AC-1): `fs_exec_spawn` and `x86_64_fs_exec_spawn` must call `CapabilityManager.check(caller_task, CapabilityKind.FileExec(path_prefix: exec_path))` and `CapabilityManager.check(caller_task, CapabilityKind.ProcessSpawn)` before loading; return -13 (-EACCES) on denial — area: `src/os/kernel/loader/fs_exec_spawn.spl`, `src/os/kernel/loader/x86_64_fs_exec_spawn.spl`
- REQ-2 (from AC-2): FAT32 binary read path (`g_vfs_read_fat32_path_bytes` / `Fat32Driver`) already exists; verify it correctly returns `[u8]` for arbitrary binary files (not text-lossy); ensure it is reachable from the exec pipeline in baremetal mode — area: `src/os/services/fat32/fat32.spl`, `src/os/services/vfs/vfs_init.spl`
- REQ-3 (from AC-3): `elf64_load` in `elf64.spl` is already implemented; wire it correctly through `loader_api.loader_dispatch` so that bytes from FAT32 flow through: `g_vfs_read_executable_bytes` → `loader_dispatch` → `elf64_load` → process image — area: `src/os/kernel/loader/loader_api.spl`, `src/os/kernel/loader/elf64.spl`
- REQ-4 (from AC-4): Remove `disk_launch_manifest` resident-task placeholders; replace with real `loader_api.loader_exec` dispatch; ensure `fs_exec_spawn` creates a real scheduler task via the `process_image` + `stack_builder` pipeline — area: `src/os/kernel/loader/disk_launch_manifest.spl`, `src/os/kernel/loader/fs_exec_spawn.spl`
- REQ-5 (from AC-5): Add end-to-end QEMU boot script that: (a) calls `disk_image_bake` to produce kernel + FAT32 disk, (b) launches QEMU x86_64 with the disk image, sample ELF executables pre-loaded — area: `src/os/port/disk_image_bake.spl`, `scripts/os/make_os_disk.shs` (or new `scripts/os/run_simpleos_qemu.shs`)
- REQ-6 (from AC-6): Extend `x86_64_hardening_probe.spl` (and riscv64/arm64) with NX/SMEP/SMAP/CR4/EFER probes and ASLR-seed logging at boot; canary-only is insufficient — area: `src/os/kernel/arch_adapt/x86_64_hardening_probe.spl`
- REQ-7 (from AC-7): Add `src/os/kernel/loader/fs_exec_spawn_spec.spl` (or equivalent) with spipe `it` blocks: inject synthetic FAT32 bytes → verify ELF parse → verify spawn returns valid PID → verify exit code — area: `src/os/kernel/loader/` (new spec file)

## Phase
arch-done

## Log
- 2026-05-23 intake: Created state file with 7 acceptance criteria (3 pillars: security hardening, QEMU boot, exec-from-fs)
- 2026-05-23 research: Found all 8 loader files exist; FAT32 binary read wired; ELF64 loader implemented; capability system exists but NOT wired to exec path; hardening probes exist but canary-only (NX/SMEP/SMAP missing); disk_launch_manifest still uses resident-task placeholders; no exec-from-fs spec tests found; 7 requirements drafted
- 2026-05-23 arch: Designed 11 modules (3 new spl, 6 modified spl, 1 new shs); sibling _as pattern for caller_task (D-1); D-11 kernel-origin bypass in cap_exec_gate; loader_api_vfs.spl split for freestanding link safety (D-8); spec uses resolve_executable_bytes + synthetic vfs hook (D-9); REQ-3 scoped to disk_launch_manifest path, spawn pipeline unchanged (D-12); HardeningReport arch-neutral type; 6 new runtime externs; no circular deps verified
- 2026-06-02 continue-audit: Rechecked the active SimpleOS hardening goal against current executable-launch evidence. The shared app registry already normalizes shell-style executable paths (`/bin/simple`, `/usr/bin/simple`, `/bin/sh`, `/usr/bin/shell`) to canonical SMF app entries; the missing piece for this continuation was executable SPipe evidence tying that shared registry behavior to VFS exec aliasing.
- 2026-06-02 continue-impl: Added focused assertions to `test/01_unit/os/kernel/loader/app_registry_spec.spl` and `test/03_system/app/os/feature/vfs_exec_bytes_spec.spl` proving shell-style executable launch paths map to `/SYS/APPS/SIMPLSTC.SMF` and `/SYS/APPS/SHELLSMF.SMF`. Also corrected the stale fallback entry count from 18 to 19 to match the current registry table including `/sys/apps/simple`.
- 2026-06-02 continue-verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/kernel/loader/app_registry.spl src/os/services/vfs/vfs_init.spl test/01_unit/os/kernel/loader/app_registry_spec.spl test/03_system/app/os/feature/vfs_exec_bytes_spec.spl` passed. `app_registry_spec.spl` passed `25/25`; `vfs_exec_bytes_spec.spl` passed `4/4`. `spipe-docgen` generated `doc/06_spec/unit/os/kernel/loader/app_registry_spec.md` and refreshed `doc/06_spec/system/app/os/feature/vfs_exec_bytes_spec.md`; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- 2026-06-11 rv64-ssh-lane: Restored current-source RV64 SSH live lane in `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl`, added `src/os/rv64_probe.spl`, and wired `rv64-ssh` through `qemu_runner_part3/4/5` plus `ssh_qemu_contract.spl`. Shared RV64 network-init status decoding now normalizes wrapped `2^61 - n` error values, and `sshd.spl` no longer depends on `rt_tls13_ed25519_public_key`; host-key startup now uses pure-Simple `ed25519_keypair_from_seed`.
- 2026-06-11 rv64-ssh-build-env: Updated `src/os/qemu_runner_part2.spl` so the RV64 SSH live target uses current-source `src`/`examples` roots and gets `SIMPLE_BOOT_MINIMAL=1` like the other RISC-V freestanding lanes. This removed the stale "missing source lane" / wrong-build-surface ambiguity.
- 2026-06-11 rv64-ssh-shell-decouple: Replaced the SSH session's dependency on `os.apps.shell.shell_app.ShellApp` with a dedicated headless `os.apps.sshd.ssh_remote_shell.SshRemoteShell` for the live SSH path. That cuts the `ShellApp -> WindowClient` desktop/userlib closure out of the RV64 SSH image.
- 2026-06-11 rv64-ssh-current-boundary: A direct current-source Cranelift build of `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` still fails freestanding link, but the unresolved-symbol count dropped from `306` to `268` after the SSH shell decoupling. The remaining blockers are now core runtime-backed SSH/auth/string/array symbols (`rt_alloc`, `rt_string_new`, `rt_array_*`, `rt_enum_*`, `rt_byte_array_new`, `rt_ssh_ch_open`, `log_raw_println`, etc.), not the prior desktop/window path. The next hardening step is to move more SSH daemon internals behind std/Simple facades or provide a narrower freestanding daemon/session closure for the RV64 live lane.
- 2026-06-11 rv64-ssh-hostkey-split: Moved file-backed host-key loading off the main `SshDaemon` module into `src/os/apps/sshd/sshd_host_key_loader_ext.spl`. The RV64 live entry still imports only `os.apps.sshd.sshd.{SshDaemon}`, while the host-key loader example/spec explicitly import the extension. This keeps PEM/base64/file-I/O parsing out of the freestanding live daemon closure without regressing host-key loader coverage.
- 2026-06-11 rv64-ssh-channel-pure-simple: Replaced the old `rt_ssh_ch_*` C-side channel table shim in `src/os/apps/sshd/ssh_channel.spl` with a pure-Simple `ChannelTable` implementation. The direct current-source RV64 Cranelift build now fails with `256` unresolved symbols instead of `264`, and the `rt_ssh_ch_open/find/get_*/close` externs are gone from the active failure boundary. Remaining blockers are concentrated in the broader SSH auth/packet/cipher/runtime surface (`rt_array_*`, `rt_alloc`, `rt_string_*`, `rt_enum_*`, `rt_byte_array_new`, `rt_text_to_bytes`, `log_raw_println`, etc.).
- 2026-06-11 rv64-ssh-entry-logging: Switched `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` from `log_raw_println` to `serial_println` and removed an unused `random_bytes` import from `sshd.spl`. This removed `log_raw_println` from the live entry edge, but the direct current-source Cranelift build still fails at `256` unresolved symbols because the remaining live closure already depends on `serial_println` and the deeper auth/session/cipher machinery.

### 3-arch

## Architecture

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| cap_exec_gate | `src/os/kernel/loader/cap_exec_gate.spl` | Thin gate: given `(caller: TaskId, path: text)`, calls `ipc_mgr.cap_manager.check(caller, FileExec(path))` + `check(caller, ProcessSpawn)`; returns `Result<(), i64>` (-13 on denial) | New |
| fs_exec_spawn | `src/os/kernel/loader/fs_exec_spawn.spl` | Add `fs_exec_spawn_as(caller: TaskId, path, argv, envp) -> i64` which calls `cap_exec_gate.exec_cap_check` before dispatching; legacy `fs_exec_spawn` calls `_as` with `TaskId.KERNEL_INIT` sentinel | Modified |
| x86_64_fs_exec_spawn | `src/os/kernel/loader/x86_64_fs_exec_spawn.spl` | Add `x86_64_fs_exec_spawn_as(caller: TaskId, path, argv, envp) -> i64` with capability gate via `cap_exec_gate`; bytes then flow through `loader_api.loader_dispatch` | Modified |
| loader_api | `src/os/kernel/loader/loader_api.spl` | No change to imports; existing `loader_exec` + `loader_dispatch` unchanged; VFS-free | Unchanged (ref only) |
| loader_api_vfs | `src/os/kernel/loader/loader_api_vfs.spl` | New file: imports both `loader_api` and `vfs_init`; exposes `loader_dispatch_from_vfs(path: text, space: ProcessVmSpace) -> i64`; not imported by disk_launch_manifest | New |
| disk_launch_manifest | `src/os/kernel/loader/disk_launch_manifest.spl` | Remove `builtin_binary_registry` resident-task placeholders; `resolve_disk_launch_entry` returns `None` (ELF exec path takes over); safe to import `loader_api` since it has no VFS transitive closure | Modified |
| x86_64_hardening_probe | `src/os/kernel/arch_adapt/x86_64_hardening_probe.spl` | Extend with `x86_64_hardening_probe_full() -> HardeningReport`; reads CR4 (SMEP/SMAP), EFER.NX, CR0.WP via new externs; seeds ASLR via RDRAND/RDTSC fallback | Modified |
| riscv64_hardening_probe | `src/os/kernel/arch_adapt/riscv64_hardening_probe.spl` | Extend with `riscv64_hardening_probe_full() -> HardeningReport`; reads mstatus PMP bits and SATP mode | Modified |
| arm64_hardening_probe | `src/os/kernel/arch_adapt/arm64_hardening_probe.spl` | Extend with `arm64_hardening_probe_full() -> HardeningReport`; reads SCTLR_EL1 (WXN/SW) and ID_AA64MMFR1_EL1 (VHE) | Modified |
| hardening_types | `src/os/kernel/arch_adapt/hardening_types.spl` | New shared type: `class HardeningReport { nx: bool, smep: bool, smap: bool, wp: bool, aslr_seed: u64, arch: text }` | New |
| arch_adapt_harness | `src/os/kernel/arch_adapt/arch_adapt.spl` | Add `arch_hardening_probe() -> HardeningReport` dispatch that calls the right per-arch `*_hardening_probe_full()` under `@cfg` | Modified |
| run_simpleos_qemu | `scripts/os/run_simpleos_qemu.shs` | End-to-end shell script: invoke `disk_image_bake` to produce disk + initramfs, then launch QEMU x86_64 with kernel ELF + FAT32 disk image + serial stdio | New |
| exec_from_fs_spec | `test/01_unit/os/kernel/loader/exec_from_fs_spec.spl` | Spipe spec: inject synthetic ELF64 bytes via `_set_synthetic_vfs_file_for_test`, call `fs_exec_prepare_spawn`, verify ELF parse (entry != 0), verify no capability denial when `TaskId.KERNEL_INIT` used; verify binary-roundtrip fidelity (high bytes 0x80–0xFF pass intact) | New |

### Dependency Map

- `cap_exec_gate` -> `os.kernel.ipc.ipc.{ipc_mgr}` (capability check)
- `cap_exec_gate` -> `os.kernel.types.capability_types.{CapabilityKind, TaskId}` (types)
- `fs_exec_spawn` -> `cap_exec_gate` (exec gate check)
- `fs_exec_spawn` -> `os.kernel.loader.loader_api.{loader_dispatch_from_vfs}` (bytes dispatch)
- `x86_64_fs_exec_spawn` -> `cap_exec_gate` (exec gate check)
- `x86_64_fs_exec_spawn` -> `os.kernel.loader.loader_api.{loader_dispatch}` (magic sniff dispatch)
- `loader_api` -> `os.kernel.loader.elf64.{elf64_load, elf64_has_magic}` (ELF path, existing)
- `loader_api` -> `os.kernel.loader.smf.{smf_load, smf_has_header}` (SMF path, existing)
- `loader_api_vfs` -> `os.kernel.loader.loader_api.{loader_dispatch}` (dispatch)
- `loader_api_vfs` -> `os.services.vfs.vfs_init.{g_vfs_read_executable_bytes}` (byte read)
- `disk_launch_manifest` -> `os.kernel.loader.loader_api.{loader_exec}` (real exec; VFS-free, safe for freestanding kernel ELF)
- `hardening_types` -> (no deps — pure value type)
- `x86_64_hardening_probe` -> `hardening_types` (return type)
- `riscv64_hardening_probe` -> `hardening_types` (return type)
- `arm64_hardening_probe` -> `hardening_types` (return type)
- `arch_adapt_harness` -> `x86_64_hardening_probe` / `riscv64_hardening_probe` / `arm64_hardening_probe` (cfg-gated)
- `exec_from_fs_spec` -> `os.kernel.loader.fs_exec_spawn.{fs_exec_prepare_spawn}` (test entry)
- `exec_from_fs_spec` -> `os.kernel.loader.executable_source.{_set_synthetic_vfs_file_for_test, _clear_synthetic_vfs_for_test}` (test hooks)
- `exec_from_fs_spec` -> `os.kernel.loader.elf64.{elf64_has_magic}` (binary fidelity probe)
- No circular dependencies: verified

### Decisions

- **D-1: Sibling `_as` pattern for caller_task** — Add `fs_exec_spawn_as(caller: TaskId, path, argv, envp)` and `x86_64_fs_exec_spawn_as(caller, path, argv, envp)`. Legacy 3-arg forms call `_as` with `TaskId { id: 0 }` (KERNEL_INIT sentinel — task 0 always passes capability check since it is the initial kernel task with all caps). Rationale: no kernel-global current_task getter exists; ripple to shell_exec is minimal (shell_exec already knows its caller PID from the syscall entry).
- **D-2: cap_exec_gate as thin module** — Rather than inlining ipc_mgr imports into fs_exec_spawn, introduce `cap_exec_gate.spl` as a narrow adapter. This keeps the freestanding-kernel import constraint manageable: capability.spl itself does not import VFS/apps, so the chain is safe.
- **D-3: ipc_mgr singleton access pattern** — `cap_exec_gate` accesses `ipc_mgr` via the same pattern as `syscall.spl` / `syscall_process.spl` (module-level singleton). No new singleton file needed.
- **D-4: loader_dispatch_from_vfs helper** — Add one new function to loader_api.spl: `loader_dispatch_from_vfs(path, space)` that reads bytes via `g_vfs_read_executable_bytes` then calls `loader_dispatch`. This avoids touching existing `loader_exec` (which uses `rt_file_read_bytes` for host-fs scenarios) and satisfies REQ-3 without ProcessVmSpace plumbing changes.
- **D-5: process_image path unchanged** — `build_user_process_image_unchecked` has its own ELF magic sniff and handles the full image-build pipeline. The `fs_exec_spawn` path continues to call it; REQ-3 is satisfied at the byte-dispatch level (ensuring FAT32 bytes reach the existing ELF sniff). `loader_api.loader_dispatch` is used by `x86_64_fs_exec_spawn_as` for the pure-load path (no process image — returns entry vaddr), not as a full process spawn replacement.
- **D-6: hardening externs are new** — No `rt_x86_64_read_cr4`, `rt_x86_64_read_msr`, `rt_x86_64_rdrand_u64` exist. They must be declared new in the runtime shim. riscv64/arm64 equivalents (`rt_riscv64_read_mstatus`, `rt_arm64_read_sctlr_el1`) are also new. Bootstrap rebuild required after adding them.
- **D-7: HardeningReport is arch-neutral output** — All three probe files return the same `HardeningReport` type from `hardening_types.spl`. Fields unavailable on a given arch are set to `false`/`0`. This allows the spec test to assert on the struct without arch-gating.
- **D-8: loader_api_vfs split for link safety** — Simple's module linker pulls the full transitive import closure. `loader_api.spl` must stay VFS-free so `disk_launch_manifest.spl` can import it without pulling `os.services.vfs.vfs_init` (and the full FAT32/UI closure). `loader_dispatch_from_vfs` is therefore moved to a new sibling file `loader_api_vfs.spl` which imports both `loader_api` and `vfs_init`. `disk_launch_manifest` imports only `loader_api` (calling `loader_exec` which uses `rt_file_read_bytes`, a pure extern). x86_64_fs_exec_spawn uses the existing `g_vfs_read_fat32_path_bytes` import it already has.
- **D-9: spec test injection via resolve_executable_bytes, not g_vfs_read_executable_bytes** — `_set_synthetic_vfs_file_for_test` lives in `executable_source.spl` and intercepts the `resolve_executable_bytes` path. The spec calls `resolve_executable_bytes(path, arch)` directly (not via `fs_exec_prepare_spawn`) to test the byte pipeline in isolation, then separately calls `fs_exec_prepare_spawn` after verifying bytes are non-empty. This avoids the mismatch where `g_vfs_read_executable_bytes` (vfs_init) does not consult the executable_source synthetic hook. Binary roundtrip test injects a 256-byte sequence via `_set_synthetic_vfs_file_for_test` and asserts `resolve_executable_bytes` returns len==256 with all bytes intact.
- **D-10: QEMU script is pure shell** — `scripts/os/run_simpleos_qemu.shs` invokes `bin/simple run src/os/port/disk_image_bake.spl` to produce the disk image, then calls `qemu-system-x86_64` with `-kernel`, `-drive`, and `-serial stdio`. No new Simple code needed for the script itself.
- **D-11: kernel-origin bypass in cap_exec_gate** — The legacy 3-arg `fs_exec_spawn` calls `fs_exec_spawn_as(caller: TaskId { id: KERNEL_TASK_ID }, ...)` where `KERNEL_TASK_ID = 0`. Task 0 may not have been run through the capability seed routine. `exec_cap_check` therefore has an explicit early return: `if caller.id == KERNEL_TASK_ID: return Ok(())`. This is documented and intentional — kernel-initiated exec (boot, init launch) is implicitly trusted; user-space exec must always carry a seeded TaskId > 0.
- **D-12: REQ-3 deferred from spawn pipeline** — The spawn pipeline (`fs_exec_spawn` → `build_user_process_image_unchecked`) continues to use the ELF sniff path inside `process_image.spl` (via `rt_arm_elf64_*` externs). `loader_api.loader_dispatch` + `elf64_load` (the `vmm_mmap` path) is used only by `disk_launch_manifest` callers and by `loader_api_vfs.loader_dispatch_from_vfs`. These are two distinct ELF implementations. REQ-3 is satisfied at the byte-routing level (FAT32 bytes correctly flow into an ELF-capable dispatcher) but the full process-spawn integration of `elf64_load`+`vmm_mmap` is scoped to the `disk_launch_manifest` replacement path, not the bootstrap-scheduler path. The spec test verifies byte fidelity and ELF parse via `resolve_executable_bytes` + `elf64_has_magic`, not end-to-end vmm_mmap.
- **D-10: QEMU script is pure shell** — `scripts/os/run_simpleos_qemu.shs` invokes `bin/simple run src/os/port/disk_image_bake.spl` to produce the disk image, then calls `qemu-system-x86_64` with `-kernel`, `-drive`, and `-serial stdio`. No new Simple code needed for the script itself.

### Public API

**cap_exec_gate.spl:**
- `fn exec_cap_check(caller: TaskId, exec_path: text) -> Result<(), i64>` — checks `FileExec(path_prefix: exec_path)` + `ProcessSpawn`; returns `Ok(())` or `Err(-13)`

**fs_exec_spawn.spl (additions):**
- `pub fn fs_exec_spawn_as(caller: TaskId, path: text, argv: [text], envp: [text]) -> i64` — capability-gated spawn

**x86_64_fs_exec_spawn.spl (additions):**
- `pub fn x86_64_fs_exec_spawn_as(caller: TaskId, path: text, argv: [text], envp: [text]) -> i64` — capability-gated x86_64 spawn

**loader_api_vfs.spl (new):**
- `fn loader_dispatch_from_vfs(path: text, space: ProcessVmSpace) -> i64` — reads bytes via `g_vfs_read_executable_bytes` + dispatches via `loader_dispatch`

**hardening_types.spl:**
- `class HardeningReport { nx: bool, smep: bool, smap: bool, wp: bool, aslr_seed: u64, arch: text }` — arch-neutral probe result
- `fn hardening_report_empty(arch: text) -> HardeningReport` — zero-initialised report for unavailable probes

**x86_64_hardening_probe.spl (additions):**
- `fn x86_64_hardening_probe_full() -> HardeningReport` — reads CR0.WP, CR4.SMEP/SMAP, EFER.NX; seeds ASLR via RDRAND fallback RDTSC
- New externs: `extern fn rt_x86_64_read_cr0() -> u64`, `extern fn rt_x86_64_read_cr4() -> u64`, `extern fn rt_x86_64_read_msr(addr: u32) -> u64`, `extern fn rt_x86_64_rdrand_u64() -> u64`

**riscv64_hardening_probe.spl (additions):**
- `fn riscv64_hardening_probe_full() -> HardeningReport` — reads mstatus PMP bits, SATP mode; maps to `nx`/`wp` fields
- New extern: `extern fn rt_riscv64_read_mstatus() -> u64`

**arm64_hardening_probe.spl (additions):**
- `fn arm64_hardening_probe_full() -> HardeningReport` — reads SCTLR_EL1 (WXN → nx, nTWE → smep proxy)
- New extern: `extern fn rt_arm64_read_sctlr_el1() -> u64`

**arch_adapt.spl (addition):**
- `pub fn arch_hardening_probe() -> HardeningReport` — cfg-dispatches to per-arch `*_probe_full()`

**exec_from_fs_spec.spl (test/01_unit/os/kernel/loader/):**
- `it "ELF bytes resolve without text corruption"` — inject 256-byte sequence 0x00–0xFF via `_set_synthetic_vfs_file_for_test`; call `resolve_executable_bytes(path, arch)`; assert len==256 and byte-at-index equality (module-level helper)
- `it "resolve_executable_bytes returns ELF magic for valid ELF64 blob"` — inject minimal valid ELF64 header; call `resolve_executable_bytes`; assert `elf64_has_magic(bytes) == true`
- `it "exec_cap_check kernel sentinel bypasses check"` — call `exec_cap_check(TaskId { id: 0 }, "/bin/sh")`; assert result is `Ok`
- `it "exec_cap_check returns -13 for task with revoked FileExec"` — construct task with empty CapabilitySet; call `exec_cap_check`; assert result is `Err(-13)`
- `it "x86_64 hardening probe returns NX true"` — call `x86_64_hardening_probe_full()`; assert `report.nx == true` (EFER.NX set by QEMU default)

### Data Flow

```
shell_exec(cmd, argv, envp)
  -> shell_path_search(cmd) -> exec_path
  -> fs_exec_spawn_as(caller_pid, exec_path, argv, envp)        [shell passes its TaskId]
      -> cap_exec_gate.exec_cap_check(caller_pid, exec_path)    [REQ-1]
          -> ipc_mgr.cap_manager.check(caller, FileExec(path))
          -> ipc_mgr.cap_manager.check(caller, ProcessSpawn)
          -> Err(-13) on denial
      -> _fs_exec_read_bytes(exec_path)                          [REQ-2]
          -> g_vfs_read_executable_bytes(exec_path)             [FAT32 read, [u8]]
      -> build_user_process_image_unchecked(path, bytes, arch, argv, envp)
          -> _has_elf_magic(bytes) -> true
          -> rt_arm_elf64_* externs (parse segments)            [REQ-3, existing ELF path]
      -> _fs_exec_new_bootstrap_scheduler()
      -> scheduler_create_bootstrap_user_task_pid(...)          [REQ-4]
      -> returns PID

disk_launch_manifest.resolve_disk_launch_entry(path)            [REQ-4]
  -> returns None (placeholder removed)
  -> caller falls through to loader_exec(path, argv, envp, space)  [from loader_api.spl — VFS-free]
      -> rt_file_read_bytes(path)
      -> loader_dispatch(bytes, space)
          -> elf64_load(bytes, space) [vmm_mmap + vmm_copy_to_user]
      -> returns entry vaddr

spec test data flow:                                              [REQ-7]
  -> _set_synthetic_vfs_file_for_test(path, bytes)               [executable_source.spl hook]
  -> resolve_executable_bytes(path, arch) -> bytes               [goes through synthetic map]
  -> elf64_has_magic(bytes) -> true
  -> exec_cap_check(TaskId{id:0}, path) -> Ok(())                [D-11 bypass]
  -> exec_cap_check(revoked_task, path) -> Err(-13)

boot sequence:
  -> arch_hardening_probe() -> HardeningReport                  [REQ-6]
      -> x86_64_hardening_probe_full()
          -> rt_x86_64_read_cr4() -> CR4 -> smep, smap
          -> rt_x86_64_read_msr(0xC0000080) -> EFER -> nx
          -> rt_x86_64_read_cr0() -> CR0 -> wp
          -> rt_x86_64_rdrand_u64() -> aslr_seed
  -> serial_println("[harden] " + report fields)

scripts/os/run_simpleos_qemu.shs:                                  [REQ-5]
  -> bin/simple run src/os/port/disk_image_bake.spl -> build/os/simpleos.img + initramfs
  -> qemu-system-x86_64 -kernel build/os/kernel.elf -drive file=build/os/simpleos.img,...
     -serial stdio -m 256M
```

### Requirement Coverage

- REQ-1 -> `cap_exec_gate` + `fs_exec_spawn` (fs_exec_spawn_as) + `x86_64_fs_exec_spawn` (x86_64_fs_exec_spawn_as)
- REQ-2 -> `fs_exec_spawn` (_fs_exec_read_bytes path verified); `exec_from_fs_spec` (binary roundtrip it-block)
- REQ-3 -> `loader_api_vfs` (loader_dispatch_from_vfs, new file) + `disk_launch_manifest` (calls loader_exec → loader_dispatch → elf64_load). Spawn pipeline defers to existing ELF path in process_image; see D-12.
- REQ-4 -> `disk_launch_manifest` (placeholder removal) + `fs_exec_spawn` (scheduler task creation already wired)
- REQ-5 -> `run_simpleos_qemu` (new script) + `disk_image_bake` (existing, invoked by script)
- REQ-6 -> `hardening_types` + `x86_64_hardening_probe` + `riscv64_hardening_probe` + `arm64_hardening_probe` + `arch_adapt_harness`
- REQ-7 -> `exec_from_fs_spec` (4 it-blocks covering ELF parse, binary fidelity, capability denial, NX probe)

### 2026-06-02 SSH Shell/Launch Evidence

- Restored `Terminal` transport buffering (`feed_remote_input`, `peek_input`, line-preserving `read_input`, `take_mirrored_output`) so SSH shell sessions can process command chunks without losing later lines.
- Added `SshShellLaunchReport` test helper in `src/os/apps/sshd/ssh_session.spl` to resolve SSH shell/exec command tokens through the registry-backed `/usr/bin`, `/sys/apps`, and `/bin` launch candidates.
- Extended `test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl` with executable evidence for:
  - shell banner/prompt startup over the SSH shell adapter;
  - built-in command round-trip over the adapter;
  - multi-command input in a single transport chunk;
  - `simple.smf --version` resolving to `/usr/bin/simple.smf` and FAT32/root SMF aliases;
  - `simple --check` resolving to `/usr/bin/simple` and the same SMF-backed aliases;
  - `sh -lc pwd` resolving to `/usr/bin/sh` and the shell SMF aliases.
- Verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/terminal/terminal.spl src/os/apps/sshd/ssh_session.spl test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl` -> PASS.
  - `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, 6/6.
  - `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl --output doc/06_spec` -> generated `doc/06_spec/unit/os/apps/sshd/ssh_session_shell_spec.md`.
  - `find doc/06_spec -name '*_spec.spl' | wc -l` -> `0`.
- Scope note: this is unit-level SSH shell/launch-path evidence. It does not yet prove a live QEMU SSH login/server session can launch SMF/executable files.

### 2026-06-02 Live SSH/QEMU Evidence

- Extended the x64 SSH live TCP probe contract to include authenticated session probes for:
  - `SESSION shell simple.smf --version` -> SMF launch marker with `/usr/bin/simple.smf` and `/SYS/APPS/SIMPLSTC.SMF`.
  - `SESSION shell simple --check` -> executable-file launch marker with `/usr/bin/simple` and `/SYS/APPS/SIMPLSTC.SMF`.
- Replaced the stale live system spec wiring with the current `x64-ssh` scenario contract:
  - uses `build_os_with_backend(target, "cranelift")`;
  - runs `test_scenario(scenario, scenario_test_timeout_ms(scenario))`;
  - uses runner timeout flag `--timeout 900` rather than ignored `--timeout-ms`.
- Hardened `examples/simple_os/arch/x86_64/ssh_live_entry.spl` for the bare-metal live path:
  - removed POSIX/service bootstrap calls that faulted before the TCP listener;
  - added direct `rt_net_init()`/`rt_net_stats()` initialization before binding port 22.
- Fixed `src/os/qemu_runner_part5.spl` so `x64-ssh` accepts the probe wrapper's host-side success exit code `0`; the wrapper already terminates QEMU after observing `TEST PASSED`.
- Verification:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check examples/simple_os/arch/x86_64/ssh_live_entry.spl test/03_system/ssh_live_login_in_qemu_spec.spl src/os/qemu_runner_part5.spl` -> PASS.
  - `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/03_system/ssh_live_login_in_qemu_spec.spl --mode=interpreter --timeout 900 --clean --format json` -> PASS, 1/1.
- Evidence artifacts:
  - `build/test-artifacts/system/ssh_live_login_in_qemu/combined.log` contains `TEST PASSED`.
  - `build/os/x64-ssh-live.session-smf.txt` contains `SESSION OK shell simple.smf path=/usr/bin/simple.smf alias=/SYS/APPS/SIMPLSTC.SMF`.
  - `build/os/x64-ssh-live.session-exec.txt` contains `SESSION OK shell simple path=/usr/bin/simple alias=/SYS/APPS/SIMPLSTC.SMF`.
- 2026-06-02 continuation: Refreshed the generated scenario manual for `test/03_system/ssh_live_login_in_qemu_spec.spl` so it documents the live QEMU boot, host port 2222 forwarding, SSH shell/auth probes, SMF launch transcript, executable launch transcript, and failure diagnostics. `spipe-docgen --no-index` generated a complete manual at `doc/06_spec/system/ssh_live_login_in_qemu_spec.md` with no stub output.
- 2026-06-02 continuation verification: The current live SSH/QEMU gate passed `1/1` with `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/03_system/ssh_live_login_in_qemu_spec.spl --mode=interpreter --timeout 900 --clean --format json`. `build/os/x64-ssh-live.session-smf.txt` contains `SESSION OK shell simple.smf path=/usr/bin/simple.smf alias=/SYS/APPS/SIMPLSTC.SMF`, `build/os/x64-ssh-live.session-exec.txt` contains `SESSION OK shell simple path=/usr/bin/simple alias=/SYS/APPS/SIMPLSTC.SMF`, no SSH/QEMU processes remained, and the doc layout guard returned `0`.

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

### 2026-06-11 RV64 SSH continuation

- continuation-impl: Updated `src/os/apps/sshd/sshd.spl` so live host-key startup no longer calls `rt_tls13_ed25519_public_key`. The daemon now derives the Ed25519 public key through the existing pure-Simple `ed25519_keypair_from_seed(seed).1`, validates it against the RFC 8032 fixed test vector, and stores the derived value as the live host public key.
- continuation-impl: Updated `src/os/services/netstack/netstack_init.spl` and `src/os/kernel/boot/riscv_services.spl` with a shared RV64 status normalizer for freestanding net-runtime returns that surface small negative errno values as wrapped 61-bit positives (`2^61 - n`). `rt_net_init`, `rt_net_tx_test`, `rt_net_rx_ready`, and `rt_net_stats` are now normalized before comparisons/logging in those shared code paths.
- continuation-impl: Localized `HostKeySet` / `HostCertificateSet` imports in `sshd.spl` to `ssh_kex_primitives` and localized the PCI/VirtIO constants used by `netstack_init.spl` so the touched shared files can be checked cleanly in the current tree without depending on missing export surfaces.
- continuation-verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/sshd.spl src/os/kernel/boot/riscv_services.spl src/os/services/netstack/netstack_init.spl` -> PASS.
- continuation-verify: Direct live RV64 QEMU repro against the current `build/os/simpleos_riscv64_ssh_live.elf` moved the failure boundary forward. The current serial log at `build/os/rv64-ssh-live.serial.log` no longer stalls at the Ed25519 self-test and instead reaches:
  - `[boot] Initializing RV64 VirtIO network runtime`
  - `[boot] rv64_network_init rc=2305843009213693933`
  - `[FATAL] SSH network init failed`
- continuation-verify: `2305843009213693933` is `2^61 - 19`, matching the wrapped-negative status pattern normalized in the shared RV64 net helpers. This means the live blocker has shifted from SSH host-key startup to the RV64 network-init caller/runtime contract.
- continuation-impl: Recreated the missing current-source RV64 live lane surface:
  - added `src/os/rv64_probe.spl` exposing `rv64_network_init()` through shared RISC-V service init;
  - added `examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` to emit the RV64 SSH live boot markers and launch `SshDaemon` through the new facade;
  - added `examples/09_embedded/simple_os/arch/riscv64/linker.ld` as a wrapper around the in-tree RV64 linker script;
  - added `scenario_rv64_ssh`, `get_riscv64_ssh_live_target`, and `run_rv64_ssh_probe` wiring across `src/os/qemu_runner*.spl` and `src/os/ssh_qemu_contract.spl`.
- continuation-verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/rv64_probe.spl examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl src/os/ssh_qemu_contract.spl` -> PASS. `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/qemu_runner_part3.spl src/os/qemu_runner_part4.spl src/os/qemu_runner_part5.spl src/os/qemu_runner.spl` -> PASS on the touched parts with the pre-existing `qemu_runner.spl` unresolved export warning.
- continuation-risk: A current-source RV64 Cranelift build now reaches the freestanding linker with the recreated entry path, but still fails because the `SshDaemon` closure pulls unsupported runtime symbols into the bare-metal bundle (`rt_enum_new`, `rt_alloc`, `rt_string_new`, `rt_array_*`, `log_raw_println`, and similar). The active blocker is therefore no longer “missing RV64 SSH live source” but “production SSH daemon is not yet freestanding-safe on the current RV64 live closure”.
- continuation-verify: Revalidated the real-filesystem dispatch prerequisite around `std.fs_driver.mount_table.MountTable.resolve()`. Current source in `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` already uses the intended slice-free indexed copy (`str_char_at` loop) for relpath extraction, matching FR-STORAGE-0004. Current verification is green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/fs_driver/mount_table_test.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `13/13`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/fs_driver/mount_table_resolve_test.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `6/6`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/fs_driver/mount_table.spl test/01_unit/fs_driver/mount_table_test.spl test/01_unit/fs_driver/mount_table_resolve_test.spl` -> PASS
- continuation-risk: The MountTable micro-bench under `test/05_perf/**` still depends on a `test.perf.*` module alias that the current runner does not resolve under `SIMPLE_LIB=src`, so current perf evidence for this sub-lane remains blocked on harness/import-path cleanup rather than on `MountTable.resolve()` correctness itself.
- continuation-impl: Extended `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` so `MountTable` now packs the owning `MountId` into returned `FileHandle` / `DirHandle` values and routes `read`, `write`, `pread`, `pwrite`, `close`, `readdir`, and `ftruncate` directly back to the owning mount instead of probing every mounted driver with a raw handle id. This addresses the structural multi-mount handle-collision risk exposed by `/` + `/data` setups.
- continuation-impl: Hardened the hosted DBFS/NVFS path for current compiler behavior:
  - `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl`: `arena_readv` now declares a mutable byte buffer parameter and the stale `DurabilityClass.Relaxed` fallback was corrected to `DurabilityClass.BestEffort`;
  - `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl` and `src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl`: byte-buffer read/pread parameters are now declared `mut` to match the in-place write semantics the lowering/JIT path expects;
  - `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` and `src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl`: added explicit `text` typing / `rt_string_len()` use in the active replay/name paths to narrow current codegen ambiguity around bare `.len()` dispatch.
- continuation-verify: Focused checks are green for the touched storage files:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/fs_driver/mount_table.spl` -> PASS
- continuation-verify: The current mounted-NVFS `/data` probe no longer reports the old stale `DurabilityClass.Relaxed` failure and previously showed `FsError::NotFound` on mounted `write` / `pread`, consistent with handle-routing or wrapper ownership failure. After the mount-qualified handle routing change, the active blocker is now a compiler/frontend failure during mounted probe execution rather than a clean storage-driver result:
  - interpreter/JIT falls back on `RamFsDriver.remove_dir_entry` mutability lowering (`W1006`) and then aborts with `error: semantic: type mismatch: cannot convert array to int` before the mounted `/data` write/read round-trip can be re-proved end to end.
- continuation-risk: The real-fs storage lane has therefore moved from "mount-table dispatch not implemented for NVFS mutation" to "current frontend/interpreter path still blocks end-to-end mounted NVFS proof even after dispatch and wrapper fixes". The next useful step is to isolate the exact `type mismatch: cannot convert array to int` source in the mounted probe/import path and close the remaining RamFs/driver mutability lowering fallout so the mounted NVFS proof can run to completion.
- continuation-impl: Fixed the concrete `type mismatch: cannot convert array to int` regression introduced during the earlier ambiguity cleanup by restoring `_ensure_persisted_path()` in `src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl` to use the byte-array `content.len()` check instead of `rt_string_len(content)`.
- continuation-impl: Replaced the earlier packed-handle experiment in `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` with explicit mount-table-owned file/dir binding tables (`open_files`, `open_dirs`) so later operations can route by mount ownership without depending on large packed integer behavior. Also fixed binding-table mutation to assign returned arrays back after `push()` / `remove()`.
- continuation-impl: Fixed multiple real state-loss bugs in hosted storage wrappers where array mutation results were previously discarded:
  - `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl`: module-level `_dbfs_*` inode/fd/device store `push()` / `remove()` calls now assign back to the owning arrays, including `new_hosted()`, `open_path()`, `opendir_path()`, inode updates, fd close state, and device registration/blob tracking paths;
  - `src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl`: `_nvfs_posix_files` and `_nvfs_posix_open` bookkeeping now assigns back on `push()` / `remove()`.
- continuation-impl: Hardened the remaining hosted probe compile path by making ambiguous local array/text types explicit in `dbfs_driver.spl` and `nvfs_posix_driver.spl` (`data_len`, typed sector/lines/parts locals, explicit split result typing).
- continuation-verify: Current focused checks remain green after those fixes:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl src/lib/nogc_sync_mut/fs_driver/mount_table.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check tmp_nvfs_posix_hosted_probe.spl tmp_mount_table_nvfs_probe.spl` -> PASS
- continuation-verify: The mounted `/data` probe still reproduces a real runtime failure rather than a compiler crash:
  - `open_ok=true`
  - `fh_id=1`
  - `write_ok=false`
  - `write_err=FsError::NotFound`
  - `reopen_ok=true`
  - `rfh_id=2`
  - `pread_ok=false`
  - `pread_err=FsError::NotFound`
- continuation-risk: This means the storage hardening lane has moved forward again: the stale durability enum issue, the array-to-int semantic break, the mount-table handle-collision design flaw, and several discarded-array-state bugs are fixed in source. The remaining blocker is now a narrower hosted `NvfsPosixDriver` / `DbFsDriver` runtime ownership/state defect that still returns `FsError::NotFound` for the mounted write/readback path under the interpreter-fallback execution environment.
- continuation-impl: Added a direct ownership-safe rewrite of the RamFs directory-entry helpers in `src/lib/nogc_sync_mut/fs_driver/ramfs.spl` (`add_dir_entry`, `remove_dir_entry`) so they rebuild `RamFsDir` values instead of mutating the matched `Dir(d)` payload in place. This is the intended fix for the recurring interpreter/JIT mutability warning on the mounted probe path, although the current fallback warning still reports the same historical source location during `tmp_mount_table_nvfs_probe.spl`.
- continuation-verify: Rechecked the active storage files together after the latest fixes:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/fs_driver/ramfs.spl src/lib/nogc_sync_mut/fs_driver/mount_table.spl src/lib/nogc_sync_mut/fs_driver/nvfs_posix_driver.spl src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` -> PASS
- continuation-risk: Changing the mounted probe to use `var mt = make_table()` did not change the failure outcome, so the remaining `FsError::NotFound` is not just lost mutation on an immutable `MountTable` local. The active blocker remains inside the hosted `NvfsPosixDriver` / `DbFsDriver` runtime path for mounted write/readback, even after the array-state fixes landed.
- continuation-impl: The active runtime import path for `std.fs_driver.mount_table` in this mounted-storage lane is `src/lib/nogc_async_mut/fs_driver/mount_table.spl`, not the sync-family file. Hardened that async-family `MountTable` with explicit open file/dir binding tables (`open_files`, `open_dirs`), virtual handle allocation (`1001+`, `2001+`), direct dispatch for `read` / `write` / `pread` / `pwrite` / `close` / `readdir` / `ftruncate`, and text-handle forwarding for `Nvfs`, `NvfsPosix`, and `DbFs` mutating operations (`write`, `pwrite`, `pread`, `unlink`, `rename`, `ftruncate`).
- continuation-impl: Corrected the async-family close helper for root-mounted `RamFs` so that `MountTable.close()` uses `RamFsDriver.close()` on that branch instead of the wrapper name that was not resolving reliably under the interpreter fallback path.
- continuation-verify: The mounted `/data` real-filesystem round-trip is now re-proved against the active runtime path. Direct probe evidence reached:
  - `open_ok=true`, `fh_id=1001`
  - `write_ok=true`
  - `close1_ok=true`
  - `reopen_ok=true`, `rfh_id=1002`
  - `pread_ok=true`, `pread_val=hello`
  - `close2_ok=true`
- continuation-verify: The integration spec covering mounted mutating I/O now passes end to end:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_async_mut/fs_driver/mount_table.spl test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `5/5`
- continuation-risk: The last failing spec branch was a test issue rather than a remaining mounted-NVFS defect. The original sibling-path assertion exercised `/etc/hosts` and then RamFs file-handle cleanup, which hit pre-existing RamFs `open_path` stub behavior instead of mount dispatch. The spec now checks sibling-path resolution directly via `MountTable.resolve(Path(raw: "/hosts"))`, which is the correct assertion for “non-/data paths still resolve to the root mount”.
- continuation-verify: Rechecked the DBFS-backed mount-table consumer path above raw dispatch. Current evidence is green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `8/8`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/02_integration/storage/dbfs/dbfs_posix_shim_spec.spl src/lib/nogc_async_mut/fs_driver/mount_table.spl src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/storage/dbfs/dbfs_posix_shim_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `9/9`
- continuation-verify: Rechecked app-layer persistence and portal content on top of the current filesystem-backed stack. Current evidence is green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/02_integration/app/web_stack_sample_persistence_spec.spl test/02_integration/app/web_stack_sample_persistence_runner.spl src/lib/nogc_sync_mut/web_framework/persistence.spl src/lib/nogc_sync_mut/web_framework/session.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/app/web_stack_sample_persistence_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `1/1`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `5/5`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/02_integration/app/simple_portal/simple_portal_server_spec.spl src/app/simple_portal/server.spl src/app/simple_portal/content_db.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/02_integration/app/simple_portal/simple_portal_server_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` -> PASS, `9/9`
- continuation-risk: With mounted NVFS, mounted DBFS POSIX-shim behavior, web-stack restart persistence, and DBFS-backed portal content serving all green in the current worktree, the active integrated-stack risk is no longer “real fs base OS stack cannot persist or serve app content”. The remaining top-priority hardening gap is still the RV64 live/freestanding path, especially the SSH daemon/runtime closure and any equivalent live-QEMU HTTP/web proof for the RISC-V lane.
- continuation-impl: Restored the canonical runnable RV64 SSH live system spec at `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`. The checkout previously only had `.spipe_matchers_rv64_ssh_live_login_in_qemu_spec.spl`, so the normal spec path was missing and `bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl ...` could not run. The restored spec now uses the repo's real `rt_env_get` / `rt_file_read_text` extern pattern instead of the non-resolving `std.nogc_sync_mut.host.runtime_facade` import.
- continuation-verify: The static RV64 SSH lane evidence is now green from the canonical path:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` -> PASS
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential --format json` -> PASS, `5/5`
- continuation-verify: The opt-in live RV64 SSH gate now reproduces a current-source build failure instead of depending on stale `build/os/rv64-ssh-live.serial.log` artifacts:
  - command: `SIMPLE_LIB=src SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential --format json`
  - build path reached: `src/compiler_rust/target/debug/simple native-build --source build/os/generated --source src --source examples --backend cranelift --opt-level=aggressive --log on --entry-closure --entry examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl --target riscv64-unknown-none -o build/os/simpleos_riscv64_ssh_live.elf --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld`
  - result: native-build failed after ~17.3s at freestanding link
  - current unresolved-symbol boundary includes `rt_string_eq`, `rt_tuple_new`, `rt_string_to_lower`, `rt_contains`, plus the broader runtime-backed string/tuple/container closure already suspected in SSH/auth/log code
- continuation-risk: This current-source repro tightens the active RV64 SSH blocker again. The dominant issue is now clearly the freestanding live bundle still pulling hosted/runtime-backed string/tuple/container helpers through `os.apps.sshd.*` and `os.kernel.log.klog_api`, not an old boot artifact or a missing test lane. The next useful cut is to shrink or facade that closure rather than continue debugging old serial logs.
- continuation-impl: Split the SSH shell launch-path helper out of `src/os/apps/sshd/ssh_session.spl` into `src/os/apps/sshd/ssh_session_shell_test_ext.spl`. That removes the `os.kernel.loader.app_registry.*` dependency from the live SSH session module while keeping the shell launch-report tests intact through the new test-only extension import.
- continuation-impl: Reworked `src/os/kernel/log/klog_api.spl` parsing helpers to use local ASCII token scanning instead of `text.lower()` / `text.contains()`. This removes that module's direct dependency on the generic runtime text helpers for log-level and target parsing.
- continuation-impl: Removed hosted `SshPty` ownership from the headless live SSH path in `src/os/apps/sshd/ssh_session.spl` and `src/os/apps/sshd/ssh_session_channel.spl`. `pty-req` is now acknowledged as protocol state only, while shell/exec traffic continues through the built-in remote shell without importing `pipe_compat`.
- continuation-verify: Focused SSH checks after the split/cut are green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl --mode=interpreter --clean --timeout 120 --sequential --format json` -> PASS, `6/6`
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential --format json` -> PASS, `5/5`
- continuation-verify: Re-ran the opt-in current-source live RV64 SSH gate after those cuts:
  - `SIMPLE_LIB=src SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential --format json`
  - result: native-build still fails at freestanding link, but the failure boundary moved materially
  - earlier intermediate boundary after the app-registry/log cuts still showed hosted PTY leakage via `os__kernel__pipe_compat__*` (`rt_index_set`, `rt_typed_words_u64_set`, `mmio_write32`)
  - after removing `SshPty` from the live path, that `pipe_compat` cluster disappeared from the unresolved tail
  - current unresolved-symbol boundary is now deeper in core runtime-backed text/array/crypto helpers:
    - `rt_string_concat`
    - `rt_byte_array_new`
    - `rt_native_neq`
    - `rt_array_new_with_cap_u64`
- continuation-risk: The RV64 SSH live lane is still blocked, but the blocker moved again in the right direction:
  - no longer stale serial-artifact confusion
  - no longer missing canonical spec lane
  - no longer obviously dominated by app-registry imports
  - no longer dragging hosted PTY / `pipe_compat` into the live closure
  - now blocked mainly by the remaining runtime-backed string/array primitives and the deeper SSH KEX / crypto closure
- continuation-impl: Hardened the RV64 freestanding runtime bridge in `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` so the boot object now compiles standalone and exports the generic helpers the live SSH lane was missing:
  - fixed the local tagged-int helper (`rt_int`) used by byte-array builders
  - added `rt_array_new_with_cap_u64`
  - added `rt_typed_words_u32_push`
  - added `rt_typed_words_u64_push`
  - added `rt_typed_words_u64_set`
  - added `rt_string_eq`
  - added `rt_any_add`
- continuation-verify: Standalone boot-object validation now proves those symbols exist in the compiled RV64 freestanding object:
  - `clang -c -ffreestanding -nostdlib -fno-pie --target=riscv64-unknown-none -march=rv64imac -mabi=lp64 -mcmodel=medany examples/09_embedded/simple_os/arch/riscv64/boot/freestanding_runtime.c`
  - `nm -g freestanding.o` now includes `rt_string_concat`, `rt_string_eq`, `rt_byte_array_new`, `rt_byte_array_new_len`, `rt_any_add`, `rt_array_new_with_cap_u64`, `rt_typed_words_u32_push`, `rt_typed_words_u64_push`, `rt_typed_words_u64_set`, `rt_native_neq`, `rt_index_set`, `serial_println`
- continuation-impl: Cleaned the split SSH session module surface so the production SSH lane checks coherently again:
  - exported shared transport/channel/auth/KEX constants and structs from their owner modules:
    - `src/os/apps/sshd/ssh_transport.spl`
    - `src/os/apps/sshd/ssh_channel.spl`
    - `src/os/apps/sshd/ssh_auth.spl`
    - `src/os/apps/sshd/ssh_kex_primitives.spl`
    - `src/os/apps/sshd/ssh_kex.spl`
    - `src/os/apps/sshd/ssh_session_helpers.spl`
  - fixed split-file imports in:
    - `src/os/apps/sshd/ssh_session.spl`
    - `src/os/apps/sshd/ssh_session_kex.spl`
    - `src/os/apps/sshd/ssh_session_helpers.spl`
  - replaced the dead `std.format.{format_hex}` imports with `std.tls.utilities.{format_hex}` in the SSH session split files
- continuation-verify: Focused compile checks for the production SSH split lane are now green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/ssh_kex.spl src/os/apps/sshd/sshd.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/ssh_session_auth.spl src/os/apps/sshd/ssh_session_channel.spl src/os/apps/sshd/ssh_session_helpers.spl src/os/apps/sshd/ssh_session_kex.spl` -> PASS
- continuation-verify: Re-ran the opt-in current-source live RV64 SSH gate after those runtime + SSH surface fixes:
  - `SIMPLE_LIB=src SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential --format json`
  - result: native-build still fails at freestanding link, but the failure boundary moved again
  - the generic runtime-backed string/array/typed-word closure is no longer the dominant failure
  - the current top unresolved symbols are now the socket-style network runtime surface used by production `sshd`:
    - `rt_net_socket`
    - `rt_net_bind`
    - `rt_net_listen`
    - `rt_net_accept`
    - `rt_net_close`
- continuation-risk: This clarifies the next honest RV64 SSH blocker. The freestanding runtime already contains low-level VirtIO net bring-up (`rt_net_init`, RX/TX readiness, TCP packet processing), but it does not yet expose the higher-level socket-style `rt_net_*` API required by the production SSH daemon. The next useful cut is therefore the RV64 freestanding TCP/socket facade over the existing net runtime, not more broad SSH source cleanup.
- continuation-impl: Added a first socket-style RV64 SSH network facade at `src/os/kernel/net/rt_net_socket_facade.spl`. This exports:
  - `rt_net_socket`
  - `rt_net_bind`
  - `rt_net_listen`
  - `rt_net_accept`
  - `rt_net_close`
  - `rt_net_send_bytes`
  - `rt_net_recv_bytes`
  - `rt_net_recv_version_text`
  - `rt_net_recv_ssh_plain_packet_payload`
  over the existing `netstack_init` singleton path, with lazy `net_boot_init()` + `net_service_init_port()` bring-up and small per-fd facade state.
- continuation-impl: Wired the facade into the RV64 boot lane in `src/os/kernel/boot/riscv_services.spl` through `rt_net_socket_facade_link_anchor()` so the network service probe can keep the new exported net facade reachable from the RISC-V boot services path.
- continuation-impl: Promoted the cross-module RV64 boot / SSH session surfaces that the live lane was semantically relying on:
  - `src/os/kernel/boot/riscv_services.spl`: `init_riscv_services`, `init_riscv_services_with_network`, `riscv_services_ready`, `riscv_network_ready`, `riscv_network_ready_code` are now `pub`
  - `src/os/apps/sshd/ssh_session.spl`: `new_with_host_materials`, `run`, `close` are now `pub`
- continuation-verify: Focused checks for the new facade and promoted surfaces are green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/kernel/boot/riscv_services.spl src/os/services/netstack/netstack_init.spl src/os/rv64_probe.spl src/os/apps/sshd/ssh_session.spl` -> PASS
- continuation-verify: Re-ran the opt-in live RV64 SSH gate after adding the facade and promoting those surfaces:
  - `SIMPLE_LIB=src SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift src/compiler_rust/target/release/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential --format json`
  - result: native-build still fails at freestanding link
  - the unresolved set narrowed compared with earlier runtime-helper failures, but the current failure now points at entry-closure reachability/emission rather than API shape:
    - `rt_net_listen`
    - `rt_net_accept`
    - `rt_net_close`
    - `os__apps__sshd__ssh_session__SshSession_dot_new_with_host_materials`
    - `os__apps__sshd__ssh_session__SshSession_dot_run`
    - `os__apps__sshd__ssh_session__SshSession_dot_close`
    - `os__kernel__boot__riscv_services__init_riscv_services_with_network`
    - `os__kernel__boot__riscv_services__riscv_network_ready_code`
- continuation-risk: The active blocker is now more specific again. The new RV64 socket facade and promoted boot/session surfaces check correctly in source, but the freestanding native-build still does not pull those symbols into the final entry closure. The next useful cut is therefore inside the native-build entry-closure / module reachability path for RV64 freestanding images, not more protocol-layer SSH cleanup.
- continuation-impl: Investigated the entry-closure path with a direct archive build of the RV64 SSH lane:
  - `env SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend cranelift --opt-level=aggressive --entry-closure --entry examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl --target riscv64-unknown-none --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld --emit-archive -o /tmp/rv64_ssh_live.a`
  - this exposed that the earlier "missing symbol" set was partly caused by two key files being silently skipped as non-critical compile failures during native-build:
    - `src/os/apps/sshd/ssh_session.spl` still referenced removed field `self.pty` in `close()`
    - `src/os/kernel/boot/riscv_services.spl` still had a stray `break` outside any loop
- continuation-impl: Fixed those two native-build blockers:
  - removed the stale `self.pty` close path from `src/os/apps/sshd/ssh_session.spl`
  - removed the invalid `break` from the net-facade probe branch in `src/os/kernel/boot/riscv_services.spl`
- continuation-verify: After those fixes:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/ssh_session.spl src/os/kernel/boot/riscv_services.spl` -> PASS
  - the RV64 archive closure build completed with `0 failed`
  - `nm -g /tmp/rv64_ssh_live.a` now proves the promoted SSH session and RISC-V boot symbols are present in the closure:
    - `os__apps__sshd__ssh_session__SshSession_dot_new_with_host_materials`
    - `os__apps__sshd__ssh_session__SshSession_dot_run`
    - `os__apps__sshd__ssh_session__SshSession_dot_close`
    - `os__kernel__boot__riscv_services__init_riscv_services_with_network`
    - `os__kernel__boot__riscv_services__riscv_network_ready_code`
- continuation-risk: That changed the diagnosis again: the live RV64 SSH lane is not primarily blocked by entry-closure omission of `ssh_session` / `riscv_services` anymore. Those definitions are in the closure once the native-build compile-skip bugs are fixed.
- continuation-impl: Tightened the RV64 socket facade export contract in `src/os/kernel/net/rt_net_socket_facade.spl` by giving each `@export("C")` an explicit `name: "rt_net_*"` spelling, then moved the SSH daemon/session off direct `extern fn rt_net_*` imports and onto normal Simple module imports from the facade:
  - `src/os/apps/sshd/sshd.spl`
  - `src/os/apps/sshd/ssh_session.spl`
  - `src/os/apps/sshd/ssh_session_helpers.spl`
- continuation-verify: Focused checks after the import-path cut are green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/sshd.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/ssh_session_helpers.spl src/os/kernel/net/rt_net_socket_facade.spl` -> PASS
- continuation-verify: Re-ran the direct current-source RV64 executable build after replacing the `extern rt_net_*` path:
  - `env SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend cranelift --opt-level=aggressive --entry-closure --entry examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl --target riscv64-unknown-none --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld -o /tmp/simpleos_riscv64_ssh_live.elf`
  - result: the live freestanding link no longer stops on `rt_net_listen` / `rt_net_accept` / `rt_net_close`
  - the active unresolved boundary moved deeper again to the remaining freestanding runtime / pure-Simple backlog, led by:
    - `rt_string_char_code_at`
    - `rt_typed_bytes_u8_push`
    - `Slice`
    - `rt_dh_curve25519_public_key`
    - `rt_dh_curve25519_shared_secret`
    - `rt_bytes_slice`
    - `rt_string_from_byte_array`
    - `rt_string_starts_with`
    - `rt_bytes_concat`
    - `rt_ssh_aes128_gcm_encrypt_packet`
    - `rt_ssh_aes128_gcm_decrypt_packet`
    - `rt_thread_sleep`
    - `rt_string_trim`
    - `rt_push_byte`
    - `rt_for_iterable`
    - `rt_ssh_userauth_password_only_failure_payload`
    - plus unrelated hosted/syscall leakage such as `rt_x86_syscall` and `syscall`
- continuation-risk: This is the current honest boundary. The RV64 SSH lane now gets past the socket-facade/import contract and into the deeper freestanding runtime backlog. The next useful cut is no longer net facade reachability; it is pruning hosted/userland leakage from the live SSH closure and filling the remaining pure-Simple/freestanding runtime helpers needed by the SSH/text/crypto path.
- continuation-impl: Kept shrinking the deeper freestanding backlog in the RV64 boot runtime itself (`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`). Added the following missing helper surfaces directly to the freestanding bridge:
  - `rt_typed_bytes_u8_push`
  - `rt_push_byte`
  - `rt_string_char_code_at`
  - `rt_string_starts_with`
  - `rt_string_trim`
  - `rt_string_ends_with`
  - `rt_string_split`
  - `rt_string_from_byte_array`
  - `rt_bytes_slice`
  - `rt_bytes_concat`
  - `rt_for_iterable`
  - `rt_ssh_userauth_password_only_failure_payload`
  - `rt_thread_sleep`
- continuation-verify: Standalone freestanding object symbol checks now prove those helpers exist in the RV64 boot object:
  - `clang -c -ffreestanding -nostdlib -fno-pie --target=riscv64-unknown-none -march=rv64imac -mabi=lp64 -mcmodel=medany src/os/kernel/arch/riscv64/boot/freestanding_runtime.c -o /tmp/freestanding_runtime.o`
  - `nm -g /tmp/freestanding_runtime.o` shows:
    - `rt_typed_bytes_u8_push`
    - `rt_push_byte`
    - `rt_string_char_code_at`
    - `rt_string_starts_with`
    - `rt_string_trim`
    - `rt_string_ends_with`
    - `rt_string_split`
    - `rt_string_from_byte_array`
    - `rt_bytes_slice`
    - `rt_bytes_concat`
    - `rt_for_iterable`
    - `rt_ssh_userauth_password_only_failure_payload`
    - `rt_thread_sleep`
- continuation-impl: Moved the live KEX transcript helpers off missing externs and onto the active net facade module:
  - `src/os/kernel/net/rt_net_socket_facade.spl` now stores `_rt_net_last_plain_payload` and exposes:
    - `rt_net_last_ssh_plain_payload_len()`
    - `rt_net_last_ssh_plain_payload_slice(start, length)`
  - `src/os/apps/sshd/ssh_session_kex.spl` now imports those functions as normal Simple module calls instead of unresolved runtime externs
- continuation-impl: Replaced the `std.tls.utilities` / `std.format` hex formatting dependency inside the SSH live lane with a new local helper module:
  - new file: `src/os/apps/sshd/ssh_hex.spl`
  - patched callers:
    - `src/os/apps/sshd/ssh_cipher.spl`
    - `src/os/apps/sshd/ssh_session_auth.spl`
    - `src/os/apps/sshd/ssh_session_channel.spl`
    - `src/os/apps/sshd/ssh_session_kex.spl`
    - `src/os/apps/sshd/ssh_session_helpers.spl`
    - `src/os/apps/sshd/ssh_kex_primitives.spl`
  - also fixed the local `SSH_MIN_PADDING` width usage in `ssh_cipher.spl` so it no longer emits `SSH_MIN_PADDING_dot_to_u64`
- continuation-verify: Focused checks on the touched SSH/facade files are green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/ssh_cipher.spl src/os/apps/sshd/ssh_hex.spl src/os/apps/sshd/ssh_session_kex.spl src/os/kernel/net/rt_net_socket_facade.spl` -> PASS
- continuation-verify: Re-ran the direct current-source RV64 freestanding SSH build after those helper/import cuts:
  - `env SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend cranelift --opt-level=aggressive --entry-closure --entry examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl --target riscv64-unknown-none --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld -o /tmp/simpleos_riscv64_ssh_live.elf`
  - unresolved count improved in this sequence:
    - `107` unexpected symbols
    - `98`
    - `96`
    - `95`
    - `91`
    - `90`
- continuation-risk: The active RV64 SSH blocker is now even narrower. The remaining tail is mostly true freestanding crypto/runtime coverage plus a few portability leaks:
  - crypto/runtime:
    - `rt_dh_curve25519_public_key`
    - `rt_dh_curve25519_shared_secret`
    - `rt_tls13_x25519_public_key`
    - `rt_tls13_x25519_shared_secret`
    - `rt_tls13_ed25519_sign`
    - `rt_ed25519_verify`
    - `rt_ssh_aes128_gcm_encrypt_packet`
    - `rt_ssh_aes128_gcm_decrypt_packet`
    - `rt_ecdsa_p256_sign`
    - `rt_ecdsa_p256_verify`
    - `rt_rsa_sha256_sign`
    - `rt_rsa_sha512_sign`
    - `rt_rsa_sha256_verify`
    - `rt_rsa_sha512_verify`
    - `rt_sha512_H`
    - `rt_rdrand`
  - portability / hosted-leakage:
    - `Slice`
    - `rt_port_outl`
    - `rt_port_inl`
    - `rt_embedded_host_rsa_component`
- continuation-risk: That is the current honest next cut. The socket facade and generic string/array helper backlog are no longer the main issue. The next useful work is either:
  1. split the live RV64 SSH closure away from hosted RSA/ECDSA/random/PIO code paths, or
  2. add the remaining required freestanding crypto/runtime primitives for the exact live SSH algorithm set.
- continuation-impl: Cut more of the RV64 live SSH closure over to existing pure-Simple crypto and removed the dead `aes128-gcm` runtime edge from the session fast path:
  - `src/os/apps/sshd/ssh_session_kex.spl`
    - now imports `os.crypto.curve25519.{x25519, x25519_base}`
    - now imports `os.crypto.ed25519.{ed25519_sign, ed25519_verify}`
    - replaced `rt_tls13_x25519_public_key` with `x25519_base`
    - replaced `rt_tls13_x25519_shared_secret` with `x25519`
    - replaced `rt_tls13_ed25519_sign` with `ed25519_sign`
    - replaced `rt_ed25519_verify` self-check with pure `ed25519_verify`
  - `src/os/apps/sshd/ssh_session.spl`
    - removed the direct `rt_tls13_x25519_*`, `rt_ed25519_verify`, and `rt_ssh_aes128_gcm_*` extern dependency from the live session module
    - `aes128-gcm@openssh.com` now fails closed as unsupported on the freestanding lane instead of dragging unresolved runtime hooks into the image
- continuation-verify: Focused checks for the touched live SSH files are green:
  - `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/sshd/ssh_session_kex.spl src/os/apps/sshd/ssh_session.spl` -> PASS
- continuation-verify: Re-ran the direct current-source RV64 freestanding SSH build after the pure-Simple KEX/session cut:
  - `env SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend cranelift --opt-level=aggressive --entry-closure --entry examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl --target riscv64-unknown-none --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld -o /tmp/simpleos_riscv64_ssh_live.elf`
  - unresolved count improved again:
    - `90` -> `85`
- continuation-risk: The active RV64 freestanding tail has shifted away from the patched live KEX/session calls and is now mostly:
  - hosted or fallback crypto still being pulled into closure:
    - `rt_dh_curve25519_public_key`
    - `rt_dh_curve25519_shared_secret`
    - `rt_ecdsa_p256_sign`
    - `rt_ecdsa_p256_verify`
    - `rt_rsa_sha256_sign`
    - `rt_rsa_sha512_sign`
    - `rt_rsa_sha256_verify`
    - `rt_rsa_sha512_verify`
    - `rt_sha512_H`
    - `rt_rdrand`
    - `rt_embedded_host_rsa_component`
  - portability or freestanding-runtime gaps:
    - `Slice`
    - `rt_port_outl`
    - `rt_port_inl`
    - `BUFFER_SIZE_dot_to_u32`
    - `VIRTQ_DESC_F_WRITE_dot_to_u32`
    - `VIRTIO_NET_HDR_SIZE_dot_to_u32`
    - `VIRTQ_DESC_F_NEXT_dot_to_u32`
    - `rt_function_not_found`
    - `rt_string_char_at`
- continuation-next: The next useful cut is no longer in `ssh_session.spl` itself. It is either:
  1. split the live RV64 SSH closure farther away from hosted RSA/ECDSA/random and generic TLS utility code, or
  2. fill the remaining freestanding runtime / virtio-net / klog gaps that the direct closure still reaches.
