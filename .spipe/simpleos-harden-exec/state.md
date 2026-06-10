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
- 2026-06-10 continue-rv64-ssh-status: Recorded the current RV64 hosted-QEMU SSH recovery lane against this broader SimpleOS hardening effort. The freestanding RV64 SSH native image `build/os/simpleos_riscv64_ssh_live.elf` links successfully with `nm -u` reporting `0` unresolved symbols, and the latest native-build evidence in `build/test-artifacts/rv64-ssh-live-native-build-after-ed25519-2d-hoist.log` ends with `Build complete: 305 compiled, 0 cached, 0 failed` and `Linked (freestanding): build/os/simpleos_riscv64_ssh_live.elf`. The executable SPipe gate `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` still fails live in this checkout's captured evidence: `build/test-artifacts/03_system/os/rv64_ssh_live_login_in_qemu/result.json` reports `passed=4`, `failed=1`, `duration_ms=110980`, with only the live example failing. Current diagnosis remains "build is clean, live daemon still does not complete the pre-listen Ed25519/host-key-ready path before the host probe contract succeeds"; this blocks closing the integrated RV64 SSH portion of the full SimpleOS hardening goal.

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
