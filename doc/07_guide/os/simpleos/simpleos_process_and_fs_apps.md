# SimpleOS Process-Backed & FS-Loaded Apps

**Version:** 1.0.0
**Status:** Code complete; FAT-backed raw-buffer handoff wired; live QEMU evidence still required for release claims

---

## Overview

SimpleOS loads applications from the FAT32 filesystem as OS-managed processes,
not as resident in-memory stubs. This guide covers the full stack: process
records, app manifests, syscall handling, VFS file reading, the launcher
registry, and the x86_64 fs-exec-spawn pipeline.

**Target model:** Apps are loaded from `/sys/apps/<name>` through VFS, launched
as kernel-scheduled processes with PIDs, and communicate with the window manager
through IPC.

**Six tool apps:**
`simple_browser`, `simple_compiler`, `simple_interpreter`, `simple_loader`,
`llvm`, `rust`

---

## Architecture

```
FAT32 Disk Image (scripts/os/make_os_disk.shs)
  /sys/apps/simple_browser.smf
  /sys/apps/simple_compiler.smf
  ...
     |
     v
VFS Layer (vfs_app_read.spl)
  canonical path: /sys/apps/<name>
  FAT32 alias resolution
     |
     v
App Loader Service (app_loader_service.spl)
  discovers apps from disk + registry
     |
     v
x86_64 FS Exec Spawn (x86_64_fs_exec_spawn.spl)
  reads bytes -> extracts SMF stub -> spawns process
     |
     v
Kernel Scheduler
  ProcessRecord with PID, status tracking
     |
     v
Window Manager IPC
  WmWindowHandle with owner PID
```

---

## Module Reference

### Process Apps (`src/os/process_apps/`)

#### ProcessRecord

Tracks a running OS process.

```simple
struct ProcessRecord:
    pid: i64
    app_path: text
    run_status: text     # "running" | "zombie" | "exited" | "faulted"
    exit_code: i64
    has_window: bool
```

| Function | Purpose |
|----------|---------|
| `ProcessRecord.new(pid, app_path)` | Create with status "running" |
| `.is_running()` / `.is_exited()` / `.is_zombie()` / `.is_faulted()` | Status checks |
| `.mark_exited(code)` / `.mark_zombie()` / `.mark_faulted(code)` | State transitions |
| `.with_window()` | Flag as having a WM window |

#### AppManifest

Declares an app's identity and capabilities.

```simple
struct AppManifest:
    app_id: text
    exec_path: text
    launch_mode: text    # "gui" | "cli" | "service"
    needs_window: bool
    needs_net: bool
```

| Function | Purpose |
|----------|---------|
| `AppManifest.gui_app(id, path)` | GUI app with window |
| `AppManifest.cli_app(id, path)` | CLI app, no window |
| `AppManifest.service_app(id, path)` | Background service |
| `.is_gui()` / `.is_cli()` / `.is_service()` | Mode checks |
| `.with_net()` | Enable network capability |

#### SyscallResult

Wraps kernel syscall return values.

```simple
struct SyscallResult:
    is_ok: bool
    retval: i64
    errno_code: i64
```

| Function | Purpose |
|----------|---------|
| `SyscallResult.ok(retval)` | Success |
| `SyscallResult.err(errno)` | Error with errno |
| `.enosys()` / `.einval()` / `.enomem()` / `.efault()` | Named error constructors |
| `.pid()` | Extract PID from retval (or -1) |

#### WmWindowHandle

Represents a window owned by a process.

```simple
struct WmWindowHandle:
    window_id: i64
    owner_pid: i64
    title: text
    ipc_status: text     # "pending" | "active" | "closed" | "hidden"
    width: i64
    height: i64
```

| Function | Purpose |
|----------|---------|
| `WmWindowHandle.create(wid, pid, title)` | Create pending window |
| `.activate(w, h)` | Activate with dimensions |
| `.close()` | Close window |
| `.is_process_backed()` | True if owner PID > 0 |
| `.matches_pid(pid)` | Check owner match |

---

### FS Apps Services (`src/os/services/fs_apps/`)

#### AppLoaderService

Discovers and manages app loading from the filesystem.

```simple
struct AppInfo:
    name: text
    path: text
    short_name: text
    on_disk: bool
    smf_present: bool
    fat32_alias: text
    pid: i64
    status: text
```

| Function | Purpose |
|----------|---------|
| `discover_apps()` | Scan FAT32 + app registry for available apps |

#### VfsReadProof / VfsProofSet

Tracks VFS file-read proofs for acceptance testing.

```simple
struct VfsReadProof:
    app_id: text
    source: text
    path: text
    bytes_read: i64
    emitted: bool
```

| Function | Purpose |
|----------|---------|
| `VfsReadProof.create(app)` | Create proof for app |
| `.record_read(sz)` | Record bytes read |
| `.is_valid_proof()` | True if bytes > 0 |
| `.serial_marker()` | Emit `[desktop-e2e] vfs-app-read:ok` |
| `VfsProofSet.all_ok()` | True if all 6 apps have valid reads |

#### ProcessBackedProof / BrowserProof / ToolchainProof

Proof structs for QEMU serial acceptance contract.

| Struct | Purpose |
|--------|---------|
| `ProcessBackedProof` | Generic: `.record_launch(pid)`, `.serial_marker()` emits `[desktop-e2e] process-backed:ok pid=N` |
| `BrowserProof` | Browser-specific: WM owner + render + page proofs |
| `ToolchainProof` | LLVM/Rust: native wrapper lane proofs |

#### LauncherToolApps

Registry of the 6 tool apps with canonical paths.

```simple
struct LauncherAppEntry:
    canonical_id: text       # e.g. "simple_browser"
    canonical_exec: text     # e.g. "/sys/apps/simple_browser"
    short_name: text         # FAT32 alias
    launch_state: text       # "idle" | "running"
    identity_match: bool
```

| Function | Purpose |
|----------|---------|
| `seed_tool_app_registry(reg)` | Register all 6 tool apps |
| `ToolAppRegistry.find_exec(name)` | Lookup executable path |
| `LauncherAppEntry.resolve_from_alias(alias)` | FAT32 alias resolution |

---

### x86_64 FS Exec Spawn (`src/os/kernel/loader/x86_64_fs_exec_spawn.spl`)

The main entry point for loading and spawning filesystem-backed processes.

| Function | Purpose |
|----------|---------|
| `x86_64_fs_exec_spawn(path, argv, envp)` | Main spawn: read bytes, extract SMF, emit markers, return PID |
| `x86_64_fs_exec_spawn_hello_world_smf()` | Backward-compat wrapper |
| `_x86_64_read_spawn_bytes_and_blob(path)` | Read executable and return the raw FAT buffer address when the byte source is FAT-backed |
| `x86_64_fs_exec_handoff_blob_ready(byte_len, raw_blob)` | Fail-closed gate: ring-3 handoff requires nonempty bytes and a resident raw buffer |
| `_x86_64_try_static_fat32_exec(path)` | Read from static FAT32 |
| `_x86_64_try_cached_exec(path)` | Try app registry cache |
| `_x86_64_try_fat32_exec_alias(path)` | Try FAT32 alias resolution |
| `_x86_64_spawn_static_seeded(path, argv, envp)` | Spawn with static-seeded PID |
| `_x86_64_exec_canonical_path(path)` | Canonicalize (strip .smf extension) |
| `_x86_64_static_fat32_alias(path)` | Map canonical path to FAT32 8.3 alias |
| `_x86_64_static_stub_size(path)` | Get static stub size for app |

**Byte resolution order:**
1. Static FAT32 exec (compiled-in)
2. FAT32 alias resolution
3. App registry cache
4. VFS file read (live filesystem)

Only the FAT-backed cases pass `simpleos_fat32_path_read_buffer_addr()` into
`x86_64_fs_exec_enter_image_ring3`. Cache-only or generic VFS array reads keep
`raw_blob=0` and fail closed rather than entering ring 3 from stale bytes.

---

## QEMU Acceptance Contract

The `src/os/qemu_runner.spl` serial contract expects these markers for each tool app:

```
[desktop-e2e] vfs-app-read:ok app=simple_browser bytes=NNN
[desktop-e2e] process-backed:ok pid=N app=simple_browser
```

**Special proofs:**
- `simple_browser`: WM owner, render, page-rendered markers
- `llvm` / `rust`: native-wrapper lane + toolchain markers

---

## Test Coverage

| Spec | Location | Coverage |
|------|----------|----------|
| Process apps unit | `src/os/process_apps/process_apps_spec.spl` (323 lines) | ProcessRecord, AppManifest, SyscallResult, WmWindowHandle |
| FS apps integration | `src/os/services/fs_apps/fs_apps_spec.spl` (504 lines) | VfsReadProof, ProcessBackedProof, BrowserProof, ToolchainProof, LauncherAppEntry |
| x86_64 exec/spawn | `test/03_system/compiler/x86_64_fs_exec_spawn_spec.spl` (19 lines) | Basic spawn contract |
| QEMU integration | `test/03_system/arm_smf_appscan_qemu_spec.spl` (83 lines) | ARM QEMU smoke |

---

## Known Runtime Blockers

| ID | Issue | Impact |
|----|-------|--------|
| FR-SOS-024 | Syscall 13 direct-spawn return-path fault | FAT-backed x86_64 spawn now passes the resident raw buffer to ring-3 handoff; rerun QEMU acceptance before removing this blocker |
| VFS-LIFETIME | `g_vfs_read_file_bytes()` C array lifetime corruption | VFS reads may return corrupt bytes |
| ELF-IMAGE | User-process image construction incomplete | Stack, auxv, entry, memory mappings |

All code modules are implemented (zero stubs). These are runtime integration issues that require kernel-level debugging.

---

## Related Docs

- App registration: `doc/07_guide/simpleos_app_registry.md`
- Executable format: `doc/07_guide/simpleos_executable_format.md`
- Desktop apps UI: `doc/07_guide/simpleos_apps.md`
- FS migration design: `doc/05_design/simpleos_fs_migration.md`
- FS current state research: `doc/01_research/simpleos_fs_current_state.md`
