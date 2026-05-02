# SimpleOS Filesystem Migration Plan
## From Direct FS Calls to FsDriver Trait

> Status: design proposal, 2026-04-18
> Author: research agent (session 4273dceb)
> Companion: `doc/01_research/simpleos_fs_current_state.md`

---

## 1. Executive Summary

SimpleOS currently has three parallel filesystem execution paths:

- **Path A** — Direct C externs (`rt_fat32_*`): used by all entry-point files at runtime
- **Path B** — OLD `Filesystem` trait via `VfsManager`: defined but mount table is always empty
- **Path C** — NEW `FsDriver` trait via `DriverInstance`/`MountTable`: fully designed but not connected to hardware

The migration consolidates all three paths into Path C. Path A is replaced by routing through `MountTable`. Path B is retired. Path C gains a real `Fat32Driver` implementation that calls through to the C runtime (or the pure-Simple FAT32 service in a later phase).

**M1 starting file**: `src/os/services/vfs/vfs_init.spl` — the single chokepoint where NVMe init and the VfsManager live.

---

## 2. Current vs. Target Call Graph

### 2.1 Current State (ASCII)

```
boot_stage2_entry.spl
  └─ vfs_boot_init()                  [vfs_init.spl]
       ├─ pcimgr_init()
       ├─ syscall(86) NvmeInit         [C runtime]
       └─ g_vfs_initialized = true
            └─ (mount table EMPTY — nothing mounted)

fs_test_entry.spl / shell_serial_entry.spl
  ├─ vfs_boot_init()                  [side-effect: NVMe init only]
  ├─ extern rt_fat32_read_file_text() [C runtime — bypasses all traits]
  ├─ extern rt_fat32_file_size()      [C runtime]
  └─ extern rt_fat32_file_exists()    [C runtime]

src/os/services/fat32/fat32.spl
  └─ Fat32Volume : Filesystem         [OLD trait — never instantiated at boot]
       └─ BlockDevice.read_sector()

src/lib/nogc_sync_mut/fs_driver/
  └─ FsDriver trait + DriverInstance  [NEW trait — defined, not connected]
       ├─ NvfsDriver  (real)
       ├─ NvfsPosixDriver (real, Phase 9 B2)
       ├─ Fat32Driver (STUB — all Err(Unsupported))
       └─ RamFsStub (stub)
```

### 2.2 Target State (ASCII)

```
boot_stage2_entry.spl
  └─ vfs_boot_init()                  [vfs_init.spl — MODIFIED]
       ├─ pcimgr_init()
       ├─ NvmeDriver.init()            [syscall 86]
       ├─ g_c_adapter = CNvmeBlockAdapter(nvme)
       ├─ fat32_drv = Fat32DriverImpl(g_c_adapter)  ← NEW
       ├─ g_mount_table.mount("/", DriverInstance.Fat32(fat32_drv))  ← NEW
       └─ g_vfs_initialized = true

fs_test_entry.spl / shell_serial_entry.spl
  ├─ vfs_boot_init()
  └─ g_mount_table.resolve("/hello.txt")
       └─ DriverInstance.Fat32(d) → d.open/read/close  ← replaces rt_fat32_*

src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl → fat32_impl.spl  ← REPLACED
  └─ Fat32DriverImpl : FsDriver
       └─ CNvmeBlockAdapter.read_sector() / write_sector()
            └─ syscall 85/94

src/os/services/fat32/fat32.spl       ← RETIRED (or kept as library)
src/os/services/vfs/vfs.spl           ← RETIRED (Filesystem trait removed)
```

---

## 3. Phase Plan

### M1 — Wire Fat32Driver into MountTable at Boot
**Goal**: After `vfs_boot_init()`, `g_mount_table.resolve("/")` returns `DriverInstance.Fat32(...)` with a real driver. Direct C externs still work alongside (no regressions).

**Files to touch**:
- `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` → promote to `fat32_impl.spl`
- `src/os/services/vfs/vfs_init.spl` — mount Fat32DriverImpl into `g_mount_table`

**Acceptance criteria**:
- `vfs_boot_init()` returns `true` and `g_mount_table.resolve("/hello.txt")` succeeds
- `Fat32DriverImpl.open("/hello.txt", READ)` returns `Ok(FileHandle)`
- `Fat32DriverImpl.read(handle, 0, buf)` returns expected bytes
- All existing `rt_fat32_*` externs still work (no entry-point changes yet)

**Risk**: Low. The C driver and pure-Simple path are additive; nothing is removed.

**Rollback**: Delete `fat32_impl.spl`; revert `vfs_init.spl` to previous version.

---

### M2 — Replace Direct C Externs in Entry Points
**Goal**: `fs_test_entry.spl` and `shell_serial_entry.spl` call through `g_mount_table` instead of `rt_fat32_*` externs.

**Files to touch**:
- `examples/simple_os/arch/x86_64/fs_test_entry.spl`
- `examples/simple_os/arch/x86_64/shell_serial_entry.spl`

**Migration pattern** (per call site):
```
# BEFORE
var text = rt_fat32_read_file_text("hello.txt")

# AFTER
var result = g_mount_table.resolve("/hello.txt")
match result:
    case Ok(mount_id):
        var drv_result = g_mount_table.lookup(mount_id)
        match drv_result:
            case Ok(entry):
                # open + read + close via FsDriver dispatch
            case Err(e): ...
    case Err(e): ...
```

**Acceptance criteria**:
- `fs_test_entry.spl` tests for `hello.txt`, `numbers.txt`, `hello.spl` all pass
- Shell file-read commands return same output as before
- No `extern rt_fat32_read_file_text` references remain in entry-point `.spl` files

**Risk**: Medium. Entry points are boot-critical; a regression here means no working shell.

**Rollback**: Revert entry-point files to previous version.

---

### M3 — Retire OLD Filesystem Trait and VfsManager
**Goal**: Remove `src/os/services/vfs/vfs.spl` (OLD `Filesystem` trait + `VfsManager`) and all its consumers.

**Pre-requisite**: M1 and M2 complete. Verify that no file imports `VfsManager` or `Filesystem` trait from `vfs.spl`.

**Files to touch**:
- `src/os/services/vfs/vfs.spl` — delete
- `src/os/services/vfs/vfs_init.spl` — remove `g_vfs: VfsManager` global, `use vfs.{VfsManager}`, all `g_vfs.*` calls
- Any file importing `VfsManager` (search: `use std.vfs.{VfsManager}` or `use os.services.vfs.vfs`)

**Acceptance criteria**:
- `bin/simple build` succeeds with no reference to `VfsManager` or `Filesystem` trait
- No `.spl` file imports from `src/os/services/vfs/vfs.spl`

**Risk**: Low — `VfsManager` mount table was always empty at runtime. No code was actually dispatching through it.

**Rollback**: Restore `vfs.spl` from git; revert `vfs_init.spl`.

---

### M4 — Implement Real Fat32Driver (Replace C-extern Delegation)
**Goal**: `Fat32DriverImpl` calls the pure-Simple `Fat32Volume` (`src/os/services/fat32/fat32.spl`) over `CNvmeBlockAdapter` rather than delegating to C externs. This completes the all-Simple FAT32 path.

**Files to touch**:
- `src/lib/nogc_sync_mut/fs_driver/fat32_impl.spl` (from M1) — replace C-extern delegation with `Fat32Volume` calls
- `src/os/services/fat32/fat32.spl` — adapt `BlockDevice` trait to match `CNvmeBlockAdapter`'s interface if needed

**Acceptance criteria**:
- `Fat32DriverImpl.read()` returns correct bytes without calling any `rt_fat32_*` extern
- `Fat32DriverImpl.write()` persists data readable on next read
- Kernel tests pass (`fs_test_entry.spl`)
- No `extern rt_fat32_*` calls remain anywhere (search confirms)

**Risk**: Medium-High. Pure-Simple FAT32 has not been exercised at boot. Likely to expose cluster-chain bugs or sector-alignment issues.

**Mitigation**: Keep C externs as a fallback for the first boot cycle during development; run both paths in parallel and diff results.

**Rollback**: Revert `fat32_impl.spl` to C-extern delegation from M1.

---

### M5 — Add RamFsDriver and Multi-Mount Support
**Goal**: Replace `RamFsStub` with a real in-memory filesystem. Mount FAT32 at `/`, RamFs at `/tmp`. Verify `resolve()` correctly dispatches by prefix.

**Files to touch**:
- New file: `src/lib/nogc_sync_mut/fs_driver/ramfs_impl.spl`
- `src/lib/nogc_sync_mut/fs_driver/instance.spl` — update `RamFs` variant to `RamFsDriver` (real type)
- `src/os/services/vfs/vfs_init.spl` — mount RamFs at `/tmp`

**Acceptance criteria**:
- `g_mount_table.resolve("/tmp/foo")` dispatches to `RamFsDriver`
- `g_mount_table.resolve("/hello.txt")` dispatches to `Fat32DriverImpl`
- `RamFsDriver.write("/tmp/foo", ...)` followed by `read("/tmp/foo")` returns same data
- Data in `/tmp` does not persist across `vfs_boot_init()` calls (volatile by design)

**Risk**: Low (new code, no regressions in existing paths).

---

## 4. Compatibility Shims

### 4.1 C-Extern Compatibility Period (M1–M3)

During M1 and M2, `rt_fat32_*` externs remain available in `baremetal_stubs.c`. New FsDriver path is additive. This allows:
- A/B comparison: read same file via both paths, assert equality
- Incremental rollout: migrate one entry-point file at a time

Remove `rt_fat32_*` RuntimeValue wrappers from `baremetal_stubs.c` only after M4 acceptance criteria pass.

### 4.2 Filesystem → FsDriver Adapter (Optional, for M3)

If any code outside the inventory still uses the OLD `Filesystem` trait, a thin adapter can wrap a `FsDriver` implementation:

```
struct FsDriverAdapter:
    inner: DriverInstance

impl Filesystem for FsDriverAdapter:
    fn open(path: text, flags: i32) -> Result<i32, text>:
        var r = self.inner.open(Path(path), OpenFlags(flags))
        r.map_err(fn(e) -> text: e.to_text())
          .map(fn(h) -> i32: h.raw_id())
    # ... etc
```

This adapter is a bridge, not a long-term target. Retire it when M3 is done.

### 4.3 `vfs_is_ready()` Migration

`boot_stage2_entry.spl` and `boot_stage3_entry.spl` call `vfs_is_ready()` which checks `g_vfs_initialized`. This flag stays valid through all phases — it means "NVMe is up and FAT32 is mountable," not "VfsManager is populated." No change required in M1–M3. Rename to `fs_is_ready()` in M5 cleanup.

---

## 5. Risk Analysis

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|-----------|
| Pure-Simple FAT32 cluster-chain bug at boot | Medium | High | Run C and Simple paths in parallel (M4); compare byte-for-byte |
| Entry-point regression (shell reads empty) | Low | High | Keep C externs until M2 tests pass |
| `MountTable.resolve()` prefix bug | Low | Medium | Unit test with overlapping mounts before M5 |
| NvfsDriver/Fat32Driver trait mismatch | Low | Low | Compiler catches all mismatches at build time |
| arm64/riscv64 builds broken by x86_64-only Fat32 | Medium | Medium | Guard `Fat32DriverImpl` construction behind `#[target(x86_64)]` |
| RamFs data corruption on reboot | Low | Low | By design (volatile); document in RamFsStub docstring |

---

## 6. Files to Touch — Complete List

### M1
| File | Action |
|------|--------|
| `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` | Replace stub body with real `Fat32DriverImpl` using `CNvmeBlockAdapter` |
| `src/os/services/vfs/vfs_init.spl` | Add mount of Fat32DriverImpl into `g_mount_table` after NVMe init |
| `src/lib/nogc_sync_mut/fs_driver/instance.spl` | Ensure `Fat32` variant type matches new impl struct name |

### M2
| File | Action |
|------|--------|
| `examples/simple_os/arch/x86_64/fs_test_entry.spl` | Replace `rt_fat32_*` calls with `g_mount_table` dispatch |
| `examples/simple_os/arch/x86_64/shell_serial_entry.spl` | Replace `rt_fat32_*` calls with `g_mount_table` dispatch |

### M3
| File | Action |
|------|--------|
| `src/os/services/vfs/vfs.spl` | Delete |
| `src/os/services/vfs/vfs_init.spl` | Remove `g_vfs: VfsManager`, all `g_vfs.*` calls, OLD trait imports |

### M4
| File | Action |
|------|--------|
| `src/lib/nogc_sync_mut/fs_driver/fat32_impl.spl` | Replace C-extern delegation with `Fat32Volume` calls |
| `src/os/services/fat32/fat32.spl` | Align `BlockDevice` trait with `CNvmeBlockAdapter` if needed |
| `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` | Remove `rt_fat32_*` RuntimeValue wrappers (after M4 tests pass) |

### M5
| File | Action |
|------|--------|
| `src/lib/nogc_sync_mut/fs_driver/ramfs_impl.spl` | Create new RamFsDriver |
| `src/lib/nogc_sync_mut/fs_driver/instance.spl` | Update `RamFs` variant to use `RamFsDriver` |
| `src/os/services/vfs/vfs_init.spl` | Mount RamFs at `/tmp` |

---

## 7. Acceptance Criteria — Per Phase

### M1 Done When
- [ ] `vfs_boot_init()` completes with no panic and `g_mount_table` has one entry at `"/"`
- [ ] `Fat32DriverImpl.open("/hello.txt", READ)` returns `Ok(FileHandle)`
- [ ] `Fat32DriverImpl.read(handle, 0, buf_256)` returns `Ok(bytes_read > 0)` with expected content
- [ ] `bin/simple build` passes
- [ ] Existing boot tests pass (no regressions)

### M2 Done When
- [ ] `fs_test_entry.spl` produces identical output via FsDriver path vs. old C-extern path
- [ ] `shell_serial_entry.spl` can read/write files through `g_mount_table`
- [ ] `grep -r "rt_fat32_" examples/simple_os/arch/x86_64/*.spl` returns no results

### M3 Done When
- [ ] `bin/simple build` succeeds with `vfs.spl` deleted
- [ ] `grep -r "VfsManager\|Filesystem" src/ --include="*.spl"` returns no results

### M4 Done When
- [ ] `grep -r "rt_fat32_" examples/ --include="*.spl"` returns no results
- [ ] `grep "rt_fat32_" baremetal_stubs.c` returns no RuntimeValue wrappers
- [ ] All `fs_test_entry.spl` tests pass
- [ ] Read-after-write consistency test passes

### M5 Done When
- [ ] `/tmp/test.txt` write + read roundtrip passes
- [ ] Mount prefix test: `/tmp/x` → RamFs, `/data/x` → Fat32
- [ ] Reboot (re-run `vfs_boot_init()`) clears `/tmp` contents

---

## 8. Open Questions

1. **`BlockDevice` trait alignment**: `fat32.spl` defines its own `BlockDevice` trait returning `Result<bool, text>`. `CNvmeBlockAdapter` in `vfs_init.spl` also implements some form of this. Are these the same trait or two separate definitions? Must be unified in M1/M4.

2. **`g_mount_table` global placement**: Should `g_mount_table: MountTable` live in `vfs_init.spl` alongside `g_vfs` (and replace it), or should it move to a new `fs_state.spl` module? The simplest approach is replacement in `vfs_init.spl` for M1.

3. **arm64/riscv64 Fat32**: The C FAT32 driver is x86_64-only. For non-x86 targets, `Fat32DriverImpl` construction must be gated, or a separate block device adapter must be provided. Scope this before M4.

4. **Kernel BPB parser**: `src/os/kernel/fs/fat32.spl` (kernel-internal read path) is a third FAT32 implementation that is separate from both the C driver and the pure-Simple service. Does it need to migrate to `FsDriver` as well, or is it kernel-private forever?

5. **FdTable integration**: `NvfsPosixDriver` uses its own `FdTable` (`posix/fd_table.spl`). The OLD `Filesystem` trait used `i32` file descriptors (raw). Should the NEW system expose a unified per-process fd table, or is per-driver fd management acceptable for M1–M3?

6. **`MountTable.resolve()` semantics**: Current `resolve(path)` returns a `MountId`. Entry-point code must then call `lookup(mount_id)` to get the `DriverInstance`. Is this the right ergonomic for caller code, or should `resolve()` return `(MountId, &DriverInstance)` directly?

---

## 9. Rollback Plan

All phases are independently revertable via `jj undo` or `git revert`:

| Phase | Rollback action |
|-------|----------------|
| M1 | Delete `fat32_impl.spl`; revert `vfs_init.spl` to pre-M1 commit |
| M2 | Revert `fs_test_entry.spl` and `shell_serial_entry.spl` |
| M3 | Restore `vfs.spl` from git; revert `vfs_init.spl` |
| M4 | Revert `fat32_impl.spl` to M1 version (C-extern delegation); restore `baremetal_stubs.c` wrappers |
| M5 | Delete `ramfs_impl.spl`; revert `instance.spl` and `vfs_init.spl` |

No phase requires force-push or destructive git operations. Each phase leaves a working system.

---

## 10. Recommended Starting Point

**Start with M1, file: `src/os/services/vfs/vfs_init.spl`**

Reason: this is the single initialization chokepoint. After NVMe init (syscall 86) succeeds, all required pieces are available:
- `g_c_adapter: CNvmeBlockAdapter` wraps sector read/write
- `g_nvme: NvmeDriver` is initialized
- The gap is explicit: `g_vfs_initialized = true` is set without mounting anything

Adding three lines — construct `Fat32DriverImpl(g_c_adapter)` and call `g_mount_table.mount("/", DriverInstance.Fat32(drv))` — closes the architectural gap and gives every subsequent phase a real dispatch target to build on.

The companion research document at `doc/01_research/simpleos_fs_current_state.md` provides the full call-site inventory, struct definitions, and architectural findings that informed this plan.
