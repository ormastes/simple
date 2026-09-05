# Lane VFSBYPASS — closing the `g_vfs_*` free-function bypass

Date: 2026-07-28. Follows lane CONTWIRE2 (`.spipe/container_live_wiring/state.md`),
which wired `VfsManager` path ops through one deny-wins gate
(`enforce_lookup_grants`) and honestly reported that the `g_vfs_*` free functions
in `vfs_write_ops.spl` bypass that gate entirely.

## 1. Survey (written BEFORE editing)

### 1a. The identity question, answered once

None of the `g_vfs_*` callers carry caller identity, and none *can* today: there
is no process→VfsManager binding in SimpleOS. But the free functions are not
identity-free in the way "no identity" suggests — they are **ambient**, and the
ambient VFS identity already exists and is already gated: the module global
`g_vfs: VfsManager` (`vfs_boot_init.spl:75`), the very object CONTWIRE2 hung
`container_view` on. `g_vfs_readdir` already proves the shape by delegating to
`g_vfs.readdir`.

So the closure is **not** a second gate. It is: every ambient path op asks the
one ambient manager the one question, via `g_vfs.enforce_lookup_grants`.
`container_view_allows_path` remains the single decision owner.

### 1b. Per-function survey — three-way outcome

`src/os/services/vfs/vfs_write_ops.spl`

| # | Function | `pub` | Reaches storage? | Identity | **Outcome** |
|---|---|---|---|---|---|
| 1 | `g_vfs_abs_path(name)` | no | no — pure path arithmetic | n/a | **(iii→delete-dup)** duplicated verbatim in `vfs_init.spl:80`. Deleted the `vfs_init` copy; `vfs_init` imports the one in `vfs_write_ops`. No gate: it decides nothing. |
| 2 | `g_vfs_root_path(name)` | no | no | n/a | **(iii→delete-dup)** same, `vfs_init.spl:87`. |
| 3 | `g_vfs_root_write_file_text(driver,…)` | no | YES | takes an explicit driver | **(iii→explicitly internal)** module-private helper of #9; already unreachable from outside. Renamed nothing; gate applied at its only caller. |
| 4 | `g_vfs_root_write_file_bytes(driver,…)` | no | YES | explicit driver | **(iii→internal)** same, caller #10. |
| 5 | `g_vfs_root_file_exists(driver,…)` | no | YES (stat) | explicit driver | **(iii→internal)** same, caller #12. |
| 6 | `_g_vfs_root_nvfs_hosted_*` (write_text/write_bytes/file_exists/file_size) | no | YES | none | **(iii→internal)** private, reachable only through the gated pub wrappers. |
| 7 | `g_vfs_select_file` / `g_vfs_get_selected_file` / `g_vfs_clear_selected_file` | yes | no — cursor state only | n/a | **(i, no change)** they touch no filesystem. Gating a cursor set would be a second envelope. |
| 8 | `g_vfs_write_selected_file_text(content)` | no | YES (via #9) | none | **(iii→DELETED)** an unauthenticated write entry point with **zero callers** anywhere in `src/` or `test/`. Per §3 of the brief, a reachable-but-unauthenticated write is worse than a missing feature; an *unreachable* one is pure liability. Deleted, not gated. |
| 9 | `g_vfs_write_file_text(name, content)` | **yes** | YES | ambient | **(ii→GATED)** the real bypass. Now calls `vfs_ambient_enforce("write", path)` and returns `false` on deny. |
| 10 | `g_vfs_write_file_bytes(name, data)` | **yes** | YES | ambient | **(ii→GATED)** same. |
| 11 | `g_vfs_delete_file(name)` | **yes** | YES | ambient | **(ii→GATED)** `"unlink"`. |
| 12 | `g_vfs_file_exists(name)` | **yes** | YES (stat, 4 fallback lanes) | ambient | **(ii→GATED)** `"stat"`. Existence is an information leak across a namespace boundary — gated at entry so **none** of the four fallback lanes (root FAT32, nvfs, mount table, C-bridge) runs under a denying view. |
| 13 | `g_vfs_readdir(path)` | **yes** | via `g_vfs.readdir` | ambient | **(i, ALREADY ENFORCED)** it delegates to the CONTWIRE2-gated `VfsManager.readdir`. Verified, not re-gated — re-gating would be the duplicate §4 forbids. |
| 14 | `vfs_mount_removable(dev, path)` | **yes** | YES — mutates the global mount table | ambient | **(ii→FAIL-CLOSED)** mounting is namespace *construction*; a confined caller must never do it. Refused whenever `g_vfs.in_container()`, regardless of path. |
| 15 | `vfs_unmount_removable(path)` | **yes** | YES | ambient | **(ii→FAIL-CLOSED)** same; unmounting another namespace's mount is an escape. |
| 16 | `_vfs_bytes_to_text(buf, count)` | no | no | n/a | **(iii→DELETED)** dead in this module (live copies in `vfs_dispatch.spl`/`vfs_init.spl`). |

`src/os/services/vfs/vfs_init.spl` (read side, same ambient shape)

| # | Function | Outcome |
|---|---|---|
| 17 | `g_vfs_read_file_text` / `g_vfs_read_file_bytes` / `g_vfs_file_size` / `g_vfs_read_executable_bytes` / `g_vfs_read_fat32_path_bytes` | **(ii→GATED)** ambient reads, same treatment: `vfs_ambient_enforce("read", path)` at entry, empty/`nil` on deny. A namespace that can read `/etc/shadow` is not confined. |
| 18 | `g_vfs_abs_path`, `g_vfs_root_path`, `_vfs_text_to_bytes` | **(iii→DELETED)** duplicates/dead; see #1, #2. |
| 19 | `vfs_mount_rootfs`, `vfs_mount_rootfs_from_nvme_lease_checked` | **(iii→internal/boot)** boot-time root construction, runs before any container exists. Left ungated deliberately: gating boot on a view that cannot yet exist would be theatre. Recorded, not closed. |

`src/os/services/vfs/vfs_boot_init.spl`

| # | Function | Outcome |
|---|---|---|
| 20 | `g_vfs_root_read_file_bytes(driver, path)` @2164 | **(iii→DELETED)** dead duplicate of `vfs_init.spl:338`; no caller in the module or anywhere. |
| 21 | new `vfs_ambient_*` accessors | the gate surface, defined in the module that **owns** `g_vfs` (see landmine note below). |

### 1c. Callers, and why none of them can be handed identity today

| Caller | Function used | Identity available? |
|---|---|---|
| `src/os/desktop/z_order_store.spl:178` | `g_vfs_write_file_bytes` | no — desktop store, no task handle |
| `src/os/services/package_installer.spl:24,50,65` | write_bytes, delete_file | no |
| `src/os/apps/dbd/dbd.spl:114,130` | file_exists, write_bytes | no |
| `src/os/kernel/boot/boot_fs.spl:384`, `rc_conf.spl:60`, `net/http_baremetal.spl:50`, `boot/http_baremetal.spl:93` | file_exists | no — boot/host context |
| `src/os/kernel/arch/riscv{32,64}/console.spl`, `src/os/apps/file_manager`, `src/os/desktop/app_manifest.spl`, `src/os/services/fs_apps/app_loader_service.spl` | `g_vfs_readdir` | no — already enforced via `g_vfs` |
| `src/os/services/removable_manager.spl:27,42` | mount/unmount removable | no |

Every one of them is host/boot context today, so every one of them keeps working
unchanged (`container_view == nil` → `Ok(true)`, the CONTWIRE2 no-regression
contract). That is the non-container regression argument, and it is spec'd
explicitly rather than asserted.

## 2. Out of scope, stated rather than half-done

* **Pid lookup stays out.** `pt_ext_lookup` / `schedctl_op_get_*` are
  scheduler- and ipc-owned (`src/os/kernel/scheduler/**`,
  `src/os/kernel/ipc/**`) and are not this lane's paths. Not touched, not
  half-plumbed. CONTWIRE2's filing stands.
* **Who calls `vfs_ambient_enter_container_view`** is still unanswered — same
  gap CONTWIRE2 named. This lane closes the *bypass* (the parallel entry point
  that ignored the view); it does not create the process→view binding. Honest
  statement: with no binding, the ambient view is only ever set by a container
  supervisor or a spec. The bypass being closed means that when the binding
  lands, it lands on **one** path instead of two.
* **Boot-time mount construction** (#19) deliberately ungated.

## 3. Lines deleted

| File | What | Lines |
|---|---|---|
| `vfs_write_ops.spl` | `_vfs_bytes_to_text` (dead) | 10 |
| `vfs_write_ops.spl` | `g_vfs_write_selected_file_text` (unauthenticated, zero callers) | 6 |
| `vfs_init.spl` | `g_vfs_abs_path` + `g_vfs_root_path` (verbatim duplicates) | 14 |
| `vfs_init.spl` | `_vfs_text_to_bytes` (dead duplicate) | 3 |
| `vfs_boot_init.spl` | `g_vfs_root_read_file_bytes` (dead duplicate) | 21 |
| **total** | | **54** |

(Filled in after the edits; see §5 for the measured diffstat.)

## 4. Enforcement matrix

See `test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl`.

## 5. Verification

(filled below)
