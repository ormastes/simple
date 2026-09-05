# Lane CONTWIRE — container isolation on the live lookup path

Date: 2026-07-27. Scope: Phase 5 row "live lookup-site wiring".

## 1. Lookup-site survey (done BEFORE editing)

### 1a. Path resolution

| Site | File | Container context available? | What would have to be threaded |
|---|---|---|---|
| `VfsManager.open/stat/readdir/mkdir/rmdir/unlink/rename/symlink` | `src/os/services/vfs/vfs.spl` | **NO container context — but a per-instance context slot already exists** (`ai_cli_manifest: AiCliManifest?`) and every one of those ops already funnels through one choke point, `enforce_ai_cli_file_grant(operation, path)`. | A sibling optional slot holding the caller's `ContainerNamespaceView`, set/cleared by whoever enters/leaves a container context. **This is the wirable site.** |
| `VfsManager.resolve_mount_index` / `resolve_mount` / `strip_mount_prefix` | same | n/a — pure prefix arithmetic below the gate | nothing; enforcing here would be a second envelope |
| `VfsHandleTable.lookup(vfs_handle)` | `src/os/kernel/fs/vfs_handle_table.spl` | **NO — and correctly so.** It resolves an *already-issued* handle back to its mount. Handles are only issued by `VfsManager.open`, which is gated. | nothing. Gating here would double-charge; the capability is the handle. |
| `g_vfs_*` free functions (`g_vfs_write_file_text`, `g_vfs_readdir`, `g_vfs_file_exists`, ...) | `src/os/services/vfs/vfs_write_ops.spl` | **NO — module-global, no caller identity at all.** They talk to a global `Fat32Core`/nvfs, not to a `VfsManager`. | a caller-identity parameter or a task-local current-view. Multi-session; **NOT wired**, boot path. |
| `g_vfs: VfsManager` global | `src/os/services/vfs/vfs_boot_init.spl:75` | host context | nothing — stays host (view `nil`), so **boot is untouched**. |

### 1b. Pid resolution

| Site | File | Container context available? | Verdict |
|---|---|---|---|
| `pt_ext_lookup(pid)`, `pt_ext_reap`, `pt_ext_address_space_for` | `src/os/kernel/scheduler/process_table_extended.spl` | **NO.** Module-global table, no per-caller context, no instance to hang a view on. | **Plan only.** Also outside this lane's owned paths (`src/os/kernel/scheduler/**` is not owned). |
| `schedctl_op_get_*(pid)` | `src/os/kernel/ipc/syscall_scheduler.spl` | NO | **Plan only** — `src/os/kernel/ipc/**` is an explicitly forbidden live lane. |
| `ContainerWorld.allows_pid/pid_decision` | `src/os/services/container/container_manager.spl` | yes (model) | already delegates to the kernel primitive; still model-only. |

**Honest answer:** container context is plumbed to *exactly one* real lookup family
— `VfsManager`'s path ops — and to *no* pid lookup site at all. So this lane wires
the VFS path family for real and leaves pid enforcement as a written plumbing plan.

## 2. What was wired (real, live path)

`src/os/services/vfs/vfs.spl`:

* new field `container_view: ContainerNamespaceView?` on `VfsManager`
  (explicitly `nil` in **both** constructors — never omitted, per the
  "omitted defaulted fields nil-fill to 3 on the JIT" landmine);
* `enter_container_view(view)` / `enter_container(root, pids)` / `leave_container()` /
  `in_container()`;
* `enforce_container_namespace(operation, path)` — delegates to
  `container_view_allows_path` from `src/os/kernel/loader/container_namespace.spl`.
  **No second enforcement path**: it re-implements nothing, it calls the kernel primitive.
* `enforce_lookup_grants(operation, path)` — the converged choke point.
  **Deny-wins**: ai-cli grant must allow AND the namespace must allow.
  All 10 former `enforce_ai_cli_file_grant` call sites (open, stat, readdir,
  mkdir, rmdir, unlink, rename×2, symlink×2) now call it.

Fail-closed properties that follow, without any new logic:

* `container_view == nil` → **host context, unaffected** (early `Ok(true)`, identical
  to the pre-change behaviour — this is the no-regression contract);
* a rootless view (`root == ""`) denies *every* path → a container whose view was
  never populated resolves nothing;
* `..` is refused, never normalized (kernel primitive);
* a **stopped/exited** container already has its view reset to
  `container_view_rootless()` by `ContainerWorld.sys_stop` (vfs.spl-external,
  container_manager.spl:478) and by the reaper (:547) — so handing the VFS a
  stopped container's view yields a view that resolves nothing. That is the live
  link between lifecycle and lookup.

`src/os/services/container/container_manager.spl`: added `kernel_view_of(idx)`,
the single accessor a lookup site uses to obtain the enforced view. No behaviour change.

## 3. What still needs plumbing (NOT wired, deliberately)

1. **Who calls `enter_container_view`.** Today the spec and any container-aware
   caller does. There is no process-to-VfsManager binding in SimpleOS: the boot
   VFS is a module global (`g_vfs`) shared by everyone. A real per-task current
   view needs either (a) a task-local slot in the scheduler's process entry, or
   (b) a per-container `VfsManager` instance handed to the container's tasks.
   (b) is smaller and is the recommended next increment.
2. **Pid enforcement.** `pt_ext_lookup` needs a `caller_view` parameter (or a
   task-local current view) before `container_view_allows_pid` can gate it.
   Owner lane: scheduler. Filed here, not attempted (out of owned paths).
3. **`g_vfs_*` free functions** in `vfs_write_ops.spl` bypass `VfsManager`
   entirely. Anything a container reaches through those is *not* enforced.
   Not touched — boot path.
4. **QEMU/boot evidence** remains blocked; nothing here is armed on a boot path.

## 4. Enforcement test matrix

`test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl`
(mock `Filesystem`, no I/O, no boot).

| # | Scenario | Expectation |
|---|---|---|
| 1 | host context (`container_view` nil): open/stat/readdir/mkdir/unlink | all succeed — **no regression for non-container callers** |
| 2 | host context: `in_container()` | false |
| 3 | container A rooted `/containers/a`: in-root open/stat/readdir/mkdir | allowed |
| 4 | **same path**, container B rooted `/containers/b` | refused |
| 5 | container A: `..` traversal | refused (never normalized) |
| 6 | container A: sibling/host path `/containers/b/x`, `/etc/shadow` | refused |
| 7 | stopped container (rootless view, as `sys_stop` leaves it) | every lookup refused — fail-closed |
| 8 | `leave_container()` returns to host semantics | succeeds again |
| 9 | write-side ops (unlink/rename/symlink) obey the same gate; rename/symlink deny if **either** endpoint is out of view | refused |
| 10 | deny-wins with ai-cli manifest also present | still refused |

## 5. Deliberate-red calibration (DONE — two independent points)

**RED-1 — namespace gate removed from the converged choke point.**
`enforce_lookup_grants` short-circuited with `return Ok(true)` before calling
`enforce_container_namespace`, i.e. only the ai-cli grant remains.
→ `build/contwire_red1.log`: **13 total, 3 passed, 10 failed.**
The 10 reds are every denial row (cross-container same-path, host/traversal
escape, leave/return, rootless ×2, rename dest, symlink target, unlink/rmdir,
deny-wins, refusal message). The 3 survivors are exactly the rows that must NOT
depend on denial: host-context no-regression, `in_container()` reporting, and
in-root allow. That split is the calibration — it proves the host rows are green
for the right reason, not because the gate is inert.

**RED-2 — fail-closed inverted for rootless/stopped views only.**
`enforce_container_namespace` given an early `if view.root == "": return Ok(true)`
(a rootless view treated as host context).
→ `build/contwire_red2.log`: **13 total, 11 passed, 2 failed** — precisely
"resolves nothing under a rootless view" and "treats the explicit rootless entry
point the same way". Surgical: nothing else moved, so the stopped-container
fail-closed rows are independently load-bearing and not piggybacking on RED-1's
gate.

Both reverts verified byte-identical to the pre-red file (`diff` vs
`/tmp/contwire_backup/vfs.spl` → clean), then re-run green:
`build/contwire_green_after_red.log` — **13/13, 0 failures.**

## 6. Run log

Tool: `bin/simple test <spec>`. Engine A = default (JIT), engine B = `SIMPLE_NO_JIT=1`.
Per-describe block counts recorded, never a whole-suite run.

| Run | Log | Result |
|---|---|---|
| new spec, JIT | `build/contwire_run2.log` | **13/13** (blocks 2,4,2,3,2) |
| new spec, interpreter (`SIMPLE_NO_JIT=1`) | `build/contwire_ab_interp.log` | **13/13** (blocks 2,4,2,3,2) — A/B agree |
| RED-1 | `build/contwire_red1.log` | 3 pass / 10 fail (expected) |
| RED-2 | `build/contwire_red2.log` | 11 pass / 2 fail (expected) |
| green after revert | `build/contwire_green_after_red.log` | **13/13** |

### Non-container regression evidence

| Spec | Log | Result |
|---|---|---|
| `container_escape_suite_spec.spl` (**not edited**, 32 attacks) | `build/contwire_final_escape.log` | **32/32 PASS** |
| `container_manager_spec.spl` | `build/contwire_reg_cm.log` | **8/8 PASS** |
| `vfs_chmod_symlink_spec.spl` | `build/contwire_reg_vfs_chmod_symlink_spec.log` | **3/3 PASS** |
| `vfs_spec.spl` **with** the change | `build/contwire_reg_vfs_spec.log` | 19 total, 7 pass, 12 fail |
| `vfs_spec.spl` **at `git show HEAD:vfs.spl`** (baseline re-run this session) | `build/contwire_baseline2_vfs_spec.log` | 19 total, 7 pass, **12 fail** |

`vfs_spec.spl`'s 12 reds are **PRE-EXISTING**, not caused by this lane: the
failing-example name sets from the HEAD baseline and from the changed tree are
**identical** (`diff` of the two extracted `✗` lists is empty, 12 each), and the
baseline was produced by restoring `git show HEAD:` over the file, running, then
restoring the working copy (`diff` clean afterwards).

Lint: `vfs.spl` clean. `container_manager.spl` reports 2× `COLL006` at line 141
(`caps_is_subset`) — **pre-existing**: linting `git show HEAD:` of the same file
reports the identical 2 errors. Spec warnings are style-only (`stub_impl` on the
mock `Filesystem`'s trivial `Ok(0)` returns, which is what a mock should return).

### Landmine compliance
No `x.f += v` (all compound writes spelled out). No `Some(<i64>)`. No `index_of`
nil-guards. No omitted defaulted struct fields — `container_view: nil` is passed
explicitly in **both** `VfsManager` constructors. No module-global written inside
a function. Backup kept out of tree at `/tmp/contwire_backup/` and working-copy
content re-verified against it after every red/revert cycle.

## 7. Ledger

`doc/08_tracking/os/production_status.sdn` — **only** the `containers:` `note:`
line changed (line 67). It separates ENFORCED LIVE (the VfsManager path family)
from STILL MODEL-ONLY (no task→view binding, pid lookup ungated, `g_vfs_*` free
functions unenforced, nothing on a boot path) and keeps QEMU/boot evidence
blocked. Nothing was committed or pushed.
