# INT-2 — VFS handle→mount wiring (P3 increment 2)

**Status:** wiring increment COMPLETE, spec green. Not committed.
**Date:** 2026-07-27

## What landed

`VfsHandleTable` (`src/os/kernel/fs/vfs_handle_table.spl`, untouched — read-only
substrate) is now the routing table of `VfsManager`. It was registered but
unwired before this lane.

### Ops now routed through the handle table

| Op | Before | After |
|----|--------|-------|
| `VfsManager.open` | returned the driver-local handle in `fd.node` | resolves mount **index**, calls `handles.register(idx, mount_path, driver_handle)`, returns the **VFS handle** in `fd.node` |
| `VfsManager.read` | `self.mounts[0].fs.read(handle, …)` | `_route(h)` → owning mount → `fs.read(driver_handle_of(h), …)` |
| `VfsManager.write` | `self.mounts[0]` (+ read-only check) | `_route(h)` → owning mount, read-only check on **that** mount |
| `VfsManager.seek` | `self.mounts[0]` | `_route(h)` → owning mount |
| `VfsManager.close` | `self.mounts[0]` | `_route(h)` → owning mount, then `handles.release(h)` (released even on driver error, so a closed handle is never re-routable) |
| `VfsManager.unmount` | dropped the mount, orphaned its handles | `handles.release_mount(i)` + `handles.reindex_after_unmount(i)` before `mounts.remove(i)` |
| `VfsService.dispatch_open` | replied `fd.fd` (descriptor number — never identified a mount, never matched what READ consumed) | replies `fd.node`, the VFS handle the other three ops resolve |
| `VfsService.dispatch_read/write/close/seek` | `self.vfs.mounts[0].fs.<op>(fd, …)` | delegate to `VfsManager.<op>` |

New helpers on `VfsManager`: `resolve_mount_index`, `_route`,
`open_handle_count`, `handle_mount_path`, `handle_mount_index`,
`handle_driver_handle`.

### mounts[0] bypass sites removed — 8 total

Line numbers are the **pre-change** file (cited in the prior lane's note):

- `src/os/services/vfs/vfs.spl` L244 (`write`), L302 (`close`), L309 (`read`),
  L316 (`seek`) — 4 sites, plus the "For simplicity, we route to the first
  mount. A full implementation would maintain a handle-to-mount mapping"
  comment block deleted.
- `src/os/services/vfs/vfs_service.spl` L212 (`dispatch_read`, incl. the
  `# Simplified: use first mount` comment), L228 (`dispatch_write`), L238
  (`dispatch_close`), L406 (`dispatch_seek`) — 4 sites.

`grep -rn "mounts\[0\]" src/os/` now returns only prose (docstrings/comments
that name the removed bypass). Converged-owner comments point at
`os.kernel.fs.vfs_handle_table` from both files.

## fs_driver "first-Ok-wins" convergence decision

The prior brief described stack 2 as a "probe each mount, first Ok wins" loop.
**That is not what the code does.** `src/lib/nogc_sync_mut/fs_driver/mount_table.spl`
(and its `nogc_async_mut` twin) already does a correct longest-prefix
`resolve()` → `MountId` and binds `OpenFileBinding(virtual_handle, mount_id,
inner_handle)` at L425-443; the `while` loop there is only a linear scan for the
already-resolved `mount_id`, not a probe.

**Decision: no convergence work, and deliberately no second implementation.**
Rationale:
- It is a *different subsystem* with a different key: `fs_driver` is the
  `std.nogc_sync_mut` host/lib FS stack keyed by `MountId` (stable across
  unmount); the OS `VfsManager` is keyed by mount **index** (renumbered by
  `mounts.remove`, hence `reindex_after_unmount`).
- It is **outside this lane's exclusive paths** (`src/lib/**`).
- It is already correct-by-construction, so replacing it with `VfsHandleTable`
  would be churn, not a fix.

Duplicate-owner guard is satisfied: within `src/os/**` there is now exactly one
handle→mount association, `VfsHandleTable`. A future unification of
`fs_driver::MountTable` and `VfsHandleTable` is a separate, larger lane —
suggest keying `VfsHandleTable` by a stable mount id first, which would then
also let `reindex_after_unmount` be deleted.

## Spec verdict

`test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl` (new)

```
7 examples, 0 failures
```

Run with `/tmp/int2/bin/int2job run <spec>` (copy of
`bin/release/x86_64-unknown-linux-gnu/simple`); identical result from
`build/native_probe/simple`.

The VFS service **was** instantiable host-side against the real `VfsManager` —
no fallback to a logic-only assertion was needed. Two `StampFs` stub drivers
mount at `/alpha` (index 0) and `/beta` (index 1); each stamps its own name into
every result, so the oracle is absolute:

- read → `"beta-payload"` (never a value compared to itself), negative: alpha's
  handle yields `"alpha-payload"`.
- write → beta returns `2000 + len`, alpha `1000 + len`.
- seek → beta returns `200 + offset`, alpha `100 + offset`.
- close → identity probe error text `"close-routed-to-beta"`.
- Both drivers issue driver handle **1**; the spec asserts the two VFS handles
  differ and resolve to different mount paths while the driver handles are equal.
- Stale-handle negatives: double close and post-`unmount` read both fail with
  `"unknown VFS handle"` instead of falling through to alpha.

**Falsifiability proven:** restoring `val mount = self.mounts[0]` in
`VfsManager.read` alone flipped the suite to `7 examples, 2 failures`
(`expected alpha-payload to contain beta`, `expected alpha-payload to equal
beta-payload`); restored → `7 examples, 0 failures`. The pre-existing
`handle_mount_association_spec.spl` is still `7 examples, 0 failures`.

## Defects found while wiring (record, do not lose)

1. **Cross-module `Result.Ok` / `Result.Err` unresolved in the interpreter.**
   `VfsManager.new()` worked, but the first call into any `VfsManager` method
   died with ``semantic: variable `Result` not found``. A module-level
   `Result.Ok(true)` in a standalone file works fine — it fails only for a
   method body reached through an import. Both the release binary and
   `build/native_probe/simple` agree, so it is not seed staleness.
   *Workaround applied:* all 59 `Result.Ok(`/`Result.Err(` in
   `src/os/services/vfs/vfs.spl` converted to the bare `Ok(`/`Err(` form
   (already used elsewhere in the same file; no `match Result.Ok(x)` patterns
   existed, so this is expression-position only and behaviour-preserving).
   `vfs_service.spl` keeps `Result.Ok`/`Result.Err` in **match patterns**, which
   are unaffected. This should be filed as a compiler bug — the workaround is
   not the fix.

2. **Mutating call nested in another call's argument list loses the write.**
   `vfs.read(vfs.open(p, f).unwrap().node, n)` failed with `unknown VFS handle:
   2` — the inner `open`'s mutation of `vfs.handles` was discarded because the
   outer call had already captured the receiver. Same family as the documented
   two-hop defect (`doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md`)
   but triggered by *argument nesting*, not field depth. Fix in the spec: bind
   the open to a `val` first. Extract-mutate-writeback (`var table =
   self.handles; …; self.handles = table`) is used in `vfs.spl` open/close/
   unmount and `var mgr = self.vfs; …; self.vfs = mgr` in `vfs_service.spl` as
   pre-emptive insurance.

3. **`simple lint` is broken for any file declaring a class** — errors with
   ``semantic: method `get` not found on type `str` (receiver value: <LastClass>)``.
   Reproduced on the **untouched** `src/os/kernel/fs/vfs_handle_table.spl`, so
   it is pre-existing and unrelated to this lane. Lint could not be used as a
   gate here.

## Remaining bypass callers — resume plan

1. **`src/os/services/llm/_McpOsServer/dispatch_and_io_tools.spl` L188-244**
   (`tool_file_read`, `tool_file_write`) — **outside this lane's exclusive
   paths.** It calls `self.vfs.open(path, flags)`, then separately
   `self.vfs.resolve_mount(path)`, and passes `fd.node` straight to
   `entry.fs.read/write/close`. That was already wrong for any non-first mount;
   after this change `fd.node` is a VFS handle, so it is now wrong for *every*
   mount. **Fix is three one-line swaps** to `self.vfs.read(fd.node, 65536)`,
   `self.vfs.write(fd.node, data)`, `self.vfs.close(fd.node)`, which also
   deletes the redundant `resolve_mount`. Assign to whichever lane owns
   `src/os/services/llm/**`, or fold into INT-3.

2. **`VfsManager.read_text` / `write_text` / `preload_file_pages`** (vfs.spl)
   still call `entry.fs.open/read/write/close` directly, bypassing the table.
   *Left intentionally:* these are path-scoped, open→use→close inside a single
   resolved mount, and the handle never escapes the method, so there is no
   association to lose. Registering them would only add table churn. Revisit if
   fd leak accounting or per-fd quotas are ever added.

3. **`VfsService` wire protocol** now returns `fd.node` from OPEN. Any in-guest
   client that assumed the old `fd.fd` reply must be re-checked — but the old
   reply was never usable, since READ fed it to a driver as if it were a driver
   handle. No in-tree client was found that depends on it; worth a grep in the
   guest userland at integration time.

4. **`fs_driver::MountTable` ↔ `VfsHandleTable` unification** — see the
   convergence decision above. Not started, not required for P3.

## Files changed (uncommitted)

- `src/os/services/vfs/vfs.spl` — handle table field + wiring, `resolve_mount_index`,
  `_route`, introspection helpers, unmount hygiene, `Result.` → bare `Ok`/`Err`.
- `src/os/services/vfs/vfs_service.spl` — 4 dispatch handlers delegate to
  `VfsManager`; OPEN replies the VFS handle.
- `test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl` — new, 7 examples.
- `.spipe/simpleos_harden_int2_vfs_wire/state.md` — this file.
