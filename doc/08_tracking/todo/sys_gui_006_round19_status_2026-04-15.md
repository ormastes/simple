# SYS-GUI-006 Round-19 Status — NOT-LIVE-GREEN (heap exhausted before QMP)

**Date:** 2026-04-15  
**Workspace:** `/tmp/simple-round27`  
**Outcome:** NOT-LIVE-GREEN — QMP screendump blocked by baremetal heap exhaustion

---

## What Was Done

### Step 1 — Compiler Rebuilt from Source
- `cargo build --release -p simple-driver` run from `/tmp/simple-round27/src/compiler_rust/`
- Vendor fixes required:
  - `log-0.4.29` missing from vendor (copied from `~/.cargo/registry/src/`)
  - 2929 files missing from vendor checksums across multiple crates (copied from registry cache via Python script)
  - `thiserror/build/probe.rs` missing (copied from registry)
- Build succeeded: 2m 19s (first build), then 1m 07s incremental
- New binary at `src/compiler_rust/target/release/simple` (48MB, Apr 15 00:00)
- `bin/simple` symlinked to new binary via `scripts/setup.sh`

### Step 2 — Missing Interpreter Externs Added
Three externs were registered in `pyy/4df8` (`rt_fd_write`, `rt_fd_read_until`, `rt_unix_socket_connect`, `rt_fd_close`) but two more were missing:

1. **`rt_process_is_running`** — added to `interpreter_extern/system.rs` + `mod.rs`
2. **`rt_process_kill`** — added to `interpreter_extern/system.rs` + `mod.rs`

Both use `SPAWNED_PROCESSES` (the interpreter's own child-process map).

### Step 3 — Two QEMU Runs (limit reached)
- **Run 1** (after `rt_process_is_running` fix): Failed — `unknown extern: rt_process_kill`
- **Run 2** (after `rt_process_kill` fix): Failed — QMP screendump write failed, then `Option.len()` interpreter bug

---

## Blocker Analysis

### Primary Blocker — Heap Exhaustion
Serial log from Run 2 shows the desktop booted and painted successfully:
```
[desktop-e2e] desktop-ready
[desktop-e2e] paint-settle:done
[PANIC] heap exhausted
```
QEMU crashes ~30s into the boot after the launcher tries to read app manifests from NVMe (not present). The QMP socket never becomes writable because QEMU terminates before the screendump command arrives.

### Secondary Blocker — `Option.len()` Interpreter Bug (pre-existing)
When `capture_qemu_vm` returns a zero-size result (0x0 frame, empty pixels array), calling `.len()` on `result.pixels` fails with:
```
semantic: method `len` not found on type `enum` (receiver value: Option::Some([]))
```
The interpreter returns `Option::Some([])` for an empty array instead of `[]`. This is a known pre-existing bug (documented in spec comment at line 323).

### Extern Chain — RESOLVED
All externs needed by the harness are now registered:
| Extern | Status |
|--------|--------|
| `rt_fd_write` | Fixed (pyy/4df8) |
| `rt_fd_read_until` | Fixed (pyy/4df8) |
| `rt_unix_socket_connect` | Fixed (pyy/4df8) |
| `rt_fd_close` | Fixed (pyy/4df8) |
| `rt_process_is_running` | Fixed (Round-19) |
| `rt_process_kill` | Fixed (Round-19) |

---

## Remaining Blockers for LIVE-GREEN

1. **Heap exhaustion** — baremetal kernel panics after `paint-settle:done`. Needs heap size increase or launcher manifest read path skip when no NVMe. This is the last gating blocker.
2. **`Option.len()` interpreter bug** — `[].len()` returns error when array is wrapped in `Option::Some`. Pre-existing, documented.

---

## Files Modified
- `src/compiler_rust/compiler/src/interpreter_extern/system.rs` — added `rt_process_is_running`, `rt_process_kill`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — registered both
- `src/compiler_rust/vendor/log/` — populated from registry cache
- `src/compiler_rust/vendor/thiserror/build/probe.rs` — populated from registry cache
- 2929 other vendor files populated from registry cache

---

## Next Round Recommendation (Round-20)
Fix the heap exhaustion. Two options:
1. Increase the baremetal heap size in `examples/simple_os/arch/x86_64/linker.ld` or the heap init code
2. Guard the launcher manifest read behind a VFS-available check (already has `No NVMe device found` path but still panics downstream)

Once heap exhaustion is fixed, the QMP screendump should succeed and LIVE-GREEN is achievable.
