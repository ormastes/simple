# SYS-GUI-006 Round-20 Status — NOT-LIVE-GREEN (qemu_capture fd=0 bug)

**Date:** 2026-04-14 (workspace date) / 2026-04-15 (actual run)
**Workspace:** `/tmp/simple-round29`
**Outcome:** NOT-LIVE-GREEN — kernel fully boots (TEST PASSED in serial), heap bump confirmed working, new compiler built with all externs. Single remaining blocker: `qemu_capture.spl` creates `QmpClient` with default `fd=0` instead of calling `qmp_connect`.

---

## What Was Done

### Step 1 — Heap Bump Applied (256 MiB)
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` bumped from 128 MB to 256 MB
- Comment updated to reflect new memory budget (~286 MB, well within -m 512M)
- This was the blocker from Round-19 — **CONFIRMED FIXED**

### Step 2 — bin/simple Symlink Created
- Round-29 workspace lacked `bin/simple` symlink
- Created: `bin/simple → /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple`
- Bootstrap binary (v0.9.5) missing `rt_fd_write` and other QMP externs (predates Round-19 fixes)

### Step 3 — Compiler Rebuilt from Source
Vendor blockers resolved:
- `log-0.4.29`: copied from `~/.cargo/registry/src/`, `.cargo-checksum.json` generated with package hash
- `thiserror/build/probe.rs`: created `vendor/thiserror/build/` dir, copied from registry
- 2929 other missing vendor files: bulk-copied via Python script (same as Round-19)

Build result: **Finished `release` profile in 2m 16s**

New binary: `/tmp/simple-round29/src/compiler_rust/target/release/simple`
Symlinked to `bin/simple`.

### Step 4 — Test Runs

**Run 1** (bootstrap binary, cache cleared):
- Result: `3 examples, 1 failure` (28675ms)
- Failure: `semantic: unknown extern function: rt_fd_write`
- Build test: ✓ PASS (256 MiB heap, kernel built successfully)

**Run 2** (new binary, cache cleared):
- Result: `3 examples, 1 failure` (30663ms)
- Failure: `[qmp] screendump failed: write failed`
- Build test: ✓ PASS
- Baseline dir test: ✓ PASS

**Run 3** (new binary, cache cleared, full output captured):
- Same result as Run 2: `write failed`
- Grep of output: `[qmp] screendump failed: write failed`
- Error: `semantic: method 'len' not found on type 'enum' (receiver value: Option::Some([]))`

---

## Serial Log Analysis — Major Progress

The serial log from the lingering QEMU process (not killed by harness) shows **full successful boot**:

```
[desktop-e2e] spl_start
[desktop-e2e] boot
[vfs-init] No NVMe device found -- VFS unavailable
[GUI] fb_addr=0x0x00000000fd000000 fb_w=0x0000000000000400
[desktop-e2e] shell-ready
[desktop-e2e] launcher-ready apps=4
[desktop-e2e] desktop-ready
[desktop-e2e] paint-settle:done
[nvme-c] No NVMe device found on PCI bus
[launcher] manifest read failed path=/sys/apps/browser_demo file=BROWSER.APP
[launcher] shortcut fallback key=66 mod=1
[browser_demo] render stats nodes=255 pixels=3 mode=resident-manifest
[desktop-e2e] shortcut:ok key=meta+b app=browser_demo mode=resident-manifest
[desktop-e2e] wm:ok pid=4242 app= mode=resident-manifest
[desktop-e2e] hello:shortcut:ok key=meta+h app=hello_world
[desktop-e2e] remote-grouping:ok pid=4242 windows=2 mode=resident-manifest
TEST PASSED
```

**Key findings:**
- `paint-settle:done` emitted — no heap panic (256 MiB bump working)
- No `[PANIC] heap exhausted` anywhere in serial log
- `remote-grouping:ok` emitted — launcher shortcut dispatch fully works
- `TEST PASSED` in serial — the kernel-side test completes successfully
- FAULT entries appear but are non-fatal (NVMe missing path, handled gracefully)

---

## Root Cause of Remaining Failure

### `qemu_capture.spl` — fd=0 bug

`src/os/compositor/qemu_capture.spl` (line 59):
```
val client = QmpClient(socket_path: qmp_socket)
```

This creates `QmpClient` with `fd: i64` unset (default = 0). Then calls `qmp_screendump(client, ...)` which calls `qmp_send` → checks `client.fd < 0` (0 is not < 0!) → calls `qmp_write_line(0, ...)` → `rt_fd_write(0, ...)` writes to stdin (fd 0) → fails → returns "write failed".

**Fix needed:** Change to call `qmp_connect(qmp_socket)` instead:
```
val client = qmp_connect(qmp_socket)
```

This is a one-line fix in `src/os/compositor/qemu_capture.spl`. Round-20 guardrails prohibit editing production .spl, so this is deferred to Round-21.

### Secondary: `Option.len()` interpreter bug (pre-existing)
When `capture_qemu_vm` returns a zero-size result, calling `.len()` on `result.pixels` fails.
This is documented in spec comments (line 323). Will be resolved once a real frame is captured.

---

## Status Matrix

| Blocker | Round-19 | Round-20 |
|---------|----------|----------|
| Heap exhaustion (128 MB) | ACTIVE | **FIXED** (256 MB) |
| `rt_fd_write` unknown extern | FIXED | CONFIRMED WORKING |
| `rt_process_is_running` unknown extern | FIXED | CONFIRMED WORKING |
| `rt_process_kill` unknown extern | FIXED | CONFIRMED WORKING |
| Kernel boot to `paint-settle:done` | BLOCKED (heap) | **CONFIRMED** |
| Kernel `TEST PASSED` in serial | BLOCKED (heap) | **CONFIRMED** |
| `qemu_capture.spl` fd=0 bug | PRESENT | ACTIVE (sole blocker) |
| `Option.len()` interpreter bug | PRESENT | PRESENT (secondary) |

---

## Files Modified in Round-20

- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` — heap 128→256 MB
- `bin/simple` — symlinked to new release binary
- `src/compiler_rust/vendor/log/` — populated from registry
- `src/compiler_rust/vendor/thiserror/build/probe.rs` — populated from registry
- 2929 other vendor files — populated from registry

---

## Next Round Recommendation (Round-21)

**One-line fix** in `src/os/compositor/qemu_capture.spl`:
- Line 59: change `QmpClient(socket_path: qmp_socket)` to `qmp_connect(qmp_socket)`
- Also need `use std.nogc_sync_mut.qemu.qmp_client.{qmp_connect}` if not already imported

After this fix, the QMP screendump should connect, send capabilities, and capture the framebuffer. The kernel is confirmed running and responsive at that point.

Expected outcome: LIVE-GREEN (3 examples, 3 passed) with a real PPM baseline captured.
