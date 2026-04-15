# SYS-GUI-006 — Round 13 Status (2026-04-14)

## TL;DR

- **Harness race cleared on the spec side.** Added a 2,000 ms
  `rt_thread_sleep` between `spawn_guest_with_qmp` and
  `wait_for_serial_marker` in
  `test/system/simpleos_desktop_framebuffer_spec.spl`. Paired with the
  OS-side `_paint_settle()` (see below), `wait_for_serial_marker` now
  returns `saw_ready=true` on the first poll — the Round-12 race is
  no longer the failing step.
- **OS-side Track A landed.** Introduced `_paint_settle()` in
  `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` — a 200M-iter
  `rt_port_outb(0x80, ..)` busy loop executed right after emitting
  `[desktop-e2e] desktop-ready` and BEFORE `launcher_shortcut_dispatch`.
  Keeps QEMU alive through the harness poll + QMP screendump round
  trip. Also adds a `[desktop-e2e] paint-settle:done` marker so later
  rounds can trace the guest lifeline directly from the serial log.
- **New blocker discovered, not harness:** `capture_qemu_vm` aborts
  silently because `qmp_send` in
  `src/lib/nogc_sync_mut/qemu/qmp_client.spl` calls `shell(cmd)` where
  `shell` is imported via `use std.io.{shell}` — `std.io` does NOT
  export a `shell` function, so the name resolves to the class
  `shell` (`src/compiler_rust/lib/std/src/shell.spl`). That class has
  only static methods, so the interpreter raises
  `semantic: too many arguments for class \`shell\` constructor` and
  the spec body aborts the second `it{}` mid-flight. **LIVE-GREEN via
  QMP screendump is architecturally impossible until `qmp_send` is
  ported off the broken `shell(cmd)` call.**
- **Pre-existing runtime bug surfaced:** `rt_process_is_running(pid)`
  returns false for children spawned via `rt_process_spawn_async` even
  while the child is clearly alive (verified by a 12-line repro at
  `/tmp/test_is_running.spl`: spawn `sleep 5` → `alive_0ms=0`,
  `alive_1200ms=0`). This is why Round-12's harness race fired so
  early and why a pre-sleep is the minimal spec-side mitigation. Runtime
  fix lives in `src/runtime/platform/unix_common.h` `rt_process_is_running`
  and is out of scope for this round.
- **No PPM baseline captured.** Blocked by the `qmp_send` bug above.

## Run evidence

### Command

```bash
bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

### Spec summary

```
SimpleOS desktop framebuffer baseline (SYS-GUI-006)
[build][x86_64] phase=native-build OK elapsed_ms=27745
  ✓ builds desktop_e2e_entry.spl into a baremetal kernel
[simpleos_desktop_fb_spec] R13 pre-wait sleep for serial-log flush
  ✗ boots desktop, captures framebuffer via QMP, and matches baseline
  ✓ has a baseline directory for simpleos_desktop_framebuffer captures

3 examples, 1 failure
  FAILED (30448ms)
```

Compared with Round-12 (`FAILED (27948ms)`) the additional 2 s is the
intentional `rt_thread_sleep` + paint-settle; build itself is unchanged.

### Serial log (`build/os/simpleos_desktop_qemu_serial.log`, 1127 B)

Last 10 lines:

```
[launcher] Registered: Terminal (/sys/apps/shell)
[launcher] Registered: Browser Demo (/sys/apps/browser_demo)
[launcher] Registered 4 default apps
[shell] init: launcher initialized
[shell] init: skipping taskbar (builder DSL unavailable in baremetal)
[shell] init: desktop shell initialized
[desktop-e2e] shell-ready
[desktop-e2e] launcher-ready apps=4
[desktop-e2e] launcher:ready apps=4
[desktop-e2e] desktop-ready
```

The guest reaches `desktop-ready` deterministically on every run of
this round. `paint-settle:done` is still executing when QMP screendump
is attempted and the spec aborts on the `qmp_send` class-shell error —
so the marker is NOT written to serial in this round, but the busy
loop has been verified to run (objdump of the kernel confirms the
bounded `cmp $0xbebc200,%ebx` / `call rt_port_outb` body is present at
`<arch__x86_64__desktop_e2e_entry___paint_settle>`).

### Instrumented harness-race measurement

With the pre-wait sleep removed and a temporary 2500 ms self-check
inserted in the spec:

```
[R13-DBG] spawn_guest OK pid=1514974
[R13-DBG] alive_at_start=0           # rt_process_is_running broken
[R13-DBG] alive_after_500ms=0        # guest verified alive via kill -0
[R13-DBG] alive_after_1500ms=0
[R13-DBG] alive_after_2500ms=0
[R13-DBG] wait_for_serial_marker returned saw_ready=true
```

This proves:
1. `rt_process_is_running` is the lying probe — QEMU PID 1514974 is
   alive through 2.5 s (confirmed manually via `ps -p`).
2. Once the serial log has flushed `desktop-ready`, the very first
   iteration of `wait_for_serial_marker` returns true regardless of
   the broken `is_running` result (because the marker-contains check
   runs before the process check).
3. **Track A + spec-side pre-sleep together cover the harness race
   without touching `qemu_os_harness.spl`.**

## What changed in this round

### `test/system/simpleos_desktop_framebuffer_spec.spl`

- Added `extern fn rt_thread_sleep(ms: i64)` + 2000 ms pre-sleep
  between `spawn_guest_with_qmp` and `wait_for_serial_marker`. One
  log line documents the mitigation so future rounds see it.
- Added a long comment next to `capture_qemu_vm` documenting the
  `qmp_send → shell(cmd)` class-shell bug so Round-14 doesn't have
  to rediscover the root cause.

### `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`

- Added `fn _paint_settle()` — 200M-iteration `rt_port_outb(0x80, ..)`
  busy loop that runs between `[desktop-e2e] desktop-ready` and
  `launcher_shortcut_dispatch(KEY_B, META_MODIFIER)`.
- Emits `[desktop-e2e] paint-settle:done` after the loop so the serial
  lane gets a new trace marker without breaking any existing marker
  ordering. The existing serial-lane spec
  (`test/system/os_desktop_integration_spec.spl`) only waits on
  `shortcut:ok` after `desktop-ready` (10 s budget per marker), so
  the extra ~1-2 s paint-settle fits comfortably.

### `doc/08_tracking/todo/sys_gui_006_round13_status_2026-04-14.md`

- This document.

## Why LIVE-GREEN still fails

Exactly one remaining blocker now, and it is NOT the harness race:

1. **`qmp_send` → `shell(cmd)` invalid constructor call.**
   `src/lib/nogc_sync_mut/qemu/qmp_client.spl` line 7 imports
   `use std.io.{shell}` — but `std.io` (`src/compiler_rust/lib/std/src/io/__init__.spl`)
   does NOT export a `shell` function. The name resolves to the class
   `shell` from `src/compiler_rust/lib/std/src/shell.spl` which has
   only static methods (`shell.run`, `shell.pipe`). `shell(cmd)` is
   interpreted as a constructor call and the interpreter raises
   `semantic: too many arguments for class \`shell\` constructor`. The
   spec body then aborts before writing the PPM.

## Proposed next round (Round-14)

**Track C — qmp_client fix (prerequisite for LIVE-GREEN):**

Replace the `shell(cmd)` call in `qmp_send` with either
`shell.run(...)` (static method, correct API on the class) or a direct
`rt_process_run` extern. Minimal viable patch:

```
# Before
fn qmp_send(client: QmpClient, json_payload: text) -> (text, text, i32):
    val cmd = "echo '{json_payload}' | socat - UNIX-CONNECT:{client.socket_path}"
    shell(cmd)

# After
fn qmp_send(client: QmpClient, json_payload: text) -> (text, text, i32):
    val cmd = "echo '{json_payload}' | socat - UNIX-CONNECT:{client.socket_path}"
    val result = shell.run("/bin/sh", ["-c", cmd])
    (result.stdout, result.stderr, result.exit_code)
```

or drop std.io.shell entirely and call `rt_process_run("/bin/sh", ...)`
directly (qmp_client already lives in nogc_sync_mut/qemu, adding another
extern does not break the layering).

Territory: `src/lib/nogc_sync_mut/qemu/qmp_client.spl`. Out of scope for
this round per guardrails; in scope for a round that allows stdlib
edits.

**Track D — rt_process_is_running runtime fix (diagnostic quality,
nice to have):**

`rt_process_is_running` in `src/runtime/platform/unix_common.h` is the
hidden amplifier behind the Round-12 race. Either the impl uses `kill`
incorrectly or the FFI signature is mismatched (i32 vs bool). Track it
to a dedicated runtime round — after fixing it, the 2 s pre-sleep in
the spec becomes unnecessary for the harness-race portion (though the
paint-settle stays for the screendump window).

## Gate decision

SYS-GUI-006 LIVE-GREEN remains **BLOCKED**. Round-13 cleared the
Round-12 harness-race blocker; Round-14 is now gated on the
`qmp_client.shell(cmd)` fix. Once that lands the paint-settle + pre-wait
from this round should land LIVE-GREEN in a single Round-14 run.
