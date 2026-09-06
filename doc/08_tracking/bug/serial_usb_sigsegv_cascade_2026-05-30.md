# Bug: serial_open SIGSEGV cascade on USB disconnect kills tmux session

Status: Open (runtime crash handler and serial fd guards landed)

**Date:** 2026-05-30
**Severity:** Critical
**Status:** Open (runtime crash handler and serial fd guards landed)
**Component:** runtime (runtime.c), serial FFI, signal handling

## Summary

When an ESP32 USB JTAG device (`ttyACM1`, Espressif `88:56:A6:7C:2C:88`)
disconnects during active serial access, compiled Simple programs
(`simple-main`) segfault at address `0x8` (null struct field deref).
Multiple forked children crash in rapid succession, destabilizing the
systemd user session which then activates `exit.target` — tearing down
all tmux panes and killing every running Claude session.

## Timeline (2026-05-30 08:50–09:09)

1. 08:50:30 — `simple-main[1256726]`: segfault at 8, ip `...0382b4`, CPU 6
2. 08:50:31 — USB 3-1.4.2 disconnect (ESP32 JTAG), then reconnect
3. 08:50:31 — `simple-main[1258001]`: segfault at 8, same instruction, CPU 23
4. 08:50:33 — `simple-main[1259340]`: segfault at 8, same instruction, CPU 22
5. 09:09:35 — systemd `exit.target` activated, all 6 tmux scopes killed

## Root Cause

`serial_open()` / serial FFI returns a handle that becomes dangling when
the underlying USB device disconnects. The compiled code dereferences a
null struct pointer at offset 8 (likely `handle` or `fd` field) without
null-checking. The runtime has no SIGSEGV handler, so each crash is an
uncontrolled process termination.

## Reproduction

1. Open a `serial_open("/dev/ttyACM1", 115200)` in compiled mode
2. Physically unplug the ESP32 USB cable
3. Observe SIGSEGV in dmesg

## Fix Plan

### Layer 1: Runtime SIGSEGV handler (runtime.c)
- Install `sigaction(SIGSEGV, ...)` handler that prints faulting address,
  backtrace via `backtrace()`, and calls `_exit(139)` instead of bare crash
- Prevents uncontrolled signal propagation

### Layer 2: Fork child signal isolation
- Child SIGSEGV must never propagate to parent process
- Parent should `waitpid()` and handle child crash gracefully

### Layer 3: Serial FFI null-guard
- `serial_open` / `serial_read` / `serial_write` must check device handle
  validity before dereference
- Return error result instead of crashing on invalid handle
- 2026-06-22: `src/compiler_rust/runtime/src/value/serial.rs` now rejects
  invalid serial fd values (`<= 0` or outside `i32`) before close/read/write,
  timeout, flush, or relay call into libc/termios/poll. Guarded by
  `value::serial::tests::test_serial_rejects_invalid_fds_before_libc_calls`.
  Physical USB disconnect validation remains open.

### Layer 4: Simple-level signal wiring (signal_handlers.spl)
- Wire SIGSEGV into `std.os.signal` so Simple code can register handlers
- Distinguish segfault from memory-limit violation

## Affected Tests

- `test/01_unit/app/serial_mcp/serial_mcp_spec.spl` — BLOCKED (5 tests disabled)
  Tests that call `serial_open`/`ssh_serial_connect` with real device paths

## Related

- `crc32_native_global_table_cache_segfault_2026-05-13.md` — different SIGSEGV root cause
- Session `8f84edc2` was mid-implementation of the 4-layer fix when killed
