# Plan: Runtime Signal Safety + Test Hardening

**Created:** 2026-05-30
**Priority:** P0 (blocks safe CI and dev)
**Bug:** `doc/08_tracking/bug/serial_usb_sigsegv_cascade_2026-05-30.md`

## Phase 1: Immediate Safety (done)

- [x] BLOCKED 5 dangerous serial_mcp_spec tests that touch real /dev/ttyUSB* devices
- [x] Filed bug doc with root cause analysis

## Phase 2: Runtime SIGSEGV Handler

- [ ] Add `sigaction(SIGSEGV, ...)` in `runtime.c` `_spl_runtime_init()`
- [ ] Handler prints: faulting address, backtrace (via `backtrace()`), then `_exit(139)`
- [ ] Add `sigaction(SIGBUS, ...)` for similar null-deref on bus errors
- [ ] Test: deliberate null deref in compiled mode produces backtrace, not bare crash

## Phase 3: Fork Child Signal Isolation

- [ ] Audit all `fork()` callsites in runtime.c
- [ ] Parent `waitpid()` must detect `WIFSIGNALED(status)` and log, not propagate
- [ ] Test: child SIGSEGV does not kill parent

## Phase 4: Serial FFI Null-Guard

- [ ] `serial_open` — validate fd after `open()`, return `is_valid=false` on failure
- [ ] `serial_read`/`serial_write` — check handle != 0 before use
- [ ] `serial_close` — idempotent, no double-free
- [ ] Re-enable BLOCKED serial_mcp_spec tests after guard lands

## Phase 5: Simple-Level Signal Wiring

- [ ] Wire SIGSEGV into `std.os.signal` (signal_handlers.spl, line ~1784)
- [ ] Distinguish segfault from memory-limit violation via `si_code` inspection
- [ ] Add `on_segfault(fn)` callback registration for user code

## Phase 6: Test Environment Hardening

- [ ] Tag hardware-dependent specs with `@env: hardware` annotation
- [ ] Add env-gate in test runner: skip `@env: hardware` unless `SIMPLE_HW_TEST=1`
- [ ] Add `@env: qemu` gate for QEMU-dependent tests
- [ ] Add `@env: network` gate for network-dependent tests
- [ ] SPipe environment test support: `env_require("SIMPLE_HW_TEST")` matcher

## Acceptance Criteria

- No compiled Simple program can kill its parent via unhandled SIGSEGV
- `bin/simple test` never touches real hardware unless explicitly opted in
- Serial MCP tests pass with mock device or env-gated real device
