# Plan: Runtime Signal Safety + Test Hardening

**Created:** 2026-05-30
**Priority:** P0 (blocks safe CI and dev)
**Bug:** `doc/08_tracking/bug/serial_usb_sigsegv_cascade_2026-05-30.md`

## Phase 1: Immediate Safety (done)

- [x] BLOCKED 5 dangerous serial_mcp_spec tests that touch real /dev/ttyUSB* devices
- [x] Filed bug doc with root cause analysis

## Phase 2: Runtime SIGSEGV Handler

- [x] Add `sigaction(SIGSEGV, ...)` in `runtime.c` `_spl_runtime_init()`
- [x] Handler prints: faulting address, backtrace (via `backtrace()`), then `_exit(139)`
- [x] Add `sigaction(SIGBUS, ...)` for similar null-deref on bus errors
- [ ] Test: deliberate null deref in compiled mode produces backtrace, not bare crash

## Phase 3: Fork Child Signal Isolation

- [ ] Audit all `fork()` callsites in runtime.c
- [x] Parent wait path detects `WIFSIGNALED(status)` and returns `128 + WTERMSIG` as an exit code instead of re-raising — verified src/runtime/runtime_fork.c:518 `WIFSIGNALED`, :520 `128 + WTERMSIG(status)`
  - divergence: planned "log, not propagate" in `runtime.c`; shipped in `runtime_fork.c` as a status code with no log line, while the legacy guardian in src/runtime/runtime_legacy_core.c:839 deliberately re-raises the child signal in itself.
- [x] Test: a child dying by SIGSEGV (139) is classified CRASHED by the surviving runner parent — verified test/01_unit/test_runner/signal_classification_subprocess_spec.spl:30 `classifies SIGSEGV (139) as CRASHED with failed: 1`
  - divergence: planned a runtime-level fork test; shipped at the test-runner subprocess-classification level (runner parent survives and reports), not a `runtime.c` fork unit test.

## Phase 4: Serial FFI Null-Guard

- [x] `serial_open` — validate fd after `open()`, return `is_valid=false` on failure — verified src/app/io/serial_ffi.spl:66 `is_valid: fd >= 0`
- [x] `serial_read`/`serial_write` — check `port.is_valid` before use — verified src/app/io/serial_ffi.spl:99 `if not port.is_valid` (`serial_read`), :108 `if not port.is_valid` (`serial_write`)
- [x] `serial_close` — idempotent, no double-free — verified `test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl` "serial_close rejects a repeat close instead of double-freeing the fd" PASSES (was RED; spec file went 0/7 -> 1/7 passing) under `src/compiler_rust/target/debug/simple run` (debug Rust seed, 120103640 bytes, mtime 2026-09-04 18:13). Guard landed in BOTH implementations: `src/lib/nogc_sync_mut/io/serial_sffi.spl` (the live one, used by `src/app/serial_mcp/tools.spl`) and `src/app/io/serial_ffi.spl` (the one the oracle greps). `SerialPort` is passed BY VALUE, so a `closed: bool` field alone cannot stop a second close through a stale copy — each module also keeps a process-global closed-descriptor set (`_closed_handles` / `_closed_fds`) that is the authoritative guard, and `serial_open` drops a stale entry when the OS recycles the number.
- [ ] Re-enable BLOCKED serial_mcp_spec tests after guard lands

## Phase 5: Simple-Level Signal Wiring

- [ ] Wire SIGSEGV into the Simple signal layer (`src/lib/nogc_sync_mut/io/signal_handlers.spl`, 255 lines; `install_signal_handlers` at :69 handles SIGINT/SIGTERM/SIGHUP/SIGUSR2 only — no `std.os.signal` module exists)
- [ ] Distinguish segfault from memory-limit violation via `si_code` inspection
- [ ] Add `on_segfault(fn)` callback registration for user code

## Phase 6: Test Environment Hardening

- [x] Hardware-dependent specs gate themselves with `test_env_require("SIMPLE_HW_TEST")` from `std.common.test_env_gate` — verified src/lib/common/test_env_gate.spl:23 `test_env_require`, test/01_unit/app/serial_mcp/serial_mcp_spec.spl:47 `test_env_require("SIMPLE_HW_TEST")`
  - divergence: planned a runner-parsed `@env: hardware` annotation; shipped an in-body library call (no `@env:` annotation is parsed anywhere under src/app/test_runner_new/).
- [x] Env gate: `test_env_hardware_available()` is true only when `SIMPLE_HW_TEST=1`; the runner client recognises the gate vars to divert off the stale-env daemon — verified src/lib/common/test_env_gate.spl:30 `test_env_hardware_available`, src/app/test_runner_new/test_runner_client.spl:591 `SIMPLE_HW_TEST`, :690 `_test_env_gate_names`
  - divergence: planned runner-side skip of annotated specs; shipped spec-side gating (spec bodies decide), runner only detects the vars for daemon bypass.
- [x] QEMU gate `test_env_qemu_available()` on `SIMPLE_QEMU_TEST=1` — verified src/lib/common/test_env_gate.spl:34 `test_env_qemu_available`
  - divergence: library predicate, not an `@env: qemu` annotation.
- [x] Network gate `test_env_network_available()` on `SIMPLE_NET_TEST=1` — verified src/lib/common/test_env_gate.spl:38 `test_env_network_available`
  - divergence: library predicate, not an `@env: network` annotation.
- [x] SPipe environment support: `test_env_require("SIMPLE_HW_TEST")` returns `"blocked:SIMPLE_HW_TEST"`/`"ready"` for `expect(...).to_equal` — verified src/lib/common/test_env_gate.spl:23 `test_env_require`, :11 usage doc
  - divergence: planned a dedicated matcher `env_require`; shipped a text-returning helper compared with the stock `to_equal` matcher.

## Acceptance Criteria

- No compiled Simple program can kill its parent via unhandled SIGSEGV
- `bin/simple test` never touches real hardware unless explicitly opted in
- Serial MCP tests pass with mock device or env-gated real device

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
