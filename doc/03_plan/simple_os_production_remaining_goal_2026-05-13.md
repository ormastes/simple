# Simple OS Production Remaining Goal

Date: 2026-05-13

## Goal

Bring Simple OS closer to production readiness across IPC, appscan coverage,
performance, stability, and primitive API hygiene.

## Verified This Session

- L4 IPC fast-path primitives exist in `src/os/kernel/ipc/l4_fast_ipc.spl`.
- L4 IPC unit coverage exists in `test/unit/os/kernel/ipc/l4_fast_ipc_spec.spl`.
- L4 IPC has a discovered regression gate in
  `test/perf/ipc_l4_logic_perf_spec.spl`; latest evidence showed queued IPC at
  about 11.5s for 20k iterations and L4 inline paths at about 1.1s.
- Multiarch appscan specs exist under `test/qemu/os/appscan/` for ARM,
  RISC-V, and x86.
- ARM and RISC-V appscan lanes passed from fresh rebuilt artifacts.
- x86 appscan passed in about 3.5s after the QEMU serial marker early-exit fix.
- `llvm-nm -u` showed no undefined symbols for rebuilt ARM32, ARM64, RV32, and
  RV64 appscan ELFs.
- QEMU stale-process check showed no leftover QEMU processes after appscan runs.
- Primitive wrapper types exist in `src/lib/common/types.spl`:
  `ExitCode`, `Handle`, `ErrorCode`, `MemAddr`, and `DurationMs`.
- Primitive API wrapper canaries passed for Trace32 duration, shell exit code,
  and SFFI handle usage.

## Remaining Work

- Fix primitive API lint regressions:
  - `test/system/code_quality/primitive_api_lint_spec.spl` currently fails because the
    text-scanner pure-math exemption is too broad.
  - `test/integration/app/primitive_api_lint_spec.spl` currently fails because
    `pub fn bad(x: i64) -> i64` is incorrectly exempted.
  - `src/compiler/90.tools/lint/main_part1.spl` still sets
    `levels["primitive_api"] = "warn"` while the spec expects `deny`.
- Re-run primitive API lint gates after the scanner fix:
  - `test/system/code_quality/primitive_api_lint_spec.spl`
  - `test/system/code_quality/primitive_api_canary_spec.spl`
  - `test/integration/app/primitive_api_lint_spec.spl`
- Run a final targeted production-readiness sweep after lint recovery:
  - IPC unit and perf gates.
  - QEMU appscan specs for ARM, RISC-V, and x86.
  - No-leftover-QEMU process check.
  - Undefined-symbol checks for rebuilt appscan ELFs.

## Stop Condition

Do not mark the broad production-readiness goal complete until the primitive API
lint regressions are fixed and the final targeted sweep passes with fresh
evidence.
