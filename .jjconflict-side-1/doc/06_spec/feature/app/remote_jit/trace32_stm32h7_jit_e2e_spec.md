# TRACE32 STM32H7 Remote JIT End-to-End

*Source: `test/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl`*
*Last Updated: 2026-03-29*

**Feature IDs:** #TRACE32-JIT-STM32H7
**Category:** Integration
**Difficulty:** 4/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

---

## Overview

Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

- `run_test_file_composite`
- `Trace32Adapter`
- `T32GdbBridgeClient`
- `RemoteExecutionManager`

Requires a live TRACE32 PowerView session with the repo GDB bridge on `2331`.

## Environment

- TRACE32 PowerView reachable on Remote API port `20000`
- TRACE32 GDB bridge reachable on TCP port `2331`
- LLVM host tools available: `clang`, `ld.lld`, `llvm-objcopy`
- Fixture file present: `test/fixtures/remote_jit/stm32h7_return_zero.spl`

## Behavior

- Verifies fixture discovery before attempting live hardware access
- Separately checks Remote API reachability and GDB bridge readiness
- Executes the real composite JIT lane only when all prerequisites are present
- Emits `[skip]` messages instead of failing when the external lab environment is unavailable

## Execution Notes

- This is an environment-backed integration test, not a hermetic unit test
- Successful execution proves the repo default TRACE32 STM32H7 lane is callable end-to-end
- A skipped run documents missing infrastructure rather than a product regression

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 4 |
| Slow Scenarios | 4 |
| Skipped Scenarios | 0 |

## Scenarios

- [slow] discovers the repo return-zero fixture
- [slow] checks for a live TRACE32 Remote API session
- [slow] checks for a live TRACE32 GDB bridge on the repo default port
- [slow] runs the real composite TRACE32 STM32H7 JIT lane
