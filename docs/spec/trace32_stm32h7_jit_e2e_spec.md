*Source: `test/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl`*
*Last Updated: 2026-03-29*

---

# TRACE32 STM32H7 Remote JIT End-to-End

**Category:** Integration
**Difficulty:** 4/5
**Status:** Implemented

## Overview

Runs the real composite JIT lane for STM32H7 through the TRACE32 adapter path:

- `run_test_file_composite`
- `Trace32Adapter`
- `T32GdbBridgeClient`
- `RemoteExecutionManager`

Requires a live TRACE32 PowerView session with the repo GDB bridge on `2331`.
