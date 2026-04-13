<!-- codex-research -->
# Research Analysis: x86 QEMU Boot Blockers

Date: 2026-04-13

## Scope

Analyze the current blockers preventing a trustworthy dual-lane x86 QEMU validation flow for:

- `x86_32` probe/browser-soft lane
- `x86_64` wrapper/runtime/browser lane
- QEMU system-test integrity

This analysis is based on:

- local code inspection
- existing repo reports
- spawned-agent focused research lanes

## Executive Summary

There are three separate problems, not one:

1. `x86_32` app-style entries are blocked by backend support selection, not by QEMU tuple or target naming.
2. `x86_64` wrapper/runtime failures are dominated by wrapper/codegen/runtime-lowering issues after boot handoff, not by browser logic.
3. The current browser QEMU system spec can produce false confidence because it primarily verifies build outputs and declarations, not real boot execution.

The correct fix order is therefore:

1. fix test/harness integrity
2. make `x86_32` a real booting lane through a supported backend path
3. repair the `x86_64` wrapper/codegen/runtime lane

## Problem 1: x86_32 lane blocked by backend support path

### Observations

- The repo already treats `x86_32` as a real architecture:
  - `src/os/kernel/arch/x86_32/**`
  - `examples/simple_os/arch/x86_32/**`
  - `src/os/qemu_runner.spl`
  - `src/os/build.sdn`
- The target triple is consistent:
  - `i686-unknown-none`
- The QEMU tuple is consistent:
  - `qemu-system-i386`
  - `pc`
  - `qemu32`
- The failure seen on app-style x86_32 entries is:
  - `codegen init: Compilation error: Support for this target has not been implemented yet`

### Root cause

The immediate blocker is backend support, not architecture metadata.

The current app-style runner build path uses:

- `native-build`
- `--backend cranelift`
- `--entry-closure`

The local/compiler evidence shows:

- Cranelift is the unsupported path for current `i686` app-style builds.
- LLVM already has more explicit x86 support plumbing than the Cranelift path for this target family.

### Conclusion

`x86_32` is not blocked by QEMU or lane definition.

It is blocked because the current implementation path routes it through a backend/build flow that does not support the target in the way these app-style baremetal entries need.

## Problem 2: x86_64 lane blocked by wrapper/codegen/runtime lowering

### Observations

- The x86_64 boot stub and C runtime handoff exist:
  - `examples/simple_os/arch/x86_64/boot/crt0.s`
  - `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- Existing reports already distinguish:
  - boot stub works far enough to call `spl_start()`
  - Simple/runtime path then faults
- Direct disassembly of the generated `spl_start` for probe entries showed absurdly large stack reservations even after runtime strings were removed from the first marker path.
- Existing reports also describe unresolved or mislowered runtime calls resolving to `0x0`, producing:
  - `FAULT @ 0x0`
  - `FAULT @ 0x3`

### Root cause

The current x86_64 failure is not primarily browser logic.

It is a wrapper/codegen/runtime-lowering problem in the generated entry path after boot handoff:

- oversized frame/prologue generation
- unresolved or invalid indirect runtime calls
- entry-closure/wrapper lowering interactions

### Conclusion

`x86_64` should remain an investigation lane until the wrapper/codegen/runtime path is repaired.

It should not be treated as the acceptance lane for browser/desktop validation yet.

## Problem 3: system-test integrity is too weak

### Observations

- The browser QEMU system spec has been able to pass very quickly.
- The harness and runner already contain real execution paths:
  - spawn QEMU
  - wait for markers
  - read serial logs
- But the current browser system test can still over-credit:
  - build success
  - output file existence
  - lane declaration checks
- The test database also shows many stale/running entries, which makes cached or build-only green states more plausible.

### Root cause

The current spec does not require enough real runtime evidence.

Build-only success and declared targets are useful, but they are not proof of:

- boot reached `spl_start`
- marker sequence executed
- guest exited cleanly
- lane survived early runtime init

### Conclusion

The first fix should strengthen the test contract.

If the spec is weak, every later fix can look green when it is not.

## Supporting Evidence

### Key local files

- `src/os/qemu_runner.spl`
- `test/qemu/os/common/qemu_os_harness.spl`
- `src/compiler_rust/driver/src/cli/native_build.rs`
- `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs`
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`
- `src/compiler_rust/compiler/src/codegen/instr/body.rs`
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs`
- `examples/simple_os/arch/x86_32/browser_probe_entry.spl`
- `examples/simple_os/arch/x86_32/browser_soft_entry.spl`
- `examples/simple_os/arch/x86_64/browser_probe_entry.spl`
- `examples/simple_os/arch/x86_64/browser_soft_entry.spl`
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/linker.ld`

### Key existing reports

- `doc/01_research/local/simpleos_qemu_validation.md`
- `doc/08_tracking/bug/os_qemu_boot_status_2026-04-04.md`
- `doc/08_tracking/bug/os_build_crash_report_2026-04-03.md`

## Recommended Strategy

### Acceptance strategy

- `x86_32` becomes the first passing boot/probe/browser-soft lane.
- `x86_64` remains a visible investigation lane.

### Engineering strategy

- fix test integrity first
- then enable a supported x86_32 build/runtime path
- then fix x86_64 wrapper/codegen/runtime lowering

## Implementation-Oriented Conclusions

### x86_32

- The immediate patch point is `src/os/qemu_runner.spl:build_os()`.
- Today it hardcodes `--backend cranelift` for all app-style OS lanes.
- The repo already has LLVM backend support wired through `simple native-build`, and target plumbing for `TargetArch::X86`.
- The smallest viable bring-up is:
  - keep `examples/simple_os/arch/x86_32/browser_soft_entry.spl` minimal
  - route the x86_32 app-style lane to `--backend llvm`
  - prove real QEMU boot with raw serial markers before importing browser subsystems

### x86_64

- The first debugging target is not Browser Demo. It is the generated `spl_start` path for the probe lane.
- The likely hot spots are:
  - function prologue / frame growth
  - closure wrapper lowering
  - indirect runtime-call lowering
  - linker-time aliasing combined with unresolved-symbol tolerance
- The shortest path is:
  - compare probe vs browser-soft vs desktop generated `spl_start`
  - log per-function frame estimates for `spl_start`
  - log unresolved/null indirect-call targets before final link

### Spec integrity

- `test/system/browser_engine_in_qemu_spec.spl` is not yet a runtime proof.
- The repo already has the harness primitives needed to make it one:
  - `spawn_guest_with_qmp(...)`
  - `wait_for_serial_marker(...)`
  - `read_serial_log(...)`
  - `stop_guest(...)`
- The stronger template is `test/system/engine2d_in_qemu_spec.spl`, not the current browser spec.

## Spawned-Agent Findings

### Agent lane: x86_32 support

- Confirmed the target triple and QEMU tuple are already correct.
- Confirmed the main blocker is backend routing, not target metadata.
- Recommended first patch: switch x86_32 app-style lane to LLVM.

### Agent lane: x86_64 wrapper/runtime

- Confirmed the dominant issue is wrapper/codegen/runtime lowering after boot handoff.
- Recommended first debug pass: instrument `spl_start` frame/prologue and indirect call targets.

### Agent lane: spec/harness integrity

- Confirmed the browser spec currently over-credits build success.
- Recommended first test patch: require actual QEMU spawn plus marker wait and fault rejection.

### Anti-patterns to avoid

- treating an ELF32-wrapped x86_64 artifact as proof of native x86_64 success
- treating build success as boot success
- debugging browser logic before wrapper/runtime correctness
