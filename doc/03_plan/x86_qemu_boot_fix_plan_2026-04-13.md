# Fix Plan: x86 QEMU Boot Blockers

Date: 2026-04-13

## Objective

Move from today’s mixed false-positive / broken-wrapper state to a trustworthy dual-lane x86 QEMU validation model.

## Principles

1. Fix test integrity before fixing implementation details.
2. Get one real passing lane first.
3. Keep `x86_32` and `x86_64` separate in both boot model and acceptance criteria.
4. Do not let `x86_64` compatibility packaging stand in for native x86_64 success.

## Staged Plan

### Stage 1: Harden test integrity

Goal:

- eliminate build-only false positives

Changes:

- split browser-QEMU specs into:
  - declaration/build checks
  - real execution checks
- require execution checks to:
  - spawn QEMU
  - wait for lane-specific serial markers
  - reject `FAULT @`
  - require clean exit or explicit `TEST PASSED`
- ensure direct QEMU runs remain part of debugging/validation, not just spec cache state

Files:

- `test/system/browser_engine_in_qemu_spec.spl`
- `test/qemu/os/common/qemu_os_harness.spl`
- `src/os/qemu_runner.spl`

Patch order:

1. keep the current lane-declaration/build checks as a separate block
2. add real execution cases that:
   - call `spawn_guest_with_qmp(...)`
   - wait for a lane-specific marker
   - fail on `FAULT @`
   - stop the guest deterministically
3. use `test/system/engine2d_in_qemu_spec.spl` as the stronger shape reference

Success criteria:

- a green runtime spec proves actual boot/marker execution
- build-only results are not counted as boot success

### Stage 2: Make x86_32 a real passing lane

Goal:

- get one trustworthy passing probe/browser-soft lane

Changes:

- route app-style x86_32 lane through a backend/build path that actually supports `i686`
- keep the lane minimal:
  - probe
  - raw marker
  - placeholder browser-soft or real software-render smoke if backend/runtime supports it

Files:

- `src/os/qemu_runner.spl`
- compiler/backend selection path for `native-build`
- `examples/simple_os/arch/x86_32/**`

Patch order:

1. update `src/os/qemu_runner.spl:build_os()` so x86_32 app-style lanes select `--backend llvm`
2. keep `examples/simple_os/arch/x86_32/browser_soft_entry.spl` as a raw-marker lane first
3. add real QEMU execution assertions for that lane
4. only after it passes, widen it into a real browser software-render smoke lane

Decision:

- do not force `x86_32` through the current unsupported Cranelift app-style path
- prefer LLVM or another already-supported x86 path for the first passing lane

Success criteria:

- `x86_32` entry builds
- QEMU boots it under `qemu-system-i386`
- lane-specific marker appears
- no early `FAULT @`

### Stage 3: Repair x86_64 wrapper/runtime entry

Goal:

- make the `x86_64` wrapper path reach first marker reliably

Changes:

- inspect generated `spl_start` prologue/frame sizing
- isolate oversized stack reservation generation
- verify indirect runtime calls resolve to real addresses
- reduce entry-closure/wrapper-lowering hazards before reintroducing richer browser/desktop behavior

Files:

- x86_64 wrapper entries
- codegen/lowering path that emits entry wrappers and prologues
- any runtime symbol-resolution path involved in wrapper entry

Primary code areas:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`
- `src/compiler_rust/compiler/src/codegen/instr/body.rs`
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs`
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/linker.ld`

Patch order:

1. instrument the probe lane first, not browser-soft or desktop
2. log `spl_start` frame/prologue size drivers during codegen
3. log unresolved or null indirect runtime-call targets before final link
4. compare probe vs browser-soft generated entry behavior
5. only after the probe is stable, move back to browser-soft and desktop

Success criteria:

- x86_64 probe reaches raw marker
- no repeated early fault loop

### Stage 4: Restore x86_64 browser-soft lane

Goal:

- promote x86_64 from investigation to runtime/browser validation

Changes:

- keep raw early marker
- add stage markers after:
  - DOM
  - layout
  - paint
  - scene
  - raster
- only after wrapper/runtime is stable, trust browser-soft pass markers

Success criteria:

- x86_64 browser-soft reaches final pass marker
- no early fault output

### Stage 5: Restore x86_64 desktop/browser integration lane

Goal:

- restore full desktop/browser validation on x86_64

Changes:

- re-enable launcher/WM/browser flow as the full lane
- keep lane-specific marker order strict

Success criteria:

- desktop/browser wrapper lane reaches final pass markers

## Parallel Workstreams

### Workstream A: Test Integrity

Owns:

- spec split
- harness strengthening
- marker/exit requirements

### Workstream B: x86_32 Bring-Up

Owns:

- supported backend path
- x86_32 probe/browser-soft lane
- first passing QEMU lane

### Workstream C: x86_64 Wrapper Repair

Owns:

- stack-frame/prologue investigation
- runtime-call resolution
- wrapper-lowering fixes

## Risk Notes

- If Stage 1 is skipped, later work may produce more false greens.
- If Stage 2 is skipped, there is no trustworthy passing lane to anchor regression work.
- If Stage 3 is attempted before test integrity is fixed, x86_64 investigations will remain noisy and hard to trust.

## Recommended Next Action

Start with Stage 1 and Stage 2 together:

- tighten runtime proof in the spec/harness
- route `x86_32` through a supported backend path

Do not spend another cycle on `x86_64` browser logic until the wrapper/runtime entry itself is proven stable.

## Explicit Spawn-Agent Lane Split

### Agent 1: Test/harness integrity

- own `test/system/browser_engine_in_qemu_spec.spl`
- own shared harness helpers in `test/qemu/os/common/qemu_os_harness.spl`
- goal: convert browser QEMU validation from build proof to boot proof

### Agent 2: x86_32 bring-up

- own `src/os/qemu_runner.spl` x86_32 backend selection
- own `examples/simple_os/arch/x86_32/browser_soft_entry.spl`
- goal: establish the first real passing x86_32 QEMU lane

### Agent 3: x86_64 wrapper/runtime repair

- own x86_64 probe entry investigation and compiler/linker instrumentation
- goal: make the x86_64 probe reach its first raw marker without early fault

## Smallest Next Patch Set

### Patch A: Make the browser spec a real boot proof

Files:

- `test/system/browser_engine_in_qemu_spec.spl`

Exact flow:

1. keep current declaration/build checks as separate metadata tests
2. convert the x86_64 browser-soft case into a live boot case:
   - `build_os(target)`
   - `file_exists(target.output)`
   - `can_run_target(target)`
   - `spawn_guest_with_qmp(target, qmp_socket, serial_log)`
   - `wait_for_serial_marker(handle, "[PASS] browser_soft_entry", 30000)`
   - `stop_guest(handle)` on every exit path
3. fail the live case if serial output contains `FAULT @`

Reason:

- this is the smallest change that turns a false-green-prone build test into a real execution proof

### Patch B: Route x86_32 browser-soft to a supported backend

Files:

- `src/os/qemu_runner.spl`
- `examples/simple_os/arch/x86_32/browser_soft_entry.spl`

Exact flow:

1. add a tiny helper such as `_backend_for_target(target)`
2. replace hardcoded `--backend cranelift` in `build_os()` with that helper
3. make the helper return:
   - `llvm` for `Architecture.X86` plus `examples/simple_os/arch/x86_32/browser_soft_entry.spl`
   - `cranelift` otherwise
4. keep the x86_32 browser-soft entry minimal:
   - `[browser-soft-x86_32] start`
   - `[browser-soft-x86_32] PASS`
   - `TEST PASSED`
   - debug-exit via port `0xF4`
5. do not import DOM/layout/paint/render modules yet

Reason:

- this establishes the first realistic passing x86 lane with the smallest possible runtime surface

### Patch C: Add the first x86_64 wrapper instrumentation only

Files:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`

Exact flow:

1. in LLVM function compilation, print one `spl_start` summary:
   - param count
   - local count
   - vreg count
   - local/vreg alloca counts
2. in closure/indirect-call lowering, print whether a function pointer resolves or falls back to `0`
3. in baremetal stubs, print around the `spl_start()` call and record the first faulting RIP once

Reason:

- this is the smallest instrumentation set that separates giant-frame failure from null-indirect-call failure

## Recommended Immediate Order

1. Patch A
2. Patch B
3. run the browser spec again and direct x86_32 QEMU boot
4. only then land Patch C if x86_64 still needs focused investigation
