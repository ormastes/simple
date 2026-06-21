# Host GPU Queue Text Native Proof Blocker

Date: 2026-06-21

## Summary

The GUI/web host-GPU queue evidence now passes on Linux, but the payload-text
path is still proven through the runtime queue contract. This does not satisfy
the longer-term "do not use rt / prefer better Simple native binary" target by
itself.

## Evidence

- Passing report: `doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-21.md`
- Runtime text probe: `test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl`
- Interpreter bridge: `src/compiler_rust/compiler/src/interpreter_extern/host_gpu_lane.rs`
- Native C ABI surface: `src/runtime/runtime_native.c`
- Codegen SFFI table entry: `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`

## Gap

Current verification proves queue payload text roundtrip and BrowserBackend
same-frame readback evidence. It does not yet prove that the optimized
Simple-native/JIT path can emit the same payload text without falling back to
interpreter/runtime evidence.

## Required Fix

Add a native/JIT proof for the same queue text scenario, or replace the
runtime-text dependency with a Simple-owned alias/compiled path that carries the
same payload text into the backend receipt.

Acceptance evidence:

- `runtime_queue_probe.spl` equivalent passes with native/JIT fallback disabled.
- BrowserBackend queue/readback wrapper records the native/JIT text path.
- The generated `doc/06_spec/...` manual says whether the proof is interpreter,
  native/JIT, or host-unavailable.
