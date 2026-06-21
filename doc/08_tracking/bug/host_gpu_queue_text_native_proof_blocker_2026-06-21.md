# Host GPU Queue Text Native Proof Blocker

Date: 2026-06-21

## Status

Resolved on 2026-06-21.

## Summary

The GUI/web host-GPU queue evidence now passes on Linux, but the payload-text
path also has focused native/JIT proof with fallback disabled.

## Evidence

- Passing report: `doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-21.md`
- Runtime text probe: `test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl`
- Interpreter bridge: `src/compiler_rust/compiler/src/interpreter_extern/host_gpu_lane.rs`
- Native C ABI surface: `src/runtime/runtime_native.c`
- Codegen SFFI table entry: `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`

## Resolved Gap

Earlier verification proved queue payload text roundtrip and BrowserBackend
same-frame readback evidence through interpreter/runtime evidence only. The
native/JIT path now exports and decodes the queue text ABI directly.

## Fix

- `src/compiler_rust/runtime/src/host_gpu_lane.rs` exports
  `rt_host_gpu_queue_emit_payload_text`, payload size/hash getters, and a
  runtime-value text getter for JIT/native calls.
- The interpreter bridge calls the internal Rust helper, so interpreter behavior
  stays unchanged.

## Acceptance Evidence

Command:

```bash
SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 \
  src/compiler_rust/target/debug/simple run \
  test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl
```

Result:

- no `JIT compilation failed`, `falling back`, unresolved symbol, or stub
  fallback message
- `queue_nonzero_backend_last_backend_handle=7`
- `queue_nonzero_backend_last_payload_hash=98765`
- `queue_nonzero_backend_last_payload_text=queue probe payload command=draw_ir_rect id=runtime-backend`
