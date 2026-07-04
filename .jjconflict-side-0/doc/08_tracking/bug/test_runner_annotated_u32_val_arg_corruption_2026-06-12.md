# Annotated u32 `val` locals corrupt as call args in it blocks under `bin/simple test`

Date: 2026-06-12
Status: fixed (seed interpreter, 2026-06-12); run-mode in the deployed stage4
binary still carries the old behavior until the next stage4 redeploy
Owner: gpu-backend-dx-harden lane

## Root Cause (corrected)

Not u32-specific and not call-arg-specific. The Rust seed interpreter has a
dedicated statement walker for NESTED blocks inside closure bodies
(`exec_block_closure_mut` in
`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`). Its
`Node::Let` arm hand-rolled binding for only `Pattern::Identifier` /
`MutIdentifier` / `MoveIdentifier` — so `val x: T = ...` (Pattern::Typed) and
tuple/array destructuring inside `if`/`while`/`else` bodies within a
describe/it lambda evaluated their RHS but bound NOTHING. The next read
failed with "variable `x` not found". Top-level it-block statements were
unaffected because `exec_block_closure` already used `bind_pattern_value`.

## Fix

`exec_block_closure_mut` now binds via the shared `bind_pattern_value`
(same as the top-level walker). Verified after seed rebuild:
- regression spec `test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl` 5/5
- the ORIGINAL annotated backend_vulkan_processing_spec content: 22/22 (was 17/5)
- current vulkan specs unchanged 22/22 + 22/22

## Summary

Inside an `it` block executed by `bin/simple test`, a local with an explicit
u32 annotation:

```spl
val red: u32 = 0xFF0000FFu32
b.clear(red)                       # it block errors here, asserts never run
```

fails the test, while BOTH of these pass with identical semantics:

```spl
val red = 0xFF0000FFu32            # no annotation
b.clear(red)
b.clear(0xFF0000FFu32)             # inline literal
```

The same corruption hits matcher args: `expect(pixels[0]).to_equal(green)`
fails when `green` is an annotated u32 val, while
`assert_equal(pixels[0], 0x00FF00FFu32)` and
`val m = pixels[0] == 0x00FF00FFu32` agree the value is correct.

`bin/simple run` is NOT affected — the same code prints the correct pixel
value (verified: clear(green) → read_pixels()[0] == 0x00FF00FF via lavapipe).

## Repro (minimized, 2026-06-12, self-hosted deploy + rebuilt seed)

Two spec files differing ONLY in `val red: u32 = ...` vs `val red = ...`:
annotated fails 0/1, unannotated passes 1/1. Bisect history: this single
trigger accounted for all 8 "Vulkan device path" failures in
backend_vulkan_processing_spec (5) and backend_vulkan_drawing_spec (3);
after stripping the annotations both specs are 22/22.

## Workaround applied

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_{processing,drawing}_spec.spl`
now use unannotated `val` color bindings (literal-typed by the u32 suffix).
Do not silently normalize this elsewhere — fix the runner/interpreter typed-
binding argument path instead.

## Also fixed while isolating

- `VulkanBackend.read_pixels` mutated `self.host_buf` inside an immutable
  `fn` (HIR lowering error, JIT fallback): dirty reads now return device bytes
  directly; `present()` owns the cache refresh.
- The specs used a nonexistent `to_not_equal` matcher in degradation branches;
  replaced with the sanctioned `assert_not_equal`.
