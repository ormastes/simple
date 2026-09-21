# Phase 2 seed LLVM array method map drift

## Status

Open. Bootstrap seed synchronization is required; the pure-Simple compiler
counterpart already has the correct `write_span` lowering.

## Reproduction

The admitted Phase 2 capsule at compiler SHA-256
`35acf59774028cb8849812abf5762330dfd16f232dacb9bb3b278f176e8b0669`
identifies itself as `simple-bootstrap 1.0.0-beta.14`. A one-file native build
of any of these sources fails in LLVM code generation:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`
- `src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`
- `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`

The diagnostic is:

```text
cannot resolve method call `Array.write_span`: receiver is a builtin type but
`write_span` is neither a known runtime method nor a resolvable user definition
```

Retained full-CLI evidence is under
`build/evidence/phase2-test-20260921/run-2/work/logs/compiler_cli_build.log`.

## Root cause

The Rust bootstrap compiler's Cranelift tables map `write_span` to
`rt_array_write_span`, and its interpreter has the dedicated mutating-method
write-back path. The LLVM `MethodCallStatic` table in
`src/compiler_rust/compiler/src/codegen/llvm/functions.rs` omits that same
mapping and reaches its fail-closed builtin receiver diagnostic.

The pure-Simple compiler is already synchronized:

- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` lowers
  unresolved four-argument `write_span` through
  `lower_unresolved_array_write_span`.
- `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`
  declares and types `rt_array_write_span`.

## Required fix

Synchronize only the bootstrap seed LLVM method table by adding
`"write_span" => Some("rt_array_write_span")`, with a focused LLVM backend
regression that constructs an `Array.write_span` static method call and asserts
the emitted IR calls `rt_array_write_span`.

Do not replace product calls with direct extern calls. Interpreter correctness
depends on the mutating-method channel to write the updated array back through
nested `mut` parameters. A direct extern route compiles natively but changes
interpreter behavior.
