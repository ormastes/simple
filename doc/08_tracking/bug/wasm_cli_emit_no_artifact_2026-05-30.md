# Bug: `simple compile/build --target=wasm32*` emits no artifact

**Date:** 2026-05-30
**Area:** compiler / CLI / wasm backend
**Severity:** blocker (for browser/webview Simple→WASM)

## Summary

The CLI WebAssembly compile path does not produce an output file in the deployed
`bin/simple` binary, even though the WASM codegen works at the library level
(`compiler.backend.backend.wasm_codegen_adapter.WasmCodegenAdapter` compiles a
`MirModule` to WAT, and `test/integration/compiler/wasm_e2e_spec.spl` plus
`test/feature/usage/wasm_compile_spec.spl` pass).

## Repro

```sh
printf 'pub fn add(a: i32, b: i32) -> i32:\n    return a + b\n' > /tmp/w.spl

bin/simple compile /tmp/w.spl --target wasm32-wasi -o /tmp/w.wasm   # EXIT=3, no /tmp/w.wasm, no diagnostic
bin/simple compile /tmp/w.spl --target wasm32      -o /tmp/w.wasm   # EXIT=3, no file
bin/simple build   /tmp/w.spl --target=wasm32-wasi --wasm-backend=wat -o /tmp/w.wasm  # EXIT=0, no file
```

All variants either exit non-zero with no diagnostic or exit 0 while writing
nothing. `bin/simple targets` advertises `wasm32`, `wasm32-wasi`, `wasm64`, and
the help advertises `--target=wasm32-wasi` / `--wasm-backend=auto|llvm|wat`.

## Likely cause

- The binary `.wasm` route goes through LLVM, and the deployed
  `bin/release/<triple>/simple` is built without LLVM (Rust seed default).
- The `wat` backend (pure-Simple, no LLVM) is wired into the codegen library
  but the CLI `compile/build` emit path does not flush a file to `-o`.

## Impact

Blocks authoring browser/webview client logic in pure Simple compiled to WASM
(required instead of hand-written JS for the Tauri mobile interaction layer).
Also blocks any standalone `wasm32` deliverable from the deployed toolchain.

## Next steps

1. Wire the `wat` backend to actually write the `-o` file from `compile`/`build`
   (no LLVM needed) and return a non-zero exit with a diagnostic on failure.
2. Provide/verify an LLVM-enabled `bin/simple` for the binary `.wasm` route, or
   pipe WAT → wasm via the bundled assembler.
3. Add a browser-DOM `@extern("browser", ...)` end-to-end example
   (compile → load in HTML → handle a click) — infra exists in
   `src/compiler_rust/compiler/src/codegen/wasm_bindgen_gen.rs` /
   `web_compiler.rs` but no working sample, and string/event marshalling is
   undocumented.
