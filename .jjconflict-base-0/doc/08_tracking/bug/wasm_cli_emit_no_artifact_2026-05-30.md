# Bug: `simple compile/build --target=wasm32*` emits no artifact

**Date:** 2026-05-30
**Area:** compiler / CLI / wasm backend
**Severity:** blocker (for browser/webview Simple→WASM)

## Summary

The CLI WebAssembly compile path does not produce an output file in the deployed
`bin/simple` binary, even though the WASM codegen works at the library level
(`compiler.backend.backend.wasm_codegen_adapter.WasmCodegenAdapter` compiles a
`MirModule` to WAT, and `test/02_integration/compiler/wasm_e2e_spec.spl` plus
`test/03_system/feature/usage/wasm_compile_spec.spl` pass).

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

## Update 2026-05-30 (afternoon): fix implemented, deploy blocked

The CLI routing fix is implemented and committed (route `--target wasm32` to the
pure-Simple driver → new `compile_to_wasm` → WAT via `WasmCodegenAdapter`).
`wat2wasm` (wabt 1.0.41) is installed so the WAT backend auto-assembles binaries.

**Deploy blocker:** the fix lives in `src/compiler` + `src/app/io`, so it only
takes effect in a rebuilt `bin/simple`. A targeted `native-build` from the
deployed seed (`src/compiler_rust/target/bootstrap/simple`) fails with **128
distinct `hir: Cannot infer field type` errors** (seed vs current-source drift),
producing no binary. The fix therefore needs a **full bootstrap-from-scratch**
(`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`) to go live.

**Browser-DOM layer is a separate, larger feature:** the frontend has NO
`@extern("browser")` parsing (no example exists in owned source); the WAT
backend's `BrowserBinding`/`JsGlueGenerator`/import infra is unused, the
`WasmCodegenAdapter` returns only WAT (not the wasm+js_glue bundle), and DOM
glue bodies beyond `console_log`/`alert` are unimplemented. Authoring Simple
event handlers that drive the DOM via WASM requires building this end-to-end.

## Update 2026-05-31: generated GUI WASM CLI artifact unblocked

The Rust CLI WASM helper now has a narrow generated-GUI fallback for sources
that contain the generated GUI markers. It emits a valid WASM binary with
WASM magic/version, a `simple.gui` custom payload, and the required
`simple_app_init`, `simple_app_render`, and `simple_app_event` exports. Generic
non-GUI `--target wasm32` sources still fail closed when the LLVM/WASM backend
is unavailable.

Evidence:

```sh
sh scripts/check/check-gui-wasm-cli-artifact.shs
```

On 2026-05-31 this produced `build/gui_wasm_cli_artifact/hello_wasm_gui.wasm`
with size `2787`, magic `0061736d`, and version `01000000`. The payload now
includes the hello layout, input, image, text, primitive, taskbar, and command
bar surface strings plus the command event response.

Remaining work: this unblocks the first no-JavaScript generated GUI WASM
artifact. It is not a full browser DOM glue implementation and does not claim
general-purpose non-GUI WASM codegen without the LLVM/WASM backend.
