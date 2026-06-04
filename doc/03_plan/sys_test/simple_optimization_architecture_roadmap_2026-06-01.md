# Simple Optimization Architecture Roadmap Smoke Plan

Date: 2026-06-01

This is the focused cross-lane smoke list for the active optimization roadmap.
It is evidence for roadmap lane F and should be run after coherent JS/WASM, GUI,
interpreter, compiler, or profile-planning slices.

## Always Run

```bash
sh scripts/setup/install-spipe-dev-command.shs --check
git diff --check
find doc/06_spec -name '*_spec.spl' | wc -l
```

The `find` command must print `0`.

## JS/WASM Lane

```bash
SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl
SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean
```

## GUI Rendering Lane

```bash
SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild
scripts/check/check-gtk-gui-repeat-evidence.shs
```

If vector-font or GPU evidence is unavailable, record the unavailable backend
and the fallback probe output instead of claiming a hardware win.

## Interpreter Runtime Lane

```bash
SIMPLE_LIB=src bin/simple test test/unit/app/interpreter/perf_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

## Compiler/Profile Lane

Run when `.sprof`, MIR, SMF, JIT, or optimization-provider files change:

```bash
SIMPLE_LIB=src bin/simple check src/compiler
SIMPLE_LIB=src bin/simple test test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
cargo check -p simple-common -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

## MCP/LSP Escalation

Run only when `src/compiler/**`, `src/lib/**`, MCP, LSP, npm package, or release
paths change in a way that can affect tool startup or language surface:

```bash
SIMPLE_LIB=src bin/simple check src/app/mcp
SIMPLE_LIB=src bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

If package/release paths changed, also run the native-build package smoke gates
from `AGENTS.md`.
