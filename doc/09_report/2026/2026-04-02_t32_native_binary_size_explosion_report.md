# TRACE32 Native Binary Size Explosion Report

Date: 2026-04-02

## Summary

The repeated native binary size explosions were caused by the native build pipeline
linking `libsimple_native_all.a` into ordinary application binaries with
`--whole-archive`.

That archive contains large LLVM-backed runtime content, including backend target
objects and global constructors. Because the old selection logic always preferred
`libsimple_native_all.a` whenever it existed, non-compiler applications such as
`t32_mcp` repeatedly inherited the full LLVM payload and inflated to roughly
`177 MB`.

This report covers:

- the root cause
- the compiler-side fix
- before/after evidence
- the remaining runtime issues after the size fix
- the current wrapper status after the native default flip

## Root Cause

The size explosion happened in the native build pipeline, not in the `t32_mcp`
application logic itself.

Before the fix:

- `NativeProjectBuilder::link_objects()` effectively preferred
  `libsimple_native_all.a` over `libsimple_runtime.a`
- the selected archive was linked with `--whole-archive`
- `libsimple_native_all.a` was present in normal release runtime directories
- therefore almost every native app build dragged in LLVM-heavy objects even when
  the app did not need compiler functionality

This made the failure repeat "all the time" because the condition was structural:

1. native-build looked in the release runtime dir
2. `libsimple_native_all.a` existed there
3. the builder preferred it
4. the linker forced the whole archive in
5. every non-compiler app became an LLVM-sized binary

## Evidence

### Before

Observed large artifact:

- `bin/release/t32_mcp_native`: about `177 MB`

Observed runtime archives:

- `src/compiler_rust/target/release/libsimple_native_all.a`: about `430 MB`
- `src/compiler_rust/target/release/libsimple_runtime.a`: about `51 MB`

Section sizes from the bloated binary:

- `.text`: about `85,797,826`
- `.rodata`: about `45,512,958`
- total loaded sections: about `155,981,596`

Symbol evidence from the bloated binary and runtime archive showed many LLVM
target constructors and backend-specific objects, for example:

- `_GLOBAL__sub_I_AArch64...`
- `_GLOBAL__sub_I_AMDGPU...`
- `_GLOBAL__sub_I_ARM...`
- `_GLOBAL__sub_I_RISCV...`
- `_GLOBAL__sub_I_X86...`

That is direct evidence that non-compiler application binaries were pulling
backend registration code they should not have linked.

### After

Rebuilt command:

```bash
src/compiler_rust/target/release/simple native-build \
  --entry-closure \
  --source examples/10_tooling/trace32_tools \
  --entry examples/10_tooling/trace32_tools/t32_mcp/frontend_light.spl \
  --runtime-path src/compiler_rust/target/release \
  -o /tmp/t32_mcp_cold_native_auto
```

Result:

- `/tmp/t32_mcp_cold_native_auto`: about `16.7 MB`
- current checked-in `bin/release/t32_mcp_native`: about `17 MB`

Section sizes:

- `.text`: about `6,076,676`
- `.rodata`: about `1,068,153`

`nm` no longer shows the previous LLVM target constructor pattern in the rebuilt
binary.

## Implemented Fix

### 1. Runtime bundle selection in native-build

Changed:

- [native_project.rs](src/compiler_rust/compiler/src/pipeline/native_project.rs)
- [native_build.rs](src/compiler_rust/driver/src/cli/native_build.rs)

New behavior:

- `NativeBuildConfig` now has `runtime_bundle`
- CLI now supports `--runtime-bundle auto|runtime|all`
- `auto` prefers runtime-only for non-compiler apps
- `auto` still prefers `native_all` for compiler/self-hosting paths

Selection heuristic:

- compiler-like entrypoints such as `src/compiler/...` or `src/app/cli/...`
  keep using `native_all`
- non-compiler apps such as `examples/.../t32_mcp/frontend_light.spl`
  prefer `libsimple_runtime.a`

### 2. Linker behavior

New linker behavior:

- `libsimple_runtime.a` is linked directly
- `--whole-archive` is only used when `native_all` is actually selected

This is the key size fix.

### 3. Stub generation alignment

Stub generation now scans the selected runtime library rather than always
implicitly preferring `native_all`.

That keeps unresolved-symbol analysis aligned with the actual runtime bundle.

### 4. Regression tests

Added compiler tests in
[native_project.rs](src/compiler_rust/compiler/src/pipeline/native_project.rs):

- `test_runtime_bundle_auto_prefers_runtime_for_non_compiler_entry`
- `test_runtime_bundle_auto_prefers_native_all_for_compiler_entry`

Both pass in release test runs.

## Additional Native Runtime Fix

After the size fix, the small `t32_mcp` native binary still crashed at runtime.

`gdb` backtrace showed:

- `rt_enum_payload`
- `t32_mcp.frontend_cold.t32_request_id_text`

That was not a linker-size issue anymore. It was a frontend request-scanner issue.

Changed:

- [frontend_cold.spl](examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl)

What changed:

- replaced the old `index_of`-heavy request id extractor with an explicit manual
  scanner
- this removed the crash site in the small native binary

After that fix, the same small native binary now answers `initialize` correctly:

```json
{"jsonrpc":"2.0","id":1,"result":{"protocolVersion":"2025-06-18", ...}}
```

## Current State

### Fixed

- native binary size explosion
- repeated accidental linkage of LLVM-heavy runtime into non-compiler apps
- small native `t32_mcp` binary no longer crashes on the `initialize` probe
- public `t32_mcp` wrapper now prefers native by default and the low-cost probe succeeds
- forced source fallback now also preserves request ids on the tested low-cost probe

### Not fully fixed

The small native `t32_mcp` binary is not yet fully feature-complete on low-cost
MCP flows.

Current observed behavior on a multi-call low-cost probe:

- `initialize`: works
- `tools/list`: works
- `t32_job_list`: works
- `t32_cmm_commands`: works
- `resources/read t32:///sessions`: works

So the current state is:

- size problem: fixed
- native startup crash on first request: fixed
- wrapper-level low-cost probe: succeeds through the public wrapper
- tested low-cost MCP functionality in the small native path: working
- tested source fallback low-cost behavior: working

## Why This Kept Happening

This repeated because the old selection rule encoded the wrong default:

- `libsimple_native_all.a` existed in the normal runtime directory
- the builder preferred it unconditionally
- the link step treated it as whole-archive input

So every new non-compiler native app inherited the same failure mode without
any app-specific mistake.

In other words, the repetition was systemic:

- same runtime layout
- same selection rule
- same linker flags
- same oversized result

## Recommended Follow-up

1. Keep `runtime_bundle=auto` as the default behavior.
2. Use `runtime_bundle=all` only for compiler/self-hosting binaries.
3. Extend verification beyond the currently tested low-cost request set in
   [frontend_cold.spl](examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl)
   so additional low-cost tools are covered in both native and source fallback paths.
4. Add one end-to-end native smoke test for a non-compiler app that asserts:
   - binary size stays below a reasonable threshold
   - representative MCP startup and low-cost request handling succeed
5. Keep native as the default wrapper path because it remains the smaller and
   more reliable execution mode.

## Verification Performed

Build:

- `cargo build --release --bin simple`

Compiler regression tests:

- `cargo test --release -p simple-compiler test_runtime_bundle_auto_prefers_runtime_for_non_compiler_entry -- --nocapture`
- `cargo test --release -p simple-compiler test_runtime_bundle_auto_prefers_native_all_for_compiler_entry -- --nocapture`

Size verification:

- rebuilt `/tmp/t32_mcp_cold_native_auto`
- confirmed size around `16.7 MB`
- confirmed LLVM target constructor pattern no longer appears

Runtime verification:

- before frontend scanner fix: small native binary crashed in `t32_request_id_text`
- after frontend scanner fix: small native binary answers `initialize`
