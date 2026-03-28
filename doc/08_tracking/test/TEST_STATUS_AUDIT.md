# Test Status Audit

**Date:** 2026-02-24
**Baseline (WS2+WS3 fixes applied):** 8,731 passed / 2,052 failed / 43 timeout (574 files)
**Prior baseline (2026-01-30):** 6,436 passed / 786 failed (7,222 tests across 129 failing files)

---

## Summary

This audit categorizes all known unfixable or structurally limited test failures into four root cause categories. "Unfixable" means the failure cannot be resolved by changing test code alone — it requires runtime binary changes, compiler feature additions, or external infrastructure.

| Category | Files | Est. Tests | Resolution Path |
|----------|-------|-----------|----------------|
| A: Missing Runtime Externs | 10 | ~342 | Add externs to runtime binary |
| B: Interpreter Runtime Limitations | ~15 | ~120 | Compiler/interpreter upgrade |
| C: Timeout Tests | ~43 | N/A | External infrastructure required |
| D: Pre-existing Semantic Failures | ~8 | ~65 | Source implementation needed |
| **Total** | **~76** | **~527** | |

---

## Category A: Missing Runtime Extern Functions

These tests declare `extern fn` bindings that call C functions not present in the current `bin/release/simple` runtime binary. The Simple wrapper code in `src/app/io/` and `src/lib/` is correct but the underlying C symbol is absent from the linked binary. Interpreter mode cannot stub these because the tests call through to actual extern resolution.

**Resolution:** Each requires adding the corresponding C implementation to `src/runtime/runtime.c` and rebuilding the binary. Alternatively, a Simple-level stub module (like `debug_stubs.spl`) can shadow the extern with a pure-Simple fallback.

| File | Missing Extern | Test Count | Notes |
|------|---------------|-----------|-------|
| `test/dyn_torch_test.spl` | `rt_torch_available` (via `DynLoader`) | 0 it-blocks (top-level script) | Calls `dyn_torch_available()` which uses `DynLoader.call0` — fails when `libspl_torch.so` is absent |
| `test/feature/app/fault_detection_spec.spl` | `rt_fault_set_stack_overflow_detection` | 36 | Stubs exist in `src/app/io/debug_stubs.spl` but the test uses `use std.sys.fault_detection.*` which must resolve differently. The `debug_stubs.spl` approach requires proper module routing. |
| `test/feature/usage/cuda_spec.spl` | `rt_cuda_is_available` | 18 | Defined as `extern fn` in `src/app/io/cuda_ffi.spl`; no runtime C symbol |
| `test/deploy/smoke_spec.spl` | `rt_shell` | 12 | `extern fn rt_shell(cmd: text) -> text` — template exists in `ffi_gen.templates/bootstrap_ffi.txt` but not in binary |
| `test/unit/app/io/gamepad_ffi_spec.spl` | `rt_gamepad_init` | 61 | `extern fn rt_gamepad_init() -> i64` in `gamepad_ffi.spl`; Gilrs library not linked |
| `test/unit/app/io/graphics2d_ffi_spec.spl` | `rt_lyon_path_builder_new` | 59 | `extern fn rt_lyon_path_builder_new() -> i64` in `graphics2d_ffi.spl`; Lyon library not linked |
| `test/unit/app/io/http_ffi_spec.spl` | `rt_http_get` | 45 | `extern fn rt_http_get(url: text) -> (i64, text, text)` in `http_ffi.spl`; HTTP runtime not linked |
| `test/unit/app/io/regex_sffi_spec.spl` | `rt_regex_new` | 25 | `extern fn rt_regex_new(pattern: text) -> i64` in `regex_ffi.spl`; listed in `runtime_symbols.spl` but not in binary |
| `test/unit/app/io/rapier2d_ffi_spec.spl` | `rt_rapier2d_world_new` | 39 | `extern fn rt_rapier2d_world_new(gravity_x: f64, gravity_y: f64) -> i64` in `rapier2d_ffi.spl`; Rapier2D not linked |
| `test/unit/app/io/window_ffi_spec.spl` | `rt_winit_event_loop_new` | 42 | `extern fn rt_winit_event_loop_new() -> i64` in `window_ffi.spl`; Winit not linked (requires display server) |

**Notes:**
- `rt_fault_set_stack_overflow_detection` has Simple-level stubs in `src/app/io/debug_stubs.spl`. If the test imports the right path, these stubs allow tests to pass without runtime changes.
- `rt_shell` has a C implementation template in `src/app/ffi_gen.templates/bootstrap_ffi.txt` but it is not compiled into the pre-built binary.
- The IO FFI libraries (gamepad, graphics2d, http, regex, rapier2d, window) all correspond to external Rust/C crates that would need to be compiled and linked into the binary as shared libraries or static archives.

---

## Category B: Interpreter Runtime Limitations

These tests use features that work in compiled mode but fail or hang in the bootstrap interpreter. The interpreter is a subset implementation and has known gaps.

**Resolution:** These cannot be fixed by changing test logic alone without breaking the intent of the test. They require interpreter upgrades or compilation to native mode.

### B1: Generic Type Parameters at Runtime

The bootstrap interpreter does not fully support parameterized generic types in patterns or return positions.

| File | Limitation | Test Count | Notes |
|------|-----------|-----------|-------|
| `test/unit/app/package/semver_spec.spl` | `Result<Version, text>` generics in `parse_version()` — interpreter hangs on generic return type resolution | ~30 | The test was rewritten to use tuple `(ok, v_opt, err)` as workaround but the module `semver.spl` still uses `Result<T, E>` internally |
| `test/unit/app/package/lockfile_spec.spl` | `Result<Lockfile, text>` in `parse_lockfile_string()` — same generic interpreter issue | ~20 | `parse_lockfile_string` is implemented in `src/app/package/lockfile.spl` but returns `Result<T, E>` |

### B2: Module-Level FFI Calls (Initialization Hang)

Modules that call FFI at top-level (outside any function, executed during import) cause the interpreter to hang because the FFI call blocks module loading.

| File | Limitation | Test Count | Notes |
|------|-----------|-----------|-------|
| `test/unit/std/env_spec.spl` | `use shell.env` triggers `rt_process_run("/bin/sh", ["-c", "pwd"])` at module load | ~8 | Root cause: `env.spl` calls `cwd()` as a module-level `val`, which calls `rt_process_run` at import time |
| `test/unit/std/log_spec.spl` | `use std.log` triggers `rt_env_get("SIMPLE_LOG")` at module load | ~6 | Root cause: `_parse_log_level()` is called as `val LOG_LEVEL = _parse_log_level()` at module scope |

### B3: Complex Closure and Static Method Patterns

The interpreter has known gaps with nested closure captures and static method resolution patterns used in certain test files.

| File | Limitation | Test Count | Notes |
|------|-----------|-----------|-------|
| `test/unit/std/mock_phase5_spec.spl` | Complex mock verification uses lambda predicates and method chaining that may trigger infinite loops in the interpreter's closure resolution | ~20 | Fluent expectation chains with `when_called().then_return()` patterns |
| `test/unit/app/tooling/arg_parsing_spec.spl` | All tests use `skip_it()` — blocked by `GlobalFlags__parse()` static method not supported in bootstrap runtime | ~15 | Not a hang — intentionally skipped; static method support is a known interpreter gap |
| `test/unit/app/diagram/call_flow_profiling_spec.spl` | Calls undeclared FFI functions (`clear_ffi_recording`, `enable_ffi_recording`, etc.) — interpreter hangs trying to resolve undefined symbols | ~10 | Missing `extern fn` declarations; profiling FFI is not yet implemented |

### B4: Dict-as-Class Bug

In certain interpreter code paths, class construction returns a dict rather than a typed class instance. This causes type mismatch failures on field access.

| Symptom | Pattern | Notes |
|---------|---------|-------|
| `Error: semantic: type mismatch: cannot convert dict to int` | Test files that construct class instances inside closures or nested functions | Appears in ~4 files identified in the 2026-02-06 failure analysis; root cause is in the MIR/interpreter class lowering path |

---

## Category C: Timeout Tests

These tests do not fail with an error — they hang until the test runner's timeout (120s) kills them. Timeouts indicate the test requires external infrastructure or triggers an interpreter deadlock.

**Root Cause Groups:**

### C1: MCP Server Infrastructure (~8 files)
Tests that require a running MCP (Model Context Protocol) server. The server must be started separately and the tests connect to it. Without a live server, the socket connection blocks indefinitely.

- `test/unit/app/mcp/failure_analysis_spec.spl` — requires `mcp.simple_lang.db_tools` module (does not exist)
- `test/unit/app/mcp/prompts_spec.spl` — old `import` syntax + type name mismatches (`String` vs `text`, `Bool` vs `bool`) cause interpreter hang

### C2: Module Initialization FFI Hang (~5 files)
Already listed in Category B2. Also counted in the 43-timeout baseline:

- `test/unit/std/env_spec.spl`
- `test/unit/std/log_spec.spl`
- `test/unit/app/package/semver_spec.spl` (generic hang)
- `test/unit/std/mock_phase5_spec.spl` (closure loop)
- `test/unit/app/diagram/call_flow_profiling_spec.spl` (undefined FFI)

### C3: LLVM/WASM Backend Tests (~15 files)
Tests that invoke the LLVM or WASM backend compilation pipeline. The compiled backend binaries (`llvm-as`, `wasm-ld`, etc.) are not present in the test environment. The test runner waits for the subprocess indefinitely.

- Various files under `test/system/` and `test/feature/` that call `bin/simple compile --backend=llvm ...` or `--backend=wasm`

### C4: Network Connectivity Tests (~10 files)
Tests that open real TCP/UDP sockets or make HTTP requests to external services. Without network access or the target server, the connection blocks.

- HTTP integration tests that are not part of the `http_ffi_spec.spl` unit test suite
- WebSocket tests under `test/unit/app/io/`

### C5: Interpreter Deadlock / Infinite Loop (~5 files)
Tests where the test logic itself triggers an infinite loop due to interpreter bugs (e.g., recursive closures, broken exit conditions in `while` loops inside methods).

**Note:** The exact 43-file list from the "574 files" baseline requires a fresh `bin/simple test --list` run to enumerate precisely. The groups above account for the known categories.

---

## Category D: Pre-existing Semantic Failures

These tests fail because the source modules they test have unimplemented functions or incorrect implementations. The test code is correct — the implementation is missing.

**Resolution:** Each requires implementing the missing function in the source module. These are tracked as known work items.

| File | Missing/Broken Feature | Est. Tests | When Fixable |
|------|----------------------|-----------|-------------|
| `test/unit/app/package/lockfile_spec.spl` | `parse_lockfile_string` exists but returns `Result<T, E>` which the interpreter cannot handle — same as B1 | ~20 | When interpreter supports generics or module returns plain tuples |
| `test/unit/app/build/cargo_spec.spl` | `parse_sdn_config` not implemented in `app.build.config`; `parse_build_args` may also be missing | ~15 | When build config parser is completed |
| `test/unit/app/mcp/di_handler_wiring_spec.spl` | Dependency injection wiring for MCP handlers; some DI container methods not implemented | ~10 | When MCP DI wiring is complete |
| `test/unit/app/test_runner_new/integration_test_config_spec.spl` | `IntegrationTestConfig` struct fields or constructors differ from test expectations | ~8 | When test runner config API is stabilized |
| `test/unit/app/test_runner_new/test_config_spec.spl` | Similar config struct mismatch | ~6 | When test runner config API is stabilized |
| `test/feature/usage/cuda_spec.spl` | `cuda_available()` calls `rt_cuda_is_available` extern which is not in binary (see also Cat A) | 18 | When CUDA runtime is linked |

**Previously reported (WS2+WS3) but now resolved:**
- `test/feature/search_spec.spl` — file does not exist at this path (may have been renamed/deleted)
- `test/unit/app/package/lockfile_spec.spl` — `parse_lockfile_string` is implemented but blocked by generics (Cat B1)

---

## Known Limitation Notes

### What Requires Runtime Binary Changes
1. All Category A extern functions require C implementations added to `src/runtime/runtime.c` (or linked shared libraries) and the binary rebuilt. These cannot be worked around at the Simple language level without stubs.
2. `rt_shell` has an implementation template in `src/app/ffi_gen.templates/bootstrap_ffi.txt` that is ready to compile into the binary.
3. The `debug_stubs.spl` pattern (Simple-level stubs for extern fns) is the recommended workaround for functions that can return safe defaults. It has already been applied to fault detection functions.

### What Requires Interpreter Upgrades
1. Generic type parameters (`Result<T, E>`, `Option<T>`, `List<T>`) in function return types cause interpreter hangs in some configurations. This is a known gap in the bootstrap interpreter — not in the compiled backend.
2. Module-level FFI calls are an anti-pattern that causes hang-on-import. The fix is to make these calls lazy (call on first use, not at module load time).
3. Static methods (`Type.method()`) are not fully supported in the bootstrap interpreter. Tests that require static methods must use the compiled binary.
4. Nested closure mutation of outer variables is not supported in the interpreter. Closures can read outer vars but not write them.

### What Requires External Infrastructure
1. MCP server tests require a running MCP server process.
2. LLVM/WASM backend tests require the respective compiler toolchains installed.
3. Network tests require connectivity and target servers.
4. GPU tests (`cuda_spec.spl`, `vulkan_spec.spl`) require actual hardware with drivers.
5. Hardware IO tests (gamepad, windowing) require physical devices or display servers.

### Interpreter Mode Test Limitation (All Tests)
The test runner in interpreter mode only verifies that the test file loads without error. The `it` block bodies are registered but **not executed** in interpreter mode. A test file showing "1 passed, 6ms" means only that the file parsed and loaded — not that any actual assertions ran. Use compiled mode for behavioral verification.

### Stable Baseline
The following test categories are consistently passing and should not regress:
- Parser features, async/coroutines, LSP infrastructure, compiler backend tests
- Standard library (text, math, json, crypto, encoding)
- Physics engine, game engine component tests (stub-based)
- ML/tensor tests (stub-based, no actual GPU required)
- TreeSitter parser integration

---

## Related Documents

- `doc/test/test_failures_summary.md` — 2026-02-06 failure breakdown by error type (355 failing files)
- `doc/test/HANG_ANALYSIS.md` — Root cause analysis for 8 timeout tests (2026-02-14)
- `doc/test/FAILURE_ANALYSIS_2026-01-30.md` — 786 failures across 129 files (2026-01-30)
- `doc/test/LATEST_TEST_RUN_2026-01-30.md` — 6,436/7,222 passing (89.1%) with 0 parse errors
- `doc/test/TEST_STATUS_AUDIT.md` — (this file, replaces the 2026-02-14 @skip/@pending audit)
