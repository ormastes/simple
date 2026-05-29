# Rust Runtime Minimization — Phase 0 Baseline

**Date:** 2026-05-16
**Agent:** Phase 0 (Research and Baseline Only — no Rust code removed)
**Plan ref:** `doc/03_plan/agent_tasks/rust_runtime_minimization.md`

---

## 1. Binary Sizes — Current State (2026-05-16)

All measurements on x86_64-unknown-linux-gnu.

### Host Compiler (`bin/simple`)

| Artifact | Size (bytes) | Size (MB) | Notes |
|---|---|---|---|
| `simple` (current, unstripped) | 28,163,152 | 26.9 MB | May 15 2026, self-hosted interpreter |
| `simple.broken.20260515` (unstripped) | 12,092,416 | 11.5 MB | Not stripped, debug info included |
| `simple.pre-llvm-release` (stripped) | 1,589,168 | 1.5 MB | LLVM-lib backend stripped binary |
| Previous baseline (exe_size_budget_spec) | 9,623,568 | 9.2 MB | Stripped hello-world, measured 2026-04-28 |
| Budget (exe_size_budget_spec) | 12,582,912 | 12.0 MB | 25% headroom over 9.2 MB baseline |

### Runtime Archives (lane discriminators)

| Archive | Lane | Size (bytes) | Size (MB) |
|---|---|---|---|
| `libsimple_runtime.a` | `core-c-bootstrap` / `simple-core` | 38,119,246 | 36.4 MB |
| `libsimple_native_all.a` | `rust-hosted` | 53,452,886 | 51.0 MB |

The `simple-core` lane (pure-Simple archive) is **not yet present** on disk — `auto` falls back to `core-c-bootstrap` for non-compiler entries when no pure-Simple archive is found.

### Tooling Binaries

| Binary | Size (bytes) | Size (MB) |
|---|---|---|
| `simple_mcp_server` (current) | 5,450,968 | 5.2 MB |
| `simple_lsp_mcp_server` (current) | 5,437,992 | 5.2 MB |
| `simple_mcp_server` (linux-x86_64, Apr 2026) | 23,051,864 | 22.0 MB |
| `simple_lsp_mcp_server` (linux-x86_64, Apr 2026) | 22,677,088 | 21.6 MB |

The current (May 2026) MCP/LSP binaries are ~4× smaller than the April builds — a significant recent improvement.

---

## 2. Smoke Binary Sizes — Per-Lane Status

The plan calls for hello, file I/O, TUI, and network smoke binary sizes across `core-c-bootstrap`, `simple-core`, and `rust-hosted` lanes.

**Status: hello fixture absent; file I/O, TUI, and network smoke fixtures confirmed absent. `native-build` exits code 3 in this environment.**

- `build/size-bench/hello.spl` was not pre-built; the directory exists but was empty.
- `bin/simple native-build --entry <file> --runtime-bundle auto --strip -o <output>` exits with code 3 and produces no output binary. Investigation: `native-build` without `--backend=llvm-lib` routes to the Rust `handle_native_build` handler (`src/compiler_rust/driver/src/main.rs:291`), which requires a full native toolchain and linker in PATH. This is not a silent no-op per `feedback_compile_mode_false_greens.md`; it is an environment/toolchain availability issue in this research shell.
- TUI smoke fixture found: `test/system/llm_dashboard_tui_smoke.spl` — runs in interpreter mode, wraps a TUI app with key input; not a compiled native binary.
- Network smoke fixture found: `test/perf/webserver/native_tcp_bind_variable_smoke.spl` — binds TCP in interpreter mode; not a compiled native binary.
- No file I/O standalone smoke fixture found.
- No pre-built `.native` or `.stripped` artifacts exist in `test/system/` or `test/integration/`.
- The existing `exe_size_budget_spec.spl` records the last known stripped hello smoke at **9,623,568 bytes** (2026-04-28) under `--runtime-bundle auto`.

**Recommended Phase 1 action:** Run `bin/simple native-build` with all three `--runtime-bundle` values in a correctly configured shell (with `SIMPLE_LIB=$(pwd)/src`) and record sizes before starting Rust removal. Template command from `src/app/ui/build.spl`:

```
SIMPLE_LIB=$(pwd)/src bin/simple native-build \
    --runtime-bundle <lane> \
    --source src/lib --source src/app \
    --entry <fixture.spl> \
    --entry-closure --strip \
    -o build/size-bench/hello_<lane>.native
```

Valid `--runtime-bundle` values: `auto`, `simple-core`, `core-c-bootstrap`, `rust-hosted`.

---

## 3. Rust Symbol Analysis — Main Binary

Measured on `bin/release/x86_64-unknown-linux-gnu/simple` (28 MB, unstripped, 2026-05-15):

| Category | Count | % of total |
|---|---|---|
| Total symbols | 77,150 | 100% |
| Rust-mangled (`_ZN...`) | 42,583 | 55.2% |
| Rust runtime intrinsics (`rust_eh_personality`, `rdl_alloc`, `rust_panic`, etc.) | 10 | <0.1% |
| Known Rust crate symbols (serde, tokio, anyhow, regex, aho_corasick, cranelift, hashbrown) | 10,063 | 13.0% |

Sample Rust runtime intrinsics present:
- `_RNvCskdKJRKLKjqM_7___rustc10rust_panic`
- `_RNvCskdKJRKLKjqM_7___rustc11___rdl_alloc`
- `_RNvCskdKJRKLKjqM_7___rustc17rust_begin_unwind`
- `_RNvCskdKJRKLKjqM_7___rustc18___rdl_alloc_zeroed`
- `DW.ref.rust_eh_personality`

MCP server (`simple_mcp_server`, 5.2 MB): 5,944 total symbols, 1,286 Rust-mangled, 7 Rust runtime intrinsics.

**The main compiler binary is deeply Rust-linked.** 55% of symbols are Rust-mangled; Rust crate dependencies (serde, anyhow, aho_corasick, chrono, etc.) are present in `libsimple_native_all.a`.

---

## 4. Runtime Source File Distribution

Location: `src/runtime/` (excluding `hosted/target/` build artifacts and `vendor/`)

| Type | Count | Key files |
|---|---|---|
| C source (`.c`) | 29 owned | `runtime.c`, `runtime_native.c`, `runtime_audio.c`, `runtime_font.c`, `runtime_fork.c`, `runtime_image.c`, `runtime_process.c`, `runtime_sdl2.c`, `runtime_thread.c`, `async_driver.c`, platform async drivers, startup CRTs |
| Rust source (`.rs`) | 7 owned | `hosted/lib.rs`, `hosted/cocoa.rs`, `hosted/select.rs`, `hosted/webgpu.rs`, `hosted/win32.rs`, `hosted/js_test262.rs`, `runtime_memtrack_rust.rs` |
| Headers (`.h`) | 39 | `runtime.h`, `runtime_fork.h`, `platform/platform.h`, `stb_*`, `torch_ffi.h`, etc. |

The C side already dominates the `src/runtime/` directory. All 7 Rust files in runtime are under `hosted/` (compositor bindings for Cocoa/Win32/WebGPU/QuickJS) plus `runtime_memtrack_rust.rs`. The core C runtime (`runtime.c`, `runtime_native.c`) is already C.

---

## 5. Existing Executable-Size Tests — Rust Symbol Detection Gap

**Finding: No existing test today gates on Rust symbol presence or Rust archive linkage in core-lane outputs.**

- `test/system/exe_size_budget_spec.spl`: checks total stripped size ≤ 12 MB budget. Prints `nm` top symbols as diagnostic on failure, but does **not** assert absence of Rust symbols.
- `test/unit/compiler/linker/object_emitter_spec.spl`: checks `file_size > 0` for object files.
- `test/unit/app/build/.spipe_matchers_bootstrap_spec.spl`: has commented-out `binary_size` assertions (all lines start with `#`).
- `test/perf/port_algorithms/run_port_algorithm_benchmarks.shs`: uses `nm` and `readelf` for relocation analysis, not Rust-specific.

**Recommended Phase 1 action:** Add a core-lane Rust-symbol audit test that runs `nm <binary> | grep -c "_ZN\|rust_eh_personality\|rdl_alloc"` and asserts the count is below a defined threshold for `core-c-bootstrap` and `simple-core` outputs.

---

## 6. Plan Reference Corrections

### Wrong path in existing research doc

`doc/01_research/local/rust_runtime_minimization.md` line 57 references `doc/05_design/rust_to_simple_migration_plan.md` — that file does **not exist**. The actual files are:

- `doc/05_design/rust_to_simple_migration.md` — original migration categories (Category A/B/C)
- `doc/05_design/rust_to_simple_migration_v2_plan.md` — test-first migration plan (v2, 2026-01-30)

Both of these predate and are superseded in scope by the C-core ABI direction. See Section 7 below.

---

## 7. Lane Architecture — What Exists Today

From `doc/05_design/default_native_runtime_shift_to_c_core_abi.md` and `src/compiler_rust/driver/src/cli/native_build.rs`:

| Lane name | Archive | Status |
|---|---|---|
| `simple-core` | Pure-Simple archive (not yet built) | Not present — `auto` skips to next |
| `core-c-bootstrap` | `libsimple_runtime.a` (38 MB, Rust crate) | Present — default core lane |
| `rust-hosted` / `all` | `libsimple_native_all.a` (53 MB, all Rust deps) | Present — hosted/compositor features |

`libsimple_runtime.a` is a **Rust crate archive** (object files named `simple_runtime.simple_runtime.*.rcgu.o` plus `libloading` objects). Despite being called `core-c-bootstrap`, it is currently fully Rust-linked. The C files in `src/runtime/` are compiled separately and linked by the build system, but the `.a` archive itself is from the Rust `simple_runtime` crate.

**This is the central gap Phase 1 must address:** `libsimple_runtime.a` must be replaced with a C-core archive that exports the same ABI symbols without Rust runtime linkage.

---

## 8. Summary of Phase 0 Findings

| Item | Status |
|---|---|
| Binary sizes recorded (host compiler + archives + tooling) | Done |
| Per-lane smoke binary sizes (hello/fileio/TUI/net) | Not available — native-build no-ops in env; use `exe_size_budget_spec` baseline (9.6 MB, 2026-04-28) |
| Rust symbol count in main binary | 42,583 / 77,150 (55%) |
| Rust archive in `core-c-bootstrap` lane | Confirmed — `libsimple_runtime.a` is a Rust crate archive |
| `simple-core` lane present | No — not yet built |
| Existing tests detect Rust symbols in core-lane outputs | No — gap identified, no such assertion exists |
| Migration plan docs updated with supersession note | See `doc/05_design/rust_to_simple_migration_v2_plan.md` and `doc/05_design/rust_to_simple_migration.md` |
| `doc/01_research/local/rust_runtime_minimization.md` path error | Fixed — stale path reference corrected |
