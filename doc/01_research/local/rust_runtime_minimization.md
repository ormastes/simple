<!-- codex-research -->
# Rust Runtime Minimization - Local Research

Date: 2026-05-04

## Objective

Reduce generated executable size by moving default host/runtime dependencies away from Rust and toward pure Simple code, with C shims only where Simple would make binaries too large or where direct OS ABI access is required. Rust remains acceptable only when the requirement is explicitly a Rust library or Rust-owned toolchain integration.

## Existing Artifacts Reused

- `doc/01_research/local/executable_size_reduction.md` and `doc/01_research/domain/executable_size_reduction.md` already cover the binary-size motivation.
- `doc/04_architecture/executable_size_reduction.md` and `doc/05_design/executable_size_reduction.md` define the executable-size design surface.
- `doc/04_architecture/default_native_runtime_shift_to_c_core_abi.md`, `doc/05_design/default_native_runtime_shift_to_c_core_abi.md`, and `doc/03_plan/default_native_runtime_shift_phase2_plan.md` already shift the default native lane toward a C core ABI.
- `doc/03_plan/default_native_runtime_shift_mcp_lsp_dependency_inventory.md` inventories MCP/LSP runtime dependencies and separates startup-critical requirements from later hosted-only capabilities.
- `doc/05_design/rust_to_simple_migration_v2_plan.md` provides a test-first Rust-to-Simple migration model, but it still classifies some runtime and unsafe pieces as not pure-Simple portable.

## Current Runtime Shape

`src/runtime/` already contains substantial C runtime code:

- `runtime.c`, `runtime_native.c`, `runtime.h`, and platform headers under `src/runtime/platform/`.
- C implementations for SDL/image/font/audio/thread/fork/memtrack and async platform drivers.
- A Rust hosted-runtime crate under `src/runtime/hosted/` for hosted compositor bindings.
- Rust compiler/runtime crates under `src/compiler_rust/`, including `runtime`, `runtime_abi`, `native_loader`, and `native_all`.

The default-native shift plan records that core-C bootstrap archives now export core-required ABI symbols and that lane resolution only chooses `simple-core` when the archive exports the required symbol list. This aligns with the new objective.

## Dependency Findings

### File I/O

Current Simple apps and tools depend on `rt_file_read_text`, `rt_file_write_text`, `rt_file_exists`, `rt_dir_list`, `rt_mkdir_p`, `rt_env_get`, `rt_env_cwd`, and time helpers. These are natural C-core shims over OS APIs and should not require Rust.

### Network

The stdlib has `net`, `tcp`, `dns`, `http`, `http_client`, `http_server`, `websocket`, and broker modules. Protocol parsing and request/response logic should be pure Simple. Socket creation, connect/listen/accept, polling, TLS provider hooks, and DNS resolver calls should be thin C shims unless a selected requirement explicitly mandates a Rust network library.

### TUI / Terminal

TUI rendering, layout, widgets, and protocol text should be pure Simple. Terminal mode changes, screen-size detection, raw input, and platform console handles should be C shims. Existing docs mention TUI in the `simple-core` milestone, so this objective strengthens that path.

### Process / Async Sessions

MCP/LSP inventory currently classifies `rt_process_run`, async process spawn/kill/status, and TRACE32/dialog passthrough as hosted-only until a core process API exists. This is the main open boundary: a minimal C process API can be planned, but it should not block the first file/network/TUI reduction.

### Rust-Required Or Rust-Acceptable Boundaries

Rust remains justified for:

- The current Rust compiler backend and Rust crate workspace until those modules are individually ported.
- External Rust libraries selected as requirements, such as Rust-only downloaded crates or wrappers around Rust ecosystems.
- Unsafe or external-library integration where an existing Rust wrapper is materially smaller, safer, or already required by the chosen backend.

## Conflicts With Current Assumptions

`doc/05_design/rust_to_simple_migration_plan.md` says the core `runtime` should be kept in Rust. That conflicts with the current objective and with the newer C-core ABI work. Treat the newer C-core/default-native plan as the preferred direction.

`doc/05_design/rust_to_simple_migration_v2_plan.md` classifies runtime value representation, GC, native loader, SIMD, GPU APIs, and WASM runtime as not pure-Simple portable. This does not block the objective if those surfaces are either C-core shims, hosted-only, or explicit Rust-required dependencies.

The MCP/LSP inventory currently allows process execution and async sessions to remain hosted-only. If the user expects all tooling to run without Rust, that is a requirement expansion and should be selected explicitly.

## Local Recommendation

Plan a three-tier runtime split:

1. Pure Simple: protocol parsers, path/string handling, JSON/HTTP framing, TUI widgets, CLI behavior, diagnostics, and policy.
2. C-core shims: file descriptors/handles, sockets, terminal modes, env/cwd/time, stdout/stdin, process basics, memory/value ABI.
3. Rust-required hosted lanes: selected Rust libraries, compiler backend pieces, WebGPU/Cocoa/Win32 hosted compositor crates while they remain Rust-only.

