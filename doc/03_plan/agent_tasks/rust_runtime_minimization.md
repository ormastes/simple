# Rust Runtime Minimization Plan

Date: 2026-05-04

## Goal

Minimize Simple generated executable size by making the default runtime path pure Simple plus small C-core ABI shims. Rust is opt-in only when the selected requirement names a Rust library or an existing Rust backend dependency.

## Assumed Requirement Path

This plan assumes feature Option A and NFR Option 1 from:

- `doc/02_requirements/feature/rust_runtime_minimization_options.md`
- `doc/02_requirements/nfr/rust_runtime_minimization_options.md`

Final requirements must not be written until the user selects options.

## Phase 0 - Baseline And Conflict Cleanup

1. Record current hello, file I/O, TUI smoke, and network smoke binary sizes for `core-c-bootstrap`, `simple-core` when present, and `rust-hosted`.
2. Add a documentation note that `doc/05_design/rust_to_simple_migration_plan.md` is superseded where it says the core runtime must remain Rust.
3. Confirm existing executable-size tests identify Rust symbols or Rust archives in core-lane outputs.

Exit evidence:

- Size baseline in `doc/01_research/local/rust_runtime_minimization.md` or a follow-up dated report.
- Updated docs point to the C-core ABI plan.

## Phase 1 - File I/O Core

1. Freeze C-core ABI names for open/read/write/append/exists/delete/dir-list/mkdir/cwd/env/time.
2. Implement missing symbols in `src/runtime/runtime_native.c` and headers.
3. Add Simple wrappers in the relevant stdlib family, keeping path normalization and error mapping in Simple.
4. Add core-lane tests for read, write, append, missing file, directory creation, cwd, env, and timestamp.

Exit evidence:

- Core-lane file smoke links without Rust runtime archives.
- Size delta from hello is within the selected NFR target.

## Phase 2 - Terminal/TUI Core

1. Freeze terminal ABI for raw/canonical mode, size query, stdin byte read, stdout raw write, flush, color capability probe, and restore-on-exit.
2. Keep widget layout, rendering diff, escape sequence composition, and input event mapping in Simple.
3. Gate optional SDL/font/image/audio runtime dependencies so text-only TUI does not pull them.
4. Add TUI smoke that draws, reads one key path where possible, restores terminal mode, and audits closure size.

Exit evidence:

- Text TUI smoke links on the core lane.
- No hosted compositor Rust crate is linked unless a GUI/compositor feature is selected.

## Phase 3 - Network Core

1. Freeze socket ABI for TCP connect/listen/accept/read/write/close and UDP send/receive.
2. Implement POSIX sockets and Windows Winsock shims behind platform files.
3. Keep DNS policy, URL parsing, HTTP/1 framing, WebSocket framing, and MCP/LSP protocol code in Simple where feasible.
4. Mark TLS, HTTP/2, QUIC, and advanced async reactors as provider-selected features, not default runtime requirements.

Exit evidence:

- TCP loopback smoke links and runs without Rust runtime archives.
- HTTP/1 client/server smoke uses Simple protocol code plus C sockets.

## Phase 4 - Hosted Boundary Reduction

1. Convert process execution from hosted-only to a minimal C process API if selected.
2. Keep async process/session control hosted-only until there is a selected process/session requirement.
3. Audit `src/runtime/hosted/` and Cargo feature defaults so Cocoa, Win32, and WebGPU crates are never pulled by text-mode or CLI binaries.
4. Add package smoke tests for MCP/LSP core-lane binaries if tool packaging is touched.

Exit evidence:

- Rust-hosted features are explicit in build output.
- Core-lane package smoke fails if a Rust archive appears unexpectedly.

## Verification Gates

- ABI symbol conformance for every core-required runtime symbol.
- Native build of hello, file I/O, TUI, and TCP loopback smoke fixtures.
- Size budget comparison against the Phase 0 baseline.
- Symbol/archive audit proving no Rust runtime linkage in core-lane outputs.
- Platform smoke for every platform file touched.

## Open Decisions

1. Should process execution be part of the first Rust-removal milestone, or remain hosted-only?
2. Should TLS be excluded from the default network target until a provider is selected?
3. Should Windows console support be required in the first TUI milestone, or compile-gated after Unix terminal support?

