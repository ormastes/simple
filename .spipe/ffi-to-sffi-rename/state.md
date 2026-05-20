# FFI → SFFI Full Rename — AUDIT INCOMPLETE

## Summary
Renamed all `ffi` references to `sffi` across the entire codebase.
State claim was COMPLETE but audit (2026-05-20) found 2 unsatisfied ACs.

## Acceptance Criteria — Audit Results

- [x] AC-1: Zero `use std.ffi.*` imports remain (all → `use std.sffi.*`)
  — VERIFIED: rg found 0 occurrences in src/lib, src/app, src/compiler

- [ ] AC-2: Zero files named `*ffi*` remain (all renamed to `*sffi*`); Rust `std::ffi` preserved
  — PARTIALLY SATISFIED: Two files remain with `_ffi` suffix that were not renamed:
    - `src/lib/nogc_sync_mut/io/tls_ffi.spl`
    - `src/lib/nogc_sync_mut/io/image_ffi.spl`
  — Note: `*_ffi.spl` suffix (meaning "FFI bindings for X") may be intentional naming
    distinct from the namespace rename. Needs clarification from orchestrator.

- [ ] AC-3: Zero identifiers/variables named `*ffi*` in source (→ `*sffi*`)
  — FAILED: Two confirmed violations:
    1. `src/compiler/70.backend/backend/interpreter_calls.spl`: imports
       `sffi_minimal as sffi` but call sites use `ffi.value_print()`,
       `ffi.value_int()`, etc. (20+ call sites using old `ffi.` alias).
       This is likely a runtime bug — the `ffi` name has no binding.
    2. `src/app/itf/adapter_minio.spl` lines 462, 528, 582: `var ffi: [text] = []`
       declares variable named `ffi`, then subsequent lines mutate `sffi` instead,
       and `rt_http_request` is passed `ffi` (the empty array). Broken rename —
       variable declaration missed but mutation lines were updated to `sffi`.
  — Also present but likely acceptable:
    - `@ffi(...)` annotation syntax in 107 comment lines (decorator syntax, not identifier)
    - `ffi-gen` CLI command name (string literal, not identifier)
    - `net/ffi.spl` references in doc comments (stale path references)
    - `var ffi` in adapter_minio passed to rt_http_request vs sffi mutations (bug above)

- [x] AC-4: Comments/docs updated
  — PARTIALLY: Doc directory has 913 `ffi` references vs sffi, but many are
    historical/intentional. The `@ffi` annotation comment refs and `net/ffi.spl`
    doc strings are stale but low-priority.

- [x] AC-5: Compiler guard rejects `std.ffi` with helpful error in both Rust seed and Simple interpreter
  — VERIFIED:
    - Rust seed: `src/compiler_rust/compiler/src/pipeline/module_loader.rs` has guard
    - Simple interpreter: `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` has guard

- [x] AC-6: Binary size identical (28,801,320 bytes before and after)
  — Not re-verified (binary exists at bin/simple)

- [x] AC-7: Rust workspace compiles clean (`cargo check --workspace` — 0 errors)
  — Not re-run; no `wffi` or `ffi_` Rust vars found outside std::ffi

- [x] AC-8: JIT/optimization plugins already updated via bulk rename
  — Not re-audited

- [x] AC-9: Binary executes (`bin/simple --version` → v0.9.8)
  — VERIFIED: `bin/simple --version` outputs `Simple Language v0.9.8`

## Commits
1. `be4` — refactor: rename all ffi → sffi (namespace, files, identifiers)
2. `76` — feat(compiler): add deprecation guard rejecting use std.ffi
3. `b6` — fix: resolve Rust compilation errors (std::ffi preserved, wffi→wsffi, variable refs)

## Phase
Phase 8 (ship) — BLOCKED pending AC-3 fixes

## Remaining Work

### Fix 1 (AC-3, HIGH — likely runtime bug):
`src/compiler/70.backend/backend/interpreter_calls.spl`
- Change all `ffi.value_*`, `ffi.file_*`, `ffi.env_*` call sites to use `sffi.` prefix
  (the import already aliases `sffi_minimal as sffi`, so just change `ffi.` → `sffi.`)

### Fix 2 (AC-3, HIGH — runtime bug):
`src/app/itf/adapter_minio.spl` lines 462, 528, 582
- Change `var ffi: [text] = []` → `var sffi: [text] = []`
  (the subsequent mutation lines already use `sffi`, only declaration and rt_http_request call use `ffi`)

### Clarification needed (AC-2):
- Are `tls_ffi.spl` and `image_ffi.spl` intentionally kept with `_ffi` suffix
  (as "FFI binding layer" naming) or should they be renamed to `tls_sffi.spl` / `image_sffi.spl`?
