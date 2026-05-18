# FFI → SFFI Full Rename — COMPLETE

## Summary
Renamed all `ffi` references to `sffi` across the entire codebase.

## Acceptance Criteria — All Met
- AC-1: Zero `use std.ffi.*` imports remain (all → `use std.sffi.*`)
- AC-2: Zero files named `*ffi*` remain (all renamed to `*sffi*`); Rust `std::ffi` preserved
- AC-3: Zero identifiers/variables named `*ffi*` in source (→ `*sffi*`)
- AC-4: Comments/docs updated
- AC-5: Compiler guard rejects `std.ffi` with helpful error in both Rust seed and Simple interpreter
- AC-6: Binary size identical (28,801,320 bytes before and after)
- AC-7: Rust workspace compiles clean (`cargo check --workspace` — 0 errors)
- AC-8: JIT/optimization plugins already updated via bulk rename
- AC-9: Binary executes (`bin/simple --version` → v0.9.8)

## Commits
1. `be4` — refactor: rename all ffi → sffi (namespace, files, identifiers)
2. `76` — feat(compiler): add deprecation guard rejecting use std.ffi
3. `b6` — fix: resolve Rust compilation errors (std::ffi preserved, wffi→wsffi, variable refs)

## Phase
Phase 8 (ship) — pushed to origin/main
