# Compiler Family Enforcement

## Status: CLOSED — 2026-05-20

## Phase: 8-ship
## Type: feature
## Status: complete

## Goal
Promote runtime-family GC boundary crossing from warnings to hard errors (Deny-level lint), add symmetric `@gc imports @no_gc` violation detection, and support attribute-based family detection (`@no_gc`/`@gc` on files/modules outside standard `nogc_*`/`gc_*` paths).

## Acceptance Criteria
- AC1: `GcBoundaryCrossing` lint default level is `Deny` (hard error), not `Warn`
- AC2: `@no_gc` modules cannot import `@gc` modules — emits hard error
- AC3: `@gc` modules cannot import `@no_gc` modules — emits hard error (new `gc_imports_nogc_family` violation reason)
- AC4: `noalloc` modules cannot import allocating or gc families — emits hard error
- AC5: Attribute-based detection: modules with `@no_gc`/`@gc` attribute (outside standard `nogc_*`/`gc_*` paths) are correctly classified
- AC6: Simple-side `gc_boundary_check.spl` has parity with Rust-side changes
- AC7: Existing Rust tests updated; `cargo check` passes

## Architecture
- Promote `GcBoundaryCrossing.default_level()` from `Warn` to `Deny` in `src/compiler_rust/compiler/src/lint/mod.rs`
- Add `gc_imports_nogc_family` violation branch in Rust `checker_resources.rs` and Simple `gc_boundary_check.spl`
- In Rust `check_gc_boundary_imports`, fall back to reading `@no_gc`/`@gc` from file-level attributes when path-based detection returns `None`
- Update Rust tests that assert `default_level() == LintLevel::Warn`

## Files Modified
- `src/compiler_rust/compiler/src/lint/mod.rs` — default level Warn -> Deny
- `src/compiler_rust/compiler/src/lint/checker_resources.rs` — attribute fallback + gc_imports_nogc
- `src/compiler/35.semantics/gc_boundary_check.spl` — Simple-side parity
