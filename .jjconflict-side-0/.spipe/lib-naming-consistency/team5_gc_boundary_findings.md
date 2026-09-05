# Team 5: gc_boundary_crossing Fix — Findings

**Date:** 2026-05-20
**Scope:** `src/lib/gc_async_mut/` — gc_boundary lint errors on delegation re-exports

## Summary

Task premise is empirically wrong. No `gc_boundary` warnings fire on `src/lib/gc_async_mut/` files.
Zero changes to `src/lib/gc_async_mut/` are needed or appropriate.

---

## Empirical Verification

Running `bin/simple src/lib/gc_async_mut/io/buffer.spl` produces:

```
warning: Avoid 'export use *' - exposes unnecessary interfaces
  --> line 7:1
   |
  7 | export use std.nogc_async_mut.io.buffer.*
```

The warning is **W0407 (star_export wildcard)** from `src/compiler/35.semantics/lint/star_import.spl`,
NOT a `gc_boundary` warning. No `[gc-warning]` or `gc_boundary` output appears on any tested file.

---

## Rust Enforcement Analysis

**File:** `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`

The Rust `runtime_family_import_violation_reason` function (the actual runtime that emits warnings)
only flags **nogc→gc** direction (line 165):

```rust
if !importer_family.is_gc() && imported_family.is_gc() {
    return Some("nogc_imports_gc_family");
}
```

It does NOT flag gc→nogc. `gc_async_mut` importing from `nogc_async_mut` or `nogc_sync_mut`
produces no `[gc-warning]` output. This is intentional: gc families are allowed to delegate
to nogc backends.

---

## .spl Rule 3 / Doctest Contradiction (Compiler Bug — Out of Team 5 Scope)

**File:** `src/compiler/35.semantics/gc_boundary_check.spl`

- Line 164 doctest: `expect(check_gc_boundary_imports("gc_async_mut.task", ["nogc_sync_mut.fs"]).len()).to_equal(0)`
  — says gc→nogc returns 0 warnings.
- Lines 213–219 (Rule 3): pushes a warning for `gc_imports_nogc_family`.

These contradict each other. Rule 3 was added after the doctest without updating it.
`check_gc_boundary_imports` is not called from the active compiler pipeline — only re-exported
from `__init__.spl`. The rule is dead code in production. File as a compiler ticket; not Team 5
scope.

---

## Actual W0407 Issue (Not Team 5's Fix to Make)

**Count:** 238 files in `src/lib/gc_async_mut/` use `export use std.X.*` delegation.

W0407 fires on delegation files that contain a module-level docstring (`"""..."""`). The
`check_star_export` function in `star_import.spl` uses an `all_facade` heuristic (lines 91–110):
if every declaration is `DECL_USE` or `DECL_EXPORT`, it suppresses W0407. A docstring node
breaks this condition.

Files that trigger: those with `"""...docstring..."""` before their `export use` line.
Files that don't trigger: `__init__.spl`, `mod.spl` (exempted by filename in `_is_facade_file`),
and files with only `#` line comments.

**Correct fix (compiler change, outside Team 5):** Extend `_is_facade_file` or the `all_facade`
check in `src/compiler/35.semantics/lint/star_import.spl` to tolerate docstring nodes in
pure delegation files. Stripping docstrings from delegation files to game the heuristic is a
cover-up fix (forbidden per project rules).

---

## Recommendations

| Issue | Owner | Action |
|-------|-------|--------|
| gc_boundary fires on gc_async_mut | Team 5 | No action — does not fire |
| Rule 3 / doctest contradiction in gc_boundary_check.spl | Compiler team | File as compiler bug ticket |
| W0407 on gc_async_mut docstring delegation files | Compiler/lint team | Fix `all_facade` to tolerate docstring nodes in `star_import.spl` |

---

## Files Checked

- `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` — Rust gc_boundary enforcement
- `src/compiler/35.semantics/gc_boundary_check.spl` — .spl warning/hard-error functions
- `src/compiler/00.common/gc_boundary.spl` — lint name constant
- `src/compiler/35.semantics/lint/star_import.spl` — W0407 star_export lint
- `src/lib/gc_async_mut/io/buffer.spl` — sample delegation file (tested)
- `src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl` — sample delegation file (tested)
- `src/lib/gc_async_mut/gpu_runtime/mod.spl` — sample delegation file (tested)
