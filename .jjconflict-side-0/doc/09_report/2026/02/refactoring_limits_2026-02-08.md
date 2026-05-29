# Refactoring Limits - Files That Cannot Be Split Further

**Date:** 2026-02-08
**Context:** Large file refactoring effort (30 files >800 lines)

## Summary

Out of 30 files targeted for refactoring, **15 were successfully split** across Phases 1-4. The remaining **9 large files cannot be split** due to fundamental limitations of the Simple runtime's module system.

**Do not attempt to split these files further.** The reasons are documented below.

## Files That CANNOT Be Split

### Monolithic `impl` Blocks (7 files)

The Simple runtime does not support splitting a single `impl` block across multiple files. All methods in an `impl` block share `self` and must reside in the same file.

| File | Lines | Block |
|------|-------|-------|
| `src/compiler/parser.spl` | 2,303 | `impl Parser:` (line 13-2272) |
| `src/compiler/treesitter/outline.spl` | 1,786 | `impl TreeSitter:` (line 33-1760) |
| `src/compiler/type_infer/inference.spl` | 1,434 | `impl HmInferContext:` (line 23+) |
| `src/compiler/lexer.spl` | 1,377 | `impl Lexer:` (line 42+) |
| `src/compiler/mir_lowering.spl` | 1,033 | `impl MirLowering:` (line 32+) |
| `src/compiler/backend/interpreter.spl` | 826 | `impl InterpreterBackendImpl:` (lines 20, 269) |
| `src/compiler/type_system/stmt_check.spl` | 582 | Single impl with shared context |

**Why:** Each file contains a single struct/class with one large `impl` block. All methods use `self` to access shared mutable state. The runtime parser requires all methods of an impl to be in the same file. Extracting methods into separate files would require either:
1. Cross-file `impl` blocks (not supported)
2. Passing `self` as a parameter to free functions (changes all signatures, breaks API)
3. Duplicating state across files (creates inconsistency)

### Mutual Recursion (1 file)

| File | Lines | Issue |
|------|-------|-------|
| `src/compiler/type_system/expr_infer.spl` | 879 | All functions call each other |

**Why:** The main function `infer_expr` dispatches to helpers (`infer_binary`, `infer_unary`, `infer_call`, etc.), and every helper calls `infer_expr` back recursively. Splitting into separate files creates circular import dependencies, which the Simple module system does not resolve.

### Under Threshold (2 files)

| File | Lines | Note |
|------|-------|------|
| `src/compiler/blocks/builder.spl` | 570 | Below 800-line threshold |
| `src/compiler/type_system/stmt_check.spl` | 582 | Below 800-line threshold |

## Files Successfully Split

### Phase 1: Test Files
- `lib/database/test_extended.spl` (1,226 → split)
- `app/parser/modules.spl` (614 → split)

### Phase 2: Standard Library
- `std/spec.spl`, `std/async.spl`, `std/async_host.spl` (assessed, 2 cannot split)
- `app/interpreter/persistent_dict.spl`, `app/interpreter/file_io.spl` (split)
- `app/fix/rules/impl.spl`, `app/lsp/main.spl` (split)

### Phase 3: Application Tools
- `app/cli/dispatch.spl` → `types.spl` + `table.spl`
- `app/io/mod.spl` → `math.spl` + `jit.spl` + `thread.spl`
- `app/ffi_gen/specs/cranelift_core.spl` → `cranelift_codegen.spl` + `cranelift_ops.spl` + `cranelift_advanced.spl`

### Phase 4: Compiler Core
- `compiler/blocks/builtin_blocks_defs.spl` (851 → 31) → `builtin_blocks_math.spl` + `builtin_blocks_shell.spl` + `builtin_blocks_data.spl`
- `compiler/backend/llvm_backend.spl` (946 → 281) → `llvm_target.spl` + `llvm_ir_builder.spl`
- `compiler/backend/backend_api.spl` (781 → 222) → `backend_types.spl` + `backend_helpers.spl`

## What Makes a File Splittable

A file CAN be split when it contains:
- Multiple independent `struct`/`enum` definitions with separate `impl` blocks
- Standalone `fn` functions that don't form circular call graphs
- Logically separate sections that don't share mutable state

A file CANNOT be split when it contains:
- A single large `impl` block (all methods need `self`)
- Mutually recursive functions (circular imports)
- Tightly coupled state shared across all methods

## Future Considerations

If the Simple runtime adds support for:
- **Partial `impl` blocks** (like Rust's `impl` in multiple files) → parser.spl, lexer.spl, outline.spl could be split
- **Circular import resolution** → expr_infer.spl could be split
- **Extension methods** (adding methods to types from other modules) → all monolithic impls could be split

Until then, these files should remain as-is.
