# Compiler Shared DI Check Design

**Date:** 2026-02-17
**Status:** IMPLEMENTED
**Relates to:** `doc/report/compiler_shared_extraction_plan_2026-02-17.md`

## Overview

The dependency injection (DI) check validates that the `compiler_shared` delegation pattern
is correctly wired across all three compiler modules:

```
src/compiler_shared/<path>.spl    ← canonical shared implementation
src/compiler/<path>.spl           ← thin delegation wrapper (uses impl blocks, modern syntax)
src/compiler_core_legacy/<path>.spl      ← thin delegation wrapper (free functions, seed-compatible)
```

The check ensures every migrated file has both wrappers, and each wrapper properly
imports from `compiler_shared` and re-exports the same symbols.

## Delegation Pattern

### Shared implementation (`compiler_shared/`)

Contains the canonical implementation as seed-compatible free functions:

```simple
# src/compiler_shared/blocks/error_helpers.spl
fn error_at(ctx: BlockContext, message: text, offset: i64, length: i64) -> BlockError:
    ...

fn error_span(ctx: BlockContext, message: text, span: _tv_0) -> BlockError:
    ...

fn errors_from_strings(ctx: BlockContext, messages: [text]) -> [BlockError]:
    ...

export error_at, error_span, errors_from_strings
```

### compiler/ wrapper (modern syntax)

```simple
# src/compiler/blocks/error_helpers.spl
use compiler_shared.blocks.error_helpers.{error_at, error_span, errors_from_strings}
export error_at, error_span, errors_from_strings
```

For Batch 2/3 files where `compiler/` uses `impl` blocks, the wrapper adds delegation:

```simple
# src/compiler/mir_json.spl
use compiler_shared.mir_json.{mirjson_serialize, mirjson_serialize_block}
impl MirJson:
    fn serialize() -> text:
        mirjson_serialize(self)   # delegation
export MirJson
```

### compiler_core_legacy/ wrapper (seed-compatible)

```simple
# src/compiler_core_legacy/blocks/error_helpers.spl
use compiler_shared.blocks.error_helpers.{error_at, error_span, errors_from_strings}
export error_at, error_span, errors_from_strings
```

## Validation Rules

A delegation wrapper is considered **valid** when it:

1. **Imports from compiler_shared**: contains `use compiler_shared.`
2. **Re-exports symbols**: contains `export`

These two rules are checked by the DI check spec.

## Test Spec

**Location:** `test/unit/compiler/compiler_shared_di_check_spec.spl`

The spec uses `rt_file_read_text` to read source files and validate their content.
Helper functions:

```simple
extern fn rt_file_read_text(path: text) -> text

fn _file_exists(path: text) -> bool:
    val content = rt_file_read_text(path) ?? ""
    content.len() > 0

fn _file_delegates(path: text) -> bool:
    val content = rt_file_read_text(path) ?? ""
    content.contains("use compiler_shared.")

fn _file_exports(path: text) -> bool:
    val content = rt_file_read_text(path) ?? ""
    content.contains("export")

fn _wrapper_ok(compiler_path: text) -> bool:
    val ok1 = _file_delegates(compiler_path)
    val ok2 = _file_exports(compiler_path)
    ok1 and ok2
```

The spec is organized into 9 describe groups:
- Batch 1 shared sources exist (9 tests)
- Batch 1 compiler/ wrappers (9 tests)
- Batch 1 compiler_core_legacy/ wrappers (9 tests)
- Batch 2 shared sources exist (15 tests)
- Batch 2 compiler/ wrappers (15 tests)
- Batch 2 compiler_core_legacy/ wrappers (15 tests)
- Batch 3 partial shared sources exist (4 tests)
- Batch 3 partial compiler/ wrappers (4 tests)
- Batch 3 partial compiler_core_legacy/ wrappers (4 tests)

**Total: 75 tests** covering 25 fully-migrated non-test files × 3 checks (shared + compiler/ + compiler_core_legacy/).
(9 Batch 1 + 8 Batch 2 + 4 Batch 3 = 21 files × 3 groups + 12 "exists" checks = 75 tests)

## Current Migration Status

### Batch 1: Identical Files (13 files, COMPLETE)

| File | compiler_shared | compiler/ | compiler_core_legacy/ |
|------|:-:|:-:|:-:|
| `backend/backend_ffi.spl` | ✅ | ✅ | ✅ |
| `blocks/builtin_blocks_defs.spl` | ✅ | ✅ | ✅ |
| `blocks/builtin.spl` | ✅ | ✅ | ✅ |
| `error_explanations.spl` | ✅ | ✅ | ✅ |
| `hir.spl` | ✅ | ✅ | ✅ |
| `mir.spl` | ✅ | ✅ | ✅ |
| `pattern_analysis.spl` | ✅ | ✅ | ✅ |
| `semantics.spl` | ✅ | ✅ | ✅ |
| `type_system/__init__.spl` | ✅ | ✅ | ✅ |
| `test_build_native_min.spl` | ✅ | (test) | (test) |
| `test_driver_only.spl` | ✅ | (test) | (test) |
| `test_enum_access.spl` | ✅ | (test) | (test) |
| `test_pkg/child.spl` | ✅ | (test) | (test) |

### Batch 2: Near-Identical Files (16 files, PARTIAL — 8/16 wrappers complete)

| File | compiler_shared | compiler/ | compiler_core_legacy/ |
|------|:-:|:-:|:-:|
| `error_codes.spl` | ✅ | ⏳ | ✅ |
| `visibility.spl` | ✅ | ⏳ | ⏳ |
| `blocks.spl` | ✅ | ⏳ | ⏳ |
| `hir_lowering.spl` | ✅ | ⏳ | ⏳ |
| `blocks/mod.spl` | ✅ | ⏳ | ⏳ |
| `type_infer.spl` | ✅ | ⏳ | ⏳ |
| `test_bootstrap.spl` | ✅ | (test) | (test) |
| `irdsl/codegen.spl` | ✅ | ⏳ | ⏳ |
| `desugar/state_enum.spl` | ✅ | ✅ | ✅ |
| `backend/capability_tracker.spl` | ✅ | ✅ | ✅ |
| `backend/native/encode_riscv32.spl` | ✅ | ✅ | ✅ |
| `backend/native/encode_riscv64.spl` | ✅ | ✅ | ✅ |
| `backend/vulkan/spirv_builder.spl` | ✅ | ✅ | ✅ |
| `loader/smf_mmap_native.spl` | ✅ | ✅ | ✅ |
| `mir_json.spl` | ✅ | ✅ | ✅ |
| `mir_serialization.spl` | ✅ | ✅ | ✅ |

### Batch 3: Mostly-Same Files (38 files, IN PROGRESS — 4/38 done)

| File | compiler_shared | compiler/ | compiler_core_legacy/ |
|------|:-:|:-:|:-:|
| `backend/native/encode_aarch64.spl` | ✅ | ✅ | ✅ |
| `blocks/error_helpers.spl` | ✅ | ✅ | ✅ |
| `blocks/text_transforms.spl` | ✅ | ✅ | ✅ |
| `desugar_async.spl` | ✅ | ✅ | ✅ |
| `backend/native/elf_writer.spl` | ⏳ | ⏳ | ⏳ |
| `backend/native/mach_inst.spl` | ⏳ | ⏳ | ⏳ |
| `backend/native/encode_x86_64.spl` | ⏳ | ⏳ | ⏳ |
| `backend/native/regalloc.spl` | ⏳ | ⏳ | ⏳ |
| `desugar/poll_generator.spl` | ⏳ | ⏳ | ⏳ |
| `blocks/testing.spl` | ⏳ | ⏳ | ⏳ |
| `backend/exhaustiveness_validator.spl` | ⏳ | ⏳ | ⏳ |
| `linker/linker_wrapper_lib_support.spl` | ⏳ | ⏳ | ⏳ |
| … (26 more files) | ⏳ | ⏳ | ⏳ |

## Adding New Tests

When a new Batch 3 file is migrated, add 3 tests to the spec (one per describe group):

```simple
# In "DI Check - Batch 3 shared sources exist":
it "backend/native/elf_writer.spl exists in compiler_shared":
    expect(_file_exists("src/compiler_shared/backend/native/elf_writer.spl")).to_equal(true)

# In "DI Check - Batch 3 compiler/ wrappers":
it "compiler/backend/native/elf_writer.spl delegates":
    expect(_wrapper_ok("src/compiler/backend/native/elf_writer.spl")).to_equal(true)

# In "DI Check - Batch 3 compiler_core_legacy/ wrappers":
it "compiler_core_legacy/backend/native/elf_writer.spl delegates":
    expect(_wrapper_ok("src/compiler_core_legacy/backend/native/elf_writer.spl")).to_equal(true)
```

## Running the Check

```bash
bin/simple test test/unit/compiler/compiler_shared_di_check_spec.spl
```

Run the full compiler test suite to catch regressions:

```bash
bin/simple test test/unit/compiler/
```

## Import Resolution Note

The `compiler_shared` module resolves via `src/` directory structure (same as `shared/llvm/`).
No symlinks are needed — the runtime resolves `use compiler_shared.x.{y}` by looking for
`src/compiler_shared/x.spl` relative to the project root.
