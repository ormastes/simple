# Compiler Shared Module Extraction Plan

**Date:** 2026-02-17
**Status:** PLANNED
**Prerequisite:** `doc/report/duplication_status_full_2026-02-16.md` (Phase A)
**Previous Work:** `doc/report/semantic_deduplication_complete_2026-02-16.md` (Phases 1-4)

## Executive Summary

Extract **67 files (~15,000 lines)** of shared code from `src/compiler/` and `src/compiler_core_legacy/` into a new `src/compiler_shared/` module. Both compilers delegate to the shared module using import + re-export pattern (proven by existing `src/shared/llvm/`). Estimated **~11,780 lines of duplication eliminated**, reducing codebase duplication from 5.1% to ~3.2%.

## Background

### Bootstrap Chain
```
seed.cpp → compiler_core_legacy/ → compiler/ → production
```

- **compiler_core_legacy/** (441 files, 97K lines): Seed-compilable, desugared free functions, manual Option handling (`has_X: bool + X: type`)
- **compiler/** (436 files, 140K lines): Full-featured, `impl` blocks, modern Option (`type?`), lambdas, tuple destructuring
- **Shared filenames:** 398 files (90%), of which 98% differ

### Systematic Differences

The differences between compiler/ and compiler_core_legacy/ are mechanical desugaring transforms:

| Pattern | compiler/ (modern) | compiler_core_legacy/ (seed) |
|---------|-------------------|----------------------|
| Methods | `impl Struct: fn method()` | `fn struct_method(self: Struct)` |
| Options | `field: Type?` | `has_field: bool` + `field: Type` |
| Method calls | `obj.method(args)` | `method_fn(obj, args)` |
| Dict iteration | `for (k, v) in dict.items()` | `for _item in vars_items(dict)` |
| Lambdas | `.map(\x: x * 2)` | explicit `for` loop + `.push()` |
| Tuple destruct | `val (a, b) = pair` | `val _d = pair; val a = _d[0]` |
| Match | `"E1": "Semantic"` | `case "E1": "Semantic"` |

### Import Pattern (Proven)

`src/shared/llvm/` already demonstrates cross-compiler sharing:
```simple
# src/compiler_core_legacy/backend/llvm_backend.spl
use shared.llvm.tools (find_llc, find_opt, llc_available, opt_available)
```
No symlinks needed — resolves via `src/` directory structure.

## Analysis Results

### File Similarity Tiers (398 paired files)

| Tier | Files | Lines (core) | Description |
|------|-------|-------------|-------------|
| **IDENTICAL** (0% diff) | 13 | 286 | Byte-for-byte copies |
| **NEAR-IDENTICAL** (<15% diff) | 16 | 4,863 | Trivial differences |
| **MOSTLY-SAME** (15-30% diff) | 38 | 9,841 | Minor divergence |
| **DIVERGED** (>30% diff) | 331 | 79,827 | Significantly different |
| **Consolidatable Total** | **67** | **14,990** | |

### Shared Code Rules (seed-compatible subset)

All `compiler_shared/` code must compile through seed.cpp:
- Free functions only (no `impl`, no `static fn`, no `me`)
- No `type?` — use `has_X: bool` + `X: type`, or empty-string sentinel
- No `.map(\x: ...)` lambdas — use explicit `for` loops
- No `for (k, v) in dict.items()` — use seed-compatible iteration
- No tuple destructuring — use index access

---

## Batch 1: Identical Files (13 files, ~286 lines)

**Risk:** ZERO — files are byte-for-byte identical
**Strategy:** Move to `compiler_shared/`, replace originals with delegation imports

### Files

| Relative Path | Lines | Purpose |
|---------------|-------|---------|
| `backend/backend_ffi.spl` | 81 | FFI backend declarations |
| `blocks/builtin_blocks_defs.spl` | 31 | Block type definitions |
| `blocks/builtin.spl` | 17 | Built-in block registry |
| `error_explanations.spl` | 10 | Error explanation hub |
| `hir.spl` | 29 | HIR hub re-exports |
| `mir.spl` | 29 | MIR hub re-exports |
| `pattern_analysis.spl` | 12 | Pattern analysis hub |
| `semantics.spl` | 12 | Semantics hub |
| `type_system/__init__.spl` | 34 | Type system init |
| `test_build_native_min.spl` | 4 | Minimal native build test |
| `test_driver_only.spl` | 2 | Driver test stub |
| `test_enum_access.spl` | 9 | Enum access test |
| `test_pkg/child.spl` | 16 | Package child test |

### Delegation Pattern (Batch 1)

```simple
# src/compiler_shared/error_explanations.spl (canonical copy)
<original file content unchanged>

# src/compiler/error_explanations.spl (delegation wrapper)
use compiler_shared.error_explanations.{all_exported_symbols}
export all_exported_symbols

# src/compiler_core_legacy/error_explanations.spl (delegation wrapper)
use compiler_shared.error_explanations.{all_exported_symbols}
export all_exported_symbols
```

### Steps

1. Create `src/compiler_shared/` directory structure
2. Create `src/compiler_shared/mod.spl` (re-export hub, following `shared/llvm/mod.spl` pattern)
3. For each of the 13 files:
   a. Read the identical file to identify all exports
   b. Copy to `src/compiler_shared/<same-relative-path>.spl`
   c. Replace `src/compiler/<path>.spl` with import+re-export delegation
   d. Replace `src/compiler_core_legacy/<path>.spl` with import+re-export delegation
4. Run `bin/release/simple test` — verify all tests pass

---

## Batch 2: Near-Identical Files (16 files, ~4,863 lines)

**Risk:** LOW — differences are <15%, all mechanical
**Strategy:** Use `compiler_core_legacy/` version as shared base (already seed-compatible), thin wrappers in both compilers

### Files

| Relative Path | Lines | Diff% | Key Difference |
|---------------|-------|-------|----------------|
| `error_codes.spl` | 243 | 4% | `code[0:2]` vs `.substring(0,2)`, `case` keyword |
| `visibility.spl` | 97 | 2% | `part_len(part)` vs `part.len()` |
| `blocks.spl` | 26 | 7% | trivial |
| `hir_lowering.spl` | 29 | 6% | trivial |
| `blocks/mod.spl` | 281 | 5% | re-export hub differences |
| `type_infer.spl` | 117 | 8% | trivial desugaring |
| `test_bootstrap.spl` | 112 | 8% | trivial |
| `irdsl/codegen.spl` | 134 | 8% | `impl` → free function |
| `desugar/state_enum.spl` | 316 | 8% | `impl` → free function |
| `backend/capability_tracker.spl` | 140 | 13% | `impl` → free function |
| `backend/native/encode_riscv32.spl` | 696 | 8% | `impl` → free function |
| `backend/native/encode_riscv64.spl` | 553 | 10% | `impl` → free function |
| `backend/vulkan/spirv_builder.spl` | 608 | 9% | `impl` → free function |
| `loader/smf_mmap_native.spl` | 359 | 12% | `impl` → free function |
| `mir_json.spl` | 549 | 9% | `impl` → free function |
| `mir_serialization.spl` | 603 | 9% | `impl` → free function |

### Delegation Pattern (Batch 2)

For files where compiler/ has `impl` blocks that compiler_core_legacy/ desugars to free functions:

```simple
# src/compiler_shared/mir_json.spl (seed-compatible base from compiler_core_legacy/)
# All functions as free functions, no impl blocks
fn mirjson_serialize(self: MirJson, ...) -> text:
    ...
fn mirjson_serialize_block(self: MirJson, ...) -> text:
    ...
export mirjson_serialize, mirjson_serialize_block, ...

# src/compiler/mir_json.spl (thin wrapper adding impl blocks)
use compiler_shared.mir_json.{mirjson_serialize, mirjson_serialize_block, ...}
impl MirJson:
    fn serialize(...) -> text:
        mirjson_serialize(self, ...)  # delegation
    fn serialize_block(...) -> text:
        mirjson_serialize_block(self, ...)
export MirJson

# src/compiler_core_legacy/mir_json.spl (direct re-export)
use compiler_shared.mir_json.{mirjson_serialize, mirjson_serialize_block, ...}
export mirjson_serialize, mirjson_serialize_block, ...
```

### Steps

1. For each of the 16 files:
   a. Diff both versions to confirm <15% mechanical differences
   b. Take `compiler_core_legacy/` version as shared base (already free functions)
   c. Fix any seed-incompatible patterns (verify no `type?`, no lambdas)
   d. Move to `src/compiler_shared/<path>.spl`
   e. Create compiler/ wrapper with `impl` delegation (where applicable)
   f. Create compiler_core_legacy/ wrapper as re-export
2. Run `bin/release/simple test` after each sub-batch (4 files at a time)

---

## Batch 3: Mostly-Same Files (38 files, ~9,841 lines)

**Risk:** MEDIUM — 15-30% differences require splitting shared core from extensions
**Strategy:** Extract the shared 70-85% into `compiler_shared/`, each compiler keeps only its unique extensions

### Large Files (>400 lines)

| Relative Path | Lines | Diff% | Shared (est.) |
|---------------|-------|-------|---------------|
| `backend/native/elf_writer.spl` | 849 | 16% | ~713 lines |
| `backend/native/mach_inst.spl` | 611 | 26% | ~452 lines |
| `backend/native/encode_x86_64.spl` | 611 | 19% | ~495 lines |
| `backend/native/regalloc.spl` | 549 | 26% | ~406 lines |
| `backend/native/encode_aarch64.spl` | 540 | 21% | ~427 lines |
| `desugar/poll_generator.spl` | 592 | 30% | ~414 lines |
| `blocks/testing.spl` | 489 | 18% | ~401 lines |
| `backend/exhaustiveness_validator.spl` | 454 | 19% | ~368 lines |
| `linker/linker_wrapper_lib_support.spl` | 437 | 25% | ~328 lines |
| `desugar_async.spl` | 432 | 20% | ~346 lines |

### Smaller Files (<400 lines) — 28 additional files

These include:
- `blocks/definition.spl` (355L, 18%)
- `blocks/easy.spl` (290L, 18%)
- `monomorphize/tracker.spl` (299L, 24%)
- `blocks/error_helpers.spl` (92L, 16%)
- `blocks/text_transforms.spl` (101L, 18%)
- Plus 23 more files across backend/, linker/, dependency/, etc.

### Delegation Pattern (Batch 3)

For files with 15-30% diff, extract the shared core functions:

```simple
# src/compiler_shared/backend/native/elf_writer.spl
# Contains the ~85% shared ELF writing logic as free functions
fn elf_write_header(bits: i64, endian: i64) -> [i64]:
    ...
fn elf_write_section(name: text, data: [i64], flags: i64) -> [i64]:
    ...
export elf_write_header, elf_write_section, ...

# src/compiler/backend/native/elf_writer.spl
# Imports shared core + adds compiler-specific methods
use compiler_shared.backend.native.elf_writer.{elf_write_header, elf_write_section, ...}
impl ElfWriter:
    fn write_header() -> [u8]:
        elf_write_header(self.bits, self.endian)  # delegation
    fn write_debug_info(...):  # compiler-only extension
        ...

# src/compiler_core_legacy/backend/native/elf_writer.spl
# Imports shared + keeps any core-specific extensions
use compiler_shared.backend.native.elf_writer.{elf_write_header, elf_write_section, ...}
fn elfwriter_write_header(self: ElfWriter) -> [i64]:
    elf_write_header(self.bits, self.endian)  # delegation
```

### Steps

1. For each of the 38 files:
   a. Diff both versions to identify shared vs diverged sections
   b. Extract shared functions into `compiler_shared/` (seed-compatible free functions)
   c. compiler/ keeps `impl` wrappers delegating to shared + its unique extensions
   d. compiler_core_legacy/ keeps free-function wrappers delegating to shared + its unique extensions
2. Run tests after each file group (native backend: 7 files, blocks: 5 files, etc.)

---

## Directory Structure

```
src/compiler_shared/
    mod.spl                              # Re-export hub
    error_codes.spl                      # B2: Error code constants + helpers
    error_explanations.spl               # B1: Error explanation hub
    visibility.spl                       # B2: Path-based visibility
    hir.spl                              # B1: HIR hub
    mir.spl                              # B1: MIR hub
    mir_json.spl                         # B2: MIR JSON serialization
    mir_serialization.spl                # B2: MIR binary serialization
    type_infer.spl                       # B2: Type inference hub
    desugar_async.spl                    # B3: Async desugaring
    pattern_analysis.spl                 # B1: Pattern analysis hub
    semantics.spl                        # B1: Semantics hub
    blocks/
        builtin.spl                      # B1: Built-in block registry
        builtin_blocks_defs.spl          # B1: Block definitions
        mod.spl                          # B2: Block utilities hub
        definition.spl                   # B3: Block definition
        easy.spl                         # B3: Easy API
        testing.spl                      # B3: Testing utilities
        error_helpers.spl                # B3: Error helpers
        text_transforms.spl              # B3: Text transforms
    backend/
        backend_ffi.spl                  # B1: FFI declarations
        capability_tracker.spl           # B2: Capability tracking
        exhaustiveness_validator.spl     # B3: Pattern exhaustiveness
        native/
            encode_riscv32.spl           # B2: RISC-V 32-bit encoding
            encode_riscv64.spl           # B2: RISC-V 64-bit encoding
            encode_x86_64.spl            # B3: x86-64 encoding
            encode_aarch64.spl           # B3: AArch64 encoding
            elf_writer.spl               # B3: ELF file writer
            mach_inst.spl                # B3: Machine instructions
            regalloc.spl                 # B3: Register allocation
        vulkan/
            spirv_builder.spl            # B2: SPIR-V builder
    desugar/
        state_enum.spl                   # B2: State enum desugaring
        poll_generator.spl               # B3: Poll generator
    irdsl/
        codegen.spl                      # B2: IR DSL codegen
    linker/
        linker_wrapper_lib_support.spl   # B3: Linker library support
    loader/
        smf_mmap_native.spl             # B2: SMF memory-mapped loader
    type_system/
        __init__.spl                     # B1: Type system init
    (+ remaining Batch 3 smaller files)
```

---

## Implementation Strategy

### Parallelism

Execute with multiple agents concurrently:
- **Agent 1:** Batch 1 (13 identical files) — trivial moves + delegation wrappers
- **Agent 2:** Batch 2 first half (8 files: error_codes through desugar/state_enum)
- **Agent 3:** Batch 2 second half (8 files: capability_tracker through mir_serialization)
- **Validation checkpoint:** Run full test suite
- **Agent 4:** Batch 3 native backend group (7 files)
- **Agent 5:** Batch 3 blocks + desugar group (8 files)
- **Agent 6:** Batch 3 linker + loader + remaining (23 files)

### Test Strategy

After each batch:
```bash
bin/release/simple test                    # Full suite (4067+ tests)
```

After each sub-batch (4-8 files):
```bash
bin/release/simple test test/unit/compiler/   # Compiler-specific tests
```

### Rollback Strategy

Each batch is independently verifiable. If a batch introduces failures:
1. Revert the batch (jj restore)
2. Investigate which specific file broke
3. Fix and retry

---

## Estimated Impact

| Batch | Files | Lines | Lines Saved | Risk |
|-------|-------|-------|-------------|------|
| 1. Identical | 13 | 286 | ~280 | Zero |
| 2. Near-identical | 16 | 4,863 | ~4,500 | Low |
| 3. Mostly-same | 38 | 9,841 | ~7,000 | Medium |
| **Total** | **67** | **14,990** | **~11,780** | |

### Duplication Metrics

| Metric | Before | After |
|--------|--------|-------|
| Intentional duplication | 31,700 lines | ~19,920 lines |
| Duplication rate | 5.1% | ~3.2% |
| compiler_core_legacy/ size | 97,057 lines | ~85,277 lines |
| compiler/ size | 140,315 lines | ~135,815 lines |
| compiler_shared/ size (new) | 0 lines | ~14,990 lines |

---

## Related Documents

- **Prerequisite analysis:** `doc/report/duplication_status_full_2026-02-16.md`
- **Previous dedup work:** `doc/report/semantic_deduplication_complete_2026-02-16.md`
- **Import pattern precedent:** `src/shared/llvm/mod.spl`
- **Delegation pattern:** `src/app/desugar/forwarding.spl` (alias-based forwarding sugar)
- **No-inheritance research:** `doc/research/no_inheritance_ergonomics_2026-02-16.md`
