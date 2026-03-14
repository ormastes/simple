# Compiler Duplicate Check - All Layers Report

**Date:** 2026-03-14
**Tool:** `src/compiler/90.tools/duplicate_check/run_check.spl` (min 5 lines)
**Method:** Line-based windowing with hash grouping

## Summary Table

| Region | Files | Dup Groups | Dup Lines | Status |
|--------|------:|----------:|---------:|--------|
| 00.common | 37 | 77 | 385 | OK |
| 10.frontend | 101 | - | - | CRASHED (bug in checker) |
| 15.blocks | 26 | 379 | 1,895 | OK |
| 20.hir | 19 | 253 | 1,265 | OK |
| 25.traits | 9 | - | - | CRASHED (bug in checker) |
| 30.types | 56 | 878 | 4,390 | OK |
| 35.semantics | 45 | 1,063 | 5,315 | OK |
| 40.mono | 22 | 323 | 1,615 | OK |
| 50.mir | 17 | 260 | 1,300 | OK |
| 55.borrow | 10 | 116 | 580 | OK |
| 60.mir_opt | 23 | 483 | 2,415 | OK |
| 70.backend | 192 | - | - | CRASHED (bug in checker) |
| 80.driver | 90 | - | - | TIMEOUT + CRASHED |
| 85.mdsoc | 151 | 597 | 2,985 | OK |
| 90.tools | 180 | - | - | CRASHED (bug in checker) |
| 95.interp | 14 | 47 | 235 | OK |
| 99.loader | 23 | 323 | 1,615 | OK |
| **TOTAL (OK only)** | **443** | **4,799** | **23,995** | |

## Crash Note

The duplicate checker binary was rebuilt mid-session, switching from a **line-based** checker
to a **token-based** checker with identifier normalization. The new token-based version crashes
with `error: semantic: array index out of bounds: index is 0 but length is 0` on ALL directories.
Results above were captured before the binary change. Five layers (10.frontend, 25.traits,
70.backend, 80.driver, 90.tools) could not be scanned.

Root cause: likely the `substring()` destructive mutation bug (documented in `memory/language_substring_mutation.md`)
triggered in the tokenizer's `source.substring(pos, id_end)` calls in `run_check.spl` lines 151, 198, 216, 232.

## Top 3 Largest Duplicate Concentrations per Region

### 00.common (37 files, 77 groups, 385 lines)
1. `di_config.spl:99-103` / `di_config.spl:125-129` / `di_config.spl:168-172` -- DiServiceConfig flush logic (3-way dup)
2. `config.spl:100-104` / `config.spl:186-190` -- log level case statements
3. `di.spl:105-109` / `di.spl:138-142` -- binding registration

### 15.blocks (26 files, 379 groups, 1,895 lines)
1. `builtin_blocks_data.spl` / `builtin_blocks_shell.spl` -- `lexer_mode() -> LexerMode.Raw` (6-way combinatorial dup across lines 43, 209, 358, 41, 169)
2. `testing.spl:429-433` / `testing.spl:439-443` -- array length comparison
3. `builder.spl:49-53` / `builder.spl:451-455` -- completer/hover field declarations

### 20.hir (19 files, 253 groups, 1,265 lines)
1. `hir_lowering/items.spl:57-61` / `hir_lowering/items.spl:742-746` -- trait lowering loop
2. Comment/export section headers (combinatorial duplicates across many files)
3. Various HIR definition lowering patterns

### 30.types (56 files, 878 groups, 4,390 lines) -- HIGHEST COUNT
1. `macro_def.spl:31` / `higher_rank_poly_types.spl:125` / `variance_types.spl:297` / `associated_types_defs.spl:30` -- `HirType impl to_string()` (4-way)
2. `macro_checker.spl:238-247` / `macro_checker.spl:269-278` / `macro_checker.spl:299-308` / `macro_checker.spl:330-334` -- MacroParam test setup (4-way)
3. `type_system/bidirectional.spl:475-479` / `bidirectional.spl:496-500` -- type annotation inference

### 35.semantics (45 files, 1,063 groups, 5,315 lines) -- MOST GROUPS
1. `lint/` directory: combinatorial explosion of identical `warnings` + export section patterns across `duplicate_typed_args.spl`, `argument_count.spl`, `collection_patterns.spl`, `closure_capture.spl`
2. `resolve.spl:125-139` / `resolve.spl:135-162` -- MethodResolver construction (3-way)
3. `macro_contracts.spl:118-122` / `macro_contracts.spl:147-151` -- MacroContractResult construction

### 40.mono (22 files, 323 groups, 1,615 lines)
1. `monomorphize/metadata.spl:102` / `:129` / `:156` / `:183` -- `specialization_count()` (4-way)
2. `monomorphize/hot_reload.spl:210-214` / `:230-234` -- metadata loading pattern
3. `monomorphize/table.spl:293` / `cycle_detector.spl:395` / `hot_reload.spl:534` -- Robustness Checklist comment block

### 50.mir (17 files, 260 groups, 1,300 lines)
1. `mir_instructions.spl:88-98` -- SIMD instruction enum variants (sliding window overlap, 6+ matches)
2. `mir_json.spl:227` / `:294` / `:342` / `:357` -- serialize_operand arg building (4-way)
3. `mir_bitfield.spl:140-144` / `:158-162` -- field lookup pattern

### 55.borrow (10 files, 116 groups, 580 lines)
1. `borrow_check/borrow_graph.spl:205-209` / `:231-235` / `:216-220` / `:243-247` -- borrow creation with kind/lifetime/point
2. `gc_analysis/escape.spl:59-63` / `gc_analysis/roots.spl:156-160` -- Points-To Set headers
3. `borrow_check/lifetime.spl:68-72` / `:93-97` -- Region construction

### 60.mir_opt (23 files, 483 groups, 2,415 lines)
1. `optimization_passes.spl:466-472` / `:482-488` -- BinOp shift replacement (sliding overlap)
2. `optimization_passes.spl:378-382` / `:386-390` / `:397-401` -- zero elimination patterns (3-way)
3. `mir_opt/cse.spl:259-263` / `:278-282` / `:270-274` / `:289-293` -- CSE expr_table patterns

### 85.mdsoc (151 files, 597 groups, 2,985 lines)
1. `feature/*/\__init__.spl:4-8` -- dimension/layer comment headers (massive combinatorial: hir_lowering, monomorphization, optimization, type_checking, linking, mir_lowering = C(6,2)=15 pairs)
2. `config.spl:197-201` / `:263-267` -- derive_target_key pattern
3. Various transform/adapter boilerplate

### 95.interp (14 files, 47 groups, 235 lines)
1. `mir_interpreter.spl:235-239` / `:259-263` / `:712-716` -- function table lookup (3-way)
2. `execution/mod.spl:107` / `interpreter/llvm/target.spl:179` / `interpreter/llvm/tools.spl:163` -- Exports header
3. `mir_interpreter.spl:239-243` / `:263-267` -- call_result handling

### 99.loader (23 files, 323 groups, 1,615 lines)
1. `loader/jit_instantiator.spl:518` / `:531` / `:544` / `module_loader_lib_support.spl:206` -- SmfReaderMemory.from_data pattern (4-way)
2. `loader/module_loader.spl:100-104` / `module_loader.spl:217-221` -- ModuleLoaderConfig default
3. Various module resolution patterns

## Key Observations

1. **Highest duplication density:** 35.semantics (5,315 dup lines / 45 files = 118 lines/file) and 30.types (4,390 / 56 = 78 lines/file)
2. **Many duplicates are structural:** Export section headers (`# ====... Exports ...====`) create combinatorial explosion (N files with same header = C(N,2) pairs)
3. **Test setup duplication:** Layers with inline tests (30.types, 25.traits, 40.mono) have repeated `HirType`, `ImplBlock`, `TraitRef` construction
4. **Real refactoring targets:** `lint/` modules in 35.semantics, `HirType.to_string()` in 30.types, `SmfReaderMemory.from_data()` error handling in 99.loader, SIMD enum patterns in 50.mir
5. **Checker bug:** The token-based duplicate checker has a crash bug -- needs fix before 10.frontend, 70.backend, 80.driver, 90.tools can be scanned
