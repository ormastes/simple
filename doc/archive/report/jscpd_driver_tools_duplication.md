# jscpd Duplication Report: Compiler Driver/Tools Layers

**Date:** 2026-03-14
**Tool:** jscpd (token-based copy/paste detection)
**Settings:** `--min-lines 5 --min-tokens 30 --formats-exts 'python:spl' -f python`

## Summary Table

| Layer | Files | Lines | Clones | Dup Lines | Dup % | Cross-File | Self |
|-------|-------|-------|--------|-----------|-------|------------|------|
| **80.driver** | 90 | 19,628 | 89 | 865 | 4.41% | 23 | 66 |
| **85.mdsoc** | 143 | 5,008 | 9 | 93 | 1.86% | 0 | 9 |
| **90.tools** | 179 | 31,532 | 100 | 823 | 2.61% | 43 | 57 |
| **95.interp** | 12 | 1,808 | 7 | 56 | 3.10% | 0 | 7 |
| **99.loader** | 23 | 6,790 | 23 | 233 | 3.43% | 16 | 7 |
| **TOTAL** | 447 | 64,766 | 228 | 2,070 | 3.20% | 82 | 146 |

## Top Duplicates by Size (per layer)

### 80.driver (4.41% - highest duplication)

| # | Type | Lines | File A | Range | File B | Range |
|---|------|-------|--------|-------|--------|-------|
| 1 | CROSS | 84 | build/main.spl | 101-184 | build/rust_subcommand.spl | 8-91 |
| 2 | CROSS | 37 | build/cli_entry_full.spl | 65-101 | build/main.spl | 296-332 |
| 3 | CROSS | 33 | build/cli_entry_full.spl | 139-171 | build/main.spl | 351-383 |
| 4 | SELF | 25 | shb/shb_reader.spl | 234-258 | shb/shb_reader.spl | 152-217 |
| 5 | SELF | 25 | build/test.spl | 170-194 | build/test.spl | 103-127 |
| 6 | SELF | 19 | shb/shb_extractor.spl | 399-417 | shb/shb_extractor.spl | 379-397 |
| 7 | SELF | 18 | build/test.spl | 134-151 | build/test.spl | 70-68 |
| 8 | CROSS | 15 | build/cli_entry_full.spl | 177-191 | build/main.spl | 388-402 |

**Key pattern:** `build/main.spl` vs `build/cli_entry_full.spl` share 3 large blocks (84+37+33 = 154 lines). `build/rust_subcommand.spl` is nearly entirely duplicated from `build/main.spl`.

### 85.mdsoc (1.86% - lowest duplication)

| # | Type | Lines | File A | Range | File B | Range |
|---|------|-------|--------|-------|--------|-------|
| 1 | SELF | 33 | config.spl | 259-291 | config.spl | 193-225 |
| 2 | SELF | 12 | config.spl | 304-315 | config.spl | 247-258 |
| 3 | SELF | 11 | config.spl | 294-304 | config.spl | 248-258 |
| 4 | SELF | 10 | layer_checker.spl | 552-561 | layer_checker.spl | 259-267 |

**Key pattern:** All self-duplicates. `config.spl` has repeated config-parsing blocks.

### 90.tools (2.61% - most clones at 100)

| # | Type | Lines | File A | Range | File B | Range |
|---|------|-------|--------|-------|--------|-------|
| 1 | SELF | 24 | ffi_gen/rust_codegen.spl | 208-231 | ffi_gen/rust_codegen.spl | 125-190 |
| 2 | CROSS | 19 | verify/compare_features.spl | 56-74 | verify/verify_features.spl | 297-315 |
| 3 | CROSS | 19 | verify/compare_features.spl | 107-125 | verify/verify_features.spl | 315+ |
| 4 | CROSS | 19 | ffi_gen/enum_gen.spl | 15-33 | ffi_gen/test_gen.spl | 33+ |
| 5 | CROSS | 17 | fix/rules/impl/lint_star_import.spl | 41-57 | fix/rules/impl/lint_stub.spl | 59-111 |
| 6 | SELF | 17 | fix/rules/impl/lint_annotation.spl | 113-129 | fix/rules/impl/lint_annotation.spl | 54-91 |
| 7 | SELF | 15 | fix/rules/impl/lint_module.spl | 77-91 | fix/rules/impl/lint_module.spl | 32-46 |

**Key patterns:**
- `verify/compare_features.spl` vs `verify/verify_features.spl` share feature-comparison logic
- `ffi_gen/` directory has repeated codegen patterns across `enum_gen`, `test_gen`, `rust_codegen`
- `fix/rules/impl/lint_*.spl` files share lint-rule boilerplate

### 95.interp (3.10%)

| # | Type | Lines | File A | Range | File B | Range |
|---|------|-------|--------|-------|--------|-------|
| 1 | SELF | 14 | mir_interpreter.spl | 257-270 | mir_interpreter.spl | 233-246 |
| 2 | SELF | 11 | mir_interpreter.spl | 722-732 | mir_interpreter.spl | 241-275 |
| 3 | SELF | 10 | mir_interpreter.spl | 709-718 | mir_interpreter.spl | 232-241 |
| 4 | SELF | 8 | interpreter/operators.spl | 49-56 | interpreter/operators.spl | 31-38 |

**Key pattern:** All self-duplicates in `mir_interpreter.spl` (repeated dispatch/evaluation blocks) and `operators.spl` (operator handling).

### 99.loader (3.43%)

| # | Type | Lines | File A | Range | File B | Range |
|---|------|-------|--------|-------|--------|-------|
| 1 | CROSS | 35 | smf_mmap_native.spl | 9-43 | loader/smf_mmap_native.spl | 14-48 |
| 2 | CROSS | 28 | smf_mmap_native.spl | 47-74 | loader/smf_mmap_native.spl | 57-84 |
| 3 | CROSS | 20 | jit_instantiator.spl | 15-34 | loader/jit_instantiator.spl | 41-60 |
| 4 | SELF | 14 | module_resolver/types.spl | 383-396 | module_resolver/types.spl | 325-338 |
| 5 | CROSS | 12 | smf_mmap_native.spl | 105-116 | loader/smf_mmap_native.spl | 166-177 |
| 6 | CROSS | 12 | module_loader.spl | 77-88 | loader/module_loader.spl | 73-84 |

**Key pattern:** Files in root `99.loader/` are nearly duplicated in `99.loader/loader/` subdirectory. `smf_mmap_native.spl` appears twice (63+ duplicated lines). `jit_instantiator.spl` also duplicated across both locations.

## Cross-File Duplication Patterns

1. **99.loader: Root vs `loader/` subdirectory** -- Most severe. `smf_mmap_native.spl`, `jit_instantiator.spl`, `module_loader.spl` exist in both `99.loader/` and `99.loader/loader/`. These appear to be copies that diverged slightly. **Recommendation:** Consolidate to single location.

2. **80.driver: `build/main.spl` vs `build/cli_entry_full.spl` vs `build/rust_subcommand.spl`** -- 84-line block shared between main.spl and rust_subcommand.spl; 70+ lines shared between cli_entry_full.spl and main.spl. **Recommendation:** Extract shared build-dispatch logic into a common module.

3. **90.tools: Lint rule boilerplate** -- `lint_star_import.spl`, `lint_stub.spl`, `lint_annotation.spl`, `lint_module.spl`, `lint_bool.spl`, `lint_wide_public.spl` share structural patterns. **Recommendation:** Create a lint-rule base template or trait.

4. **90.tools: FFI codegen templates** -- `enum_gen.spl`, `test_gen.spl`, `rust_codegen.spl`, `struct_gen.spl`, `lib_gen.spl` repeat codegen scaffolding. **Recommendation:** Extract shared codegen helpers.

5. **90.tools: Feature verification** -- `compare_features.spl` and `verify_features.spl` share feature-comparison blocks. **Recommendation:** Merge or extract shared comparison logic.
