# Coupling proxy (import fan-out)

Generated: 2026-04-27
Method: count unique 'use ' statements per .spl file
Caveat: This is a proxy, not a real CBO/RFC. The refactor skill claims metrics that the tool does not implement.

## Top 30 high-fan-out files in src/compiler/

| Imports | File |
|--------:|------|
| 62 | `src/compiler/10.frontend/core/parser_expr.spl` |
| 60 | `src/compiler/10.frontend/core/parser_decls.spl` |
| 50 | `src/compiler/10.frontend/core/parser_stmts.spl` |
| 43 | `src/compiler/10.frontend/core/parser_primary.spl` |
| 40 | `src/compiler/80.driver/driver.spl` |
| 39 | `src/compiler/10.frontend/core/parser.spl` |
| 39 | `src/compiler/10.frontend/core/lexer.spl` |
| 26 | `src/compiler/30.types/associated_types.spl` |
| 24 | `src/compiler/10.frontend/core/lexer_scanners.spl` |
| 21 | `src/compiler/70.backend/linker/linker_wrapper.spl` |
| 20 | `src/compiler/30.types/variance.spl` |
| 20 | `src/compiler/30.types/higher_rank_poly.spl` |
| 20 | `src/compiler/10.frontend/core/lexer_struct.spl` |
| 18 | `src/compiler/80.driver/driver_types.spl` |
| 18 | `src/compiler/10.frontend/core/ast_clone.spl` |
| 17 | `src/compiler/99.loader/loader/module_loader.spl` |
| 17 | `src/compiler/80.driver/watcher/watcher_client.spl` |
| 17 | `src/compiler/70.backend/backend/llvm_backend.spl` |
| 17 | `src/compiler/70.backend/backend/compile_c_entry.spl` |
| 17 | `src/compiler/30.types/type_system/expr_infer_calls.spl` |
| 16 | `src/compiler/70.backend/build_native_pipeline.spl` |
| 16 | `src/compiler/70.backend/backend/native/mod.spl` |
| 15 | `src/compiler/80.driver/build/cli_entry_full.spl` |
| 15 | `src/compiler/70.backend/backend/codegen_factory.spl` |
| 15 | `src/compiler/60.mir_opt/mir_opt/mod.spl` |
| 14 | `src/compiler/90.tools/ffi_gen/specs/__init__.spl` |
| 14 | `src/compiler/90.tools/ffi_gen/main.spl` |
| 14 | `src/compiler/85.mdsoc/types.spl` |
| 14 | `src/compiler/80.driver/driver_aot_output.spl` |
| 14 | `src/compiler/80.driver/build/main.spl` |

## Distribution of imports/file (compiler subtree)

- Files measured: 1080
- Total imports: 2850
- Max imports in one file: 62
- p50: 1, p90: 6, p99: 20
- Files with ≥10 imports (fan-out concern): 54
