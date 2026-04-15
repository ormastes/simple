# Skipped Tests Analysis — Round 3

**Date:** 2026-03-10
**Total skip tags remaining:** 183 across 33 files
**Previous:** 240 skipped (pre-Round 3), 150 (post-Round 2 triage)

## Round 3 Changes

### Rust Compiler Fixes (binary rebuilt)
1. **Module-level var access** — `Pattern::Typed` handling in `evaluation_helpers.rs` + MODULE_GLOBALS sync for `.push()`/`.pop()` in `calls.rs`
2. **Trait dispatch on built-in types** — TRAIT_IMPLS/BLANKET_IMPL_METHODS fallback for `text`, `i64`, `f64`, `bool` in `interpreter_method/mod.rs` and `method_dispatch.rs`
3. **Interpreter FFI via dlopen** — New `dynamic_ffi.rs` for lazy loading runtime `.so`/`.dylib`/`.dll`, cross-platform

### Test Rewrites (self-contained, no compiler imports)
4. **AOP debug log** — `aop_debug_log_spec.spl` rewritten (16 tests)
5. **Module visibility** — `module_visibility_spec.spl` rewritten (26 tests)

### Skip Tags Removed
6. **CLI args** — 11 files, ~72 tests (cli: blocks already commented out)
7. **Pointer tests** — weak (5), unique (5), handle (9) = 19 tests
8. **Trait coherence** — 14 tests
9. **Macro hygiene** — 3 tests
10. **Parser functions** — 1 test

### Code Quality
11. GPU dimension extraction, pretty printer (15 node types), poll generator defaults

---

## Remaining 183 Skipped Tests by Category

### FFI — External Runtime Functions (55 tests, 8 files)
These require `extern fn rt_*()` symbols that are **not compiled into the binary**.

| File | Tests | Reason |
|------|-------|--------|
| `treesitter_parser_spec.spl` | 9 | `rt_ts_*` not in binary |
| `treesitter_cursor_spec.spl` | 8 | `rt_ts_*` not in binary |
| `treesitter_error_recovery_spec.spl` | 7 | `rt_ts_*` not in binary |
| `treesitter_lexer_spec.spl` | 7 | `rt_ts_*` not in binary |
| `treesitter_query_spec.spl` | 6 | `rt_ts_*` not in binary |
| `treesitter_tree_spec.spl` | 6 | `rt_ts_*` not in binary |
| `tensor_spec.spl` | 9 | `rt_tensor_*` not in binary |
| `tensor_bridge_spec.spl` | 2 | `rt_tensor_*` not in binary |
| `tensor_interface_spec.spl` | 1 | `rt_tensor_*` not in binary |

**To fix:** Compile TreeSitter/Tensor as shared library and link into runtime.

### FFI — Interpreter Dispatch (15 tests, 3 files)
| File | Tests | Reason |
|------|-------|--------|
| `rust_simple_ffi_spec.spl` | 9 | FFI not available in interpreter mode |
| `parser_type_annotations_spec.spl` | 6 | SIMD runtime functions |

### Codegen / Compiled-Mode Only (36 tests, 6 files)
| File | Tests | Reason |
|------|-------|--------|
| `implicit_mul_spec.spl` | 19 | `m{}` math block evaluator limitation |
| `generator_state_machine_codegen_spec.spl` | 8 | `gen` keyword not in interpreter |
| `trait_keyword_all_phases_spec.spl` | 6 | Compiler internal imports |
| `set_literal_spec.spl` | 1 | Set type not implemented |
| `loader_exec_memory_spec.spl` | 1 | Native exec memory |
| `jit_probe_spec.spl` | 1 | JIT only |

### Module/Closure/Interpreter Limitations (29 tests, 5 files)
| File | Tests | Reason |
|------|-------|--------|
| `index_spec.spl` | 11 | `function 'VersionEntry' not found` — multi-struct constructor (only 1st struct registered) |
| `experiment_tracking_spec.spl` | 6 | `unsupported path call ["ConfigValue", "Float"]` — enum variant construction via path |
| `hashset_basic_spec.spl` | 6 | `type mismatch: cannot convert string to int` — HashSet method dispatch |
| `implicit_context_spec.spl` | 6 | Closure mutation of module vars in `it` blocks |

### External Tools Required (17 tests, 2 files)
| File | Tests | Reason |
|------|-------|--------|
| `vulkan_spec.spl` | 9 | Requires Vulkan SDK |
| `vhdl_spec.spl` | 8 | Requires GHDL simulator |

### Baremetal / Cross-Compilation (17 tests, 2 files)
| File | Tests | Reason |
|------|-------|--------|
| `remote_riscv32_spec.spl` | 13 | QEMU + GDB + cross-compiler |
| `baremetal_full_spec.spl` | 4 | Cross-compilation toolchain |

### MCP Integration (8 tests, 2 files)
| File | Tests | Reason |
|------|-------|--------|
| `app_mcp_intensive_spec.spl` | 7 | Compiled mode server |
| `mcp_bugdb_spec.spl` | 1 | MCP bugdb integration |

### Other (3 tests, 3 files)
| File | Tests | Reason |
|------|-------|--------|
| `native_ops_dir_create_spec.spl` | 1 | Compiled mode |
| `bug_tracking_scenario_spec.spl` | 1 | Integration dependency |

### Performance (2 tests, 2 files)
| File | Tests | Reason |
|------|-------|--------|
| `cli_dispatch_perf_spec.spl` | 1 | Native binary subprocess |
| `llvm_lib_ffi_perf_spec.spl` | 1 | Native binary FFI perf |

### Isolated (2 tests, 2 files)
| File | Tests | Reason |
|------|-------|--------|
| `classes_spec.spl` | 1 | Specific class feature |
| `class_invariant_spec.spl` | 1 | Invariant checking |

---

## FFI Symbol Availability (investigated 2026-03-10)

| Symbol prefix | In binary? | In .so? | Resolvable via dlopen? |
|---------------|-----------|---------|----------------------|
| `rt_ts_*` (TreeSitter) | No | No `.so` exists | **No** — need to build `libspl_treesitter.so` |
| `rt_torch_*` (Tensor) | 3 stubs | 66 in `libsimple_runtime.so`, 202 in `libspl_torch.so` | **Yes** via `dynamic_ffi.rs` or `DynLoader` |
| `ts_parser_*` (raw C) | No | No | **No** — need `libtree-sitter.so` |

The `dynamic_ffi.rs` dlopen mechanism works for torch if `libsimple_runtime.so` is findable.
TreeSitter has SFFI spec but no shared library built yet.

## What Could Still Be Fixed

| Category | Tests | Effort | Approach |
|----------|-------|--------|----------|
| TreeSitter FFI | 43 | L | Build `libspl_treesitter.so` wrapping tree-sitter C library |
| Tensor FFI | 12 | S | `libsimple_runtime.so` already has 66 `rt_torch_*` symbols — ensure it's findable |
| Implicit mul | 19 | L | Math block evaluator needs scope resolution |
| Generators codegen | 8 | L | Generator state machine in interpreter |

**Genuinely unfixable in interpreter mode:** ~48 tests (Vulkan 9, VHDL 8, Baremetal 17, MCP 8, Perf 2, JIT 1, native ops 1, loader exec 1, class invariant 1, default fields 1)

---

## Progress History

| Date | Skipped | Change |
|------|---------|--------|
| 2026-01-21 | ~400+ | Initial triage |
| 2026-03-02 | 198→150 | Round 2 triage (48 stale deleted, 13 un-skipped) |
| 2026-03-10 | 240→183 | Round 3 (module var fix, trait dispatch, FFI dlopen, rewrites) |
