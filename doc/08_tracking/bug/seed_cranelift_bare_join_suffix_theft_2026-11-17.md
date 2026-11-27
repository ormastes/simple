# Seed Cranelift Bare `.join(sep)` Erased-Receiver Suffix Theft + Primitive Numeric Suffixes

Date: 2026-11-17
Target: `aarch64-apple-darwin` Stage 2 / compiler frontend (`release/1.0.0`)
Status: FIXED

## Root Cause

1. In `src/compiler/10.frontend/core/unit_scope.spl` (`unit_library_families`),
   `val joined = found.sort().join(",")` chains `.join(",")` onto `found.sort()`.
2. The Rust seed (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`)
   lowered `.sort()` to `rt_sort` without recording an element/array type that
   kept `.join` qualified, so `.join(",")` arrived at `compile_method_call_static`
   as a bare `"join"` call with 1 arg (`lookup_name = "join"`).
3. Unlike `pipeline/native_project/mangle.rs` (`if matches!(lookup_name, "join" | "Array.join")`)
   and unlike `"has"` / `"len"` / `"length"` in `closures_structs.rs`, bare `"join"` was
   absent from both `is_bare_builtin_collection_method` and the in-module suffix-scan
   skip list. Because the Stage 2 compiler closure linked a single user method named
   `join` (`CacheSingleFlightV1.join(self, key, request_id)`), the single-candidate
   name-suffix fallback in `closures_structs.rs` bound `found.sort().join(",")` directly
   to `_compiler__driver__cache__daemon__cache_single_flight_v1__CacheSingleFlightV1_dot_join`
   (verified via `llvm-objdump -d phase2/simple`: `bl 0x1014f12a0` immediately after
   `bl _rt_sort`) instead of falling through to `"join" => "rt_string_join"`.
4. Passing a `SplArray*` as `CacheSingleFlightV1*` with uninitialized `x2` corrupted
   memory, returned bogus non-empty `joined` strings, triggered false
   `unit suffix '<u64|u8|u32|i8>' is not in scope` parser errors across 19+ files,
   and crashed Stage 2 build workers with `SIGSEGV` (`signal 11`).
5. Additionally, `unit_suffix_scope_error` did not short-circuit built-in primitive
   numeric suffixes (`i8..i128`, `u8..u128`, `isize`, `usize`, `f16..f64`), and line
   194 carried an unescaped `".{"` interpolation warning (`W-STR-BRACE-001`).

## Fix

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`:
  - Added `| ("join", 1)` to `is_bare_builtin_collection_method`.
  - Excluded bare `"join"` alongside `"has" | "len" | "length"` in the in-module
    suffix-binding fallback so erased-receiver `.join(sep)` routes to `rt_string_join`.
  - Added `"join"` to `builtin_method_result_type` returning `Some(TypeId::STRING)`.
  - Added unit test `erased_join_uses_builtin_dispatch` and executable JIT regression
    `src/compiler_rust/compiler/tests/erased_join_sort_chain_jit.rs`.
- `src/compiler/10.frontend/core/unit_scope.spl`:
  - Added `unit_is_primitive_numeric_suffix` fast-path at entry to `unit_suffix_scope_error`.
  - Switched `".{"` / `"}"` hint formatting to raw string literals (`r".{"`, `r"}`"`).
- `test/01_unit/compiler/frontend/compiled_unit_suffix_scope_spec.spl`:
  - Added regression checking primitive numeric suffixes pass even with empty unit library root.
