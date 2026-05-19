# Cross-Module ABI Fix — State

## Status: DONE (committed in 5d65a6a7f8)

## Bug Reference
`doc/08_tracking/bug/native_cross_module_call_abi_broken_2026-05-18.md`

## Root Cause (Confirmed Empirically)

`nm .simple/native_cache/objects/*.o` shows:
- Caller imports: `U is_digit` (bare name)
- Exporter defines: `T common__ctype__is_digit` (mangled)

These don't match → linker calls wrong symbol or a random function.

### Code Path

1. `imports.rs:build_import_map` — builds `raw_to_mangled`:
   - bare key `"is_digit"` → `["common__ctype__is_digit", "compiler__10.frontend__core__lexer_chars__is_digit", ...]` (multiple)
   - Since `mangled_list.len() > 1`, goes into `ambiguous` set but still inserts `mangled_list[0]` (non-deterministic)

2. `imports.rs:collect_use_imports` (Single branch, lines 601-612) — for `use std.common.ctype`:
   - Inserts `name="ctype"` → resolved mangled (the module itself, not a function)
   - Iterates `all_mangled` looking for keys starting with `"ctype."` — finds nothing because free functions are keyed as bare `"is_digit"`, NOT `"ctype.is_digit"`
   - So `use_map` does NOT get `"is_digit"` → `"common__ctype__is_digit"`

3. `calls.rs:compile_call` (lines 2767-2811) — for call to `ctype.is_digit`:
   - Checks `use_map.get("ctype.is_digit")` → None
   - Checks `import_map.get("ctype.is_digit")` → None (dotted form not in map)
   - Falls through to rfind('.') branch: gets `method = "is_digit"`
   - Checks `import_map.get("is_digit")` → picks `mangled_list[0]` = non-deterministic wrong module

4. Result: caller declares import symbol `is_digit` (or wrong module's mangled), callee exports `common__ctype__is_digit` → **ABI mismatch**

## Fix Plan

In `imports.rs:collect_use_imports`, when `target = Single(name)` and the name matches a module/prefix:

After inserting the module name itself, also walk `all_mangled` to find bare function names whose ONLY matching candidate (under the use path) belongs to this module. Insert them as `"bare_name"` → `"module__bare_name"`.

Alternatively (simpler): in `resolve_import_name_strict`, when `func_name` is bare and multiple candidates exist, check if any single candidate's prefix matches the use_segments exactly — use that one.

**Chosen fix location**: `collect_use_imports` Single branch: after the `prefix = format!("{}.", name)` loop, also walk all bare function entries and use `resolve_import_name_strict` with the use_segments to pick the right one. Then insert `bare_name → correct_mangled` into `use_map`.

This means: for `use std.common.ctype` with segments `["lib","common","ctype"]`, when iterating bare names, `resolve_import_name_strict("is_digit", ["lib","common","ctype"], ...)` finds `common__ctype__is_digit` because `mangled_matches_use_path("common__ctype__is_digit", ["lib","common","ctype"])` should be true.

## Files Modified

- `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs` — `collect_use_imports` Single branch (lines 613-634)

## Verification

- Bootstrap build (`cargo build --profile bootstrap`) completed successfully (4m 12s, no errors)
- `nm .simple/native_cache/objects/*.o` confirmed: caller was importing bare `is_digit`, exporter was exporting `common__ctype__is_digit` — symbol mismatch at link time
