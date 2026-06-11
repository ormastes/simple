# Bug: Native cross-module function call returns wrong values (Cranelift)

Status: FIXED 2026-05-19

**Status:** FIXED 2026-05-19
**Date:** 2026-05-18
**Severity:** High — blocks native-mode benchmarking of any cross-module code
**Component:** `native-build` / Cranelift AOT codegen

## Symptom

Functions called across module boundaries in native-compiled binaries return
wrong values. Both `bool` and `i64` return types are affected.

## Minimal Repro

```spl
# src/lib/common/ctype.spl — is_digit returns bool
# /tmp/bool_call_repro.spl:
use std.common.ctype

fn main():
    var chk = 0
    var ch = 0
    while ch < 128:
        if ctype.is_digit(ch):
            chk = chk + 1
        ch = ch + 1
    print "chk should be 10, got: {chk}"
```

```bash
bin/simple native-build --entry /tmp/bool_call_repro.spl \
  --source src/lib --entry-closure -o /tmp/bool_call_native --backend cranelift
/tmp/bool_call_native
# Output: chk should be 10, got: 0
```

Same-module calls work correctly. Interpreter mode works correctly.

## i64 variant

```spl
use std.common.ctype
fn main():
    var chk = 0
    var ch = 0
    while ch < 128:
        chk = chk + ctype.to_lower(ch)
        ch = ch + 1
    print "chk should be 8960, got: {chk}"
# Native output (before fix): chk should be 8960, got: 983245137
# Note: original expected value 8256 in this doc was wrong.
# Correct: sum(0..127)=8128 + 26 uppercase offsets×32=832 → 8960.
# Interpreter mode also returns 8960 (ground truth).
```

## Impact

- All native-mode cross-module benchmarks produce wrong results
- Blocks AC-4 (native perf benchmarks) for the C-to-Simple runtime conversion
- Same-module code and interpreter mode are unaffected

## Likely Cause

Name mangling or calling convention mismatch between compilation units in the
Cranelift AOT `native-build` pipeline. Each `.spl` file is compiled to a
separate `.o` file in `.simple/native_cache/objects/`, then linked. The caller
and callee may disagree on symbol name, parameter passing, or return value
register.

## Fix

**Committed:** 5d65a6a7f8 (2026-05-19)
**File:** `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`
**Function:** `collect_use_imports` Single branch

In `collect_use_imports`, after the `"module."` prefix loop, now also walks all
bare (non-dotted) function names in `all_mangled` that are not already in
`use_map`. For each with multiple candidates, calls
`resolve_import_name_strict(raw_name, use_segments, ...)` which finds the
unique candidate whose mangled prefix matches the use-path segments. Inserts
`bare_name → correct_mangled` into `use_map`.

Result: for `use std.common.ctype`, `use_map["is_digit"] = "common__ctype__is_digit"`
so `calls.rs` declares the correct import symbol and the linker resolves correctly.

**Verified 2026-05-20:**
- `nm` shows caller now imports `U common__ctype__is_digit` (matches exporter `T`)
- bool repro: `got: 10` ✓
- i64 repro: `got: 8960` ✓
- Regression spec: `test/01_unit/compiler/codegen/native_cross_module_abi_spec.spl`

## Workaround

~~Use interpreter mode for correctness testing. Native benchmarks require
same-file inlined implementations until this is fixed.~~

**Fixed.** Cross-module native calls now work correctly.
