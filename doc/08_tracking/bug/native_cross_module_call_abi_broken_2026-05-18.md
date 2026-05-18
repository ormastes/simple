# Bug: Native cross-module function call returns wrong values (Cranelift)

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
    print "chk should be 8256, got: {chk}"
# Native output: chk should be 8256, got: 256229713
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

## Workaround

Use interpreter mode for correctness testing. Native benchmarks require
same-file inlined implementations until this is fixed.
