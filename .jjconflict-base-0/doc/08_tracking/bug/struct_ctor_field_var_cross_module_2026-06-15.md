# Bug: struct constructor Type(field: var) fails "unknown argument" in cross-module spec context

**ID:** struct_ctor_field_var_cross_module_2026-06-15
**Filed:** 2026-06-15
**Severity:** P1 — semantic analysis rejects valid constructor syntax when var is a parameter
**Component:** interpreter / semantic analysis — cross-module struct constructor resolution
**Driver:** `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`

## Summary

When a struct defined in module A is constructed with named-field syntax
`Type(field: var)` in a function that is called from a cross-module spec context
(a function that takes `var` as a parameter), the interpreter raises
`semantic: unknown argument 'field'` even though the field name is correct.

The same construction works when:
- The struct is defined inline in the same file, OR
- The value is passed as a fresh inline constructor expression (not a variable)

## Minimal repro

```simple
# In a spec file using std.spec (cross-module context):
use std.spec
use std.common.bytes.span.{ByteSpan}
use std.common.crypto.typed.ctypes.{Digest}

fn wrap_span_direct(span: ByteSpan) -> Digest:
    Digest(payload: span)          # FAILS: "unknown argument 'payload'"

describe "struct ctor cross-module":
    it "Digest(payload: param_span) in cross-module spec":
        val data: [u8] = [1u8, 2u8]
        val sp = ByteSpan.new(data)
        val d = wrap_span_direct(sp)
        expect(d.len()).to_equal(2)
```

Run:
```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple run <above_file>
```

## Observed

```
✗ Digest(payload: param_span) in cross-module spec
  semantic: unknown argument 'payload'
```

## Expected

Constructor `Digest(payload: span)` where `span` is a `ByteSpan` parameter should
succeed since `payload` is a valid field name of `Digest` (defined in ctypes.spl).

## Conditions required to reproduce

1. Struct defined in an imported module (not inline in the same file)
2. Constructor field value is a local **variable** (function parameter or `val`),
   NOT a fresh inline expression like `ByteSpan.new(arr)`
3. The call occurs in a cross-module context (imported function in a spec file)

## Workaround

Route through a static `new(...)` function that takes primitive types and
constructs internally:

```simple
fn wrap_span_via_new(span: ByteSpan) -> Digest:
    Digest.new(span.to_bytes())   # WORKS: avoids Type(field: var) pattern
```

This is the pattern documented in `src/lib/common/crypto/typed/ctypes.spl` in the
`Digest.from_span` comment:

> NOTE: Digest(payload: span) fails with "unknown argument 'payload'" in
> interpreter cross-module context when span is a parameter (not a fresh
> constructor call). Route through new() to avoid the issue.

## Impact

All cross-module code that constructs imported structs with named fields referencing
parameter variables must route through a `new(...)` wrapper. Affects any library
struct used from a spec or cross-module fn.

## Related

- `doc/08_tracking/bug/cross_module_struct_method_poisons_itblock_byte_ops_2026-06-15.md`
  — related cross-module interpreter issue with byte ops
