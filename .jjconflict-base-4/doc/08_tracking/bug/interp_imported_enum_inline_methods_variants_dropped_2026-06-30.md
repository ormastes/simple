# Bug: imported enum with inline methods loses its variants under the interpreter

**Date:** 2026-06-30
**Severity:** High — any `match`/construction on an imported enum whose body
mixes variants with inline `static fn` methods fails under the classic
interpreter (`SIMPLE_EXECUTION_MODE=interpret`, which is what `bin/simple test`
uses). JIT (`run` default) handles it correctly, so this is interpreter-only.
**Component:** Rust seed — interpreter module/enum registration
(`interpreter/expr/calls.rs:501-561`, enum import/registration path).

## Symptom

`match v: case SdnValue.Int(i): …` (and constructing `SdnValue.Int(42)`) raises:

```
error: semantic: unknown variant or method 'Int' on enum SdnValue
```

even though `enum SdnValue` (src/lib/common/sdn/value.spl:28) clearly declares
`Int(i64)`. At calls.rs:508 `enum_def.variants.iter().find(|v| v.name == "Int")`
returns None — the registered enum_def's `.variants` is missing/partial for the
imported enum.

Fails 5 examples in `test/01_unit/lib/common/roundtrip_spec.spl`
("preserves primitives/inline dicts/inline arrays/block dicts/...").

## Minimal reproducer

```simple
use std.sdn.value.{SdnValue}
fn main():
    val v = SdnValue.Int(42)
    match v:
        case SdnValue.Int(i): print("int {i}")
        case _: print("other")
```

- `bin/simple run repro.spl` (JIT)            → `int 42`  ✓
- `SIMPLE_EXECUTION_MODE=interpret … run`      → `unknown variant or method 'Int'` ✗

## Isolation (what is NOT the cause)

An equivalent enum **defined inline in the same file** works under the
interpreter — including with a named-field variant (`Table(headers:…, rows:…)`)
AND a static method whose name case-collides with a variant (`static fn int` vs
`Int`). Both of these passed:

```simple
enum MyV:
    Null
    Bool(bool)
    Int(i64)
    String(text)
    Table(headers: [text], rows: [[i64]])
    static fn int(i: i64) -> MyV: MyV.Int(i)
# match MyV.Int(42) → "int 42"  ✓ under interpret
```

So the trigger is specifically that the enum is **imported from a module** and
its body mixes variants with inline `static fn` methods (SdnValue has ~15 inline
static factory methods in its body, lines 38-207). The variants are dropped from
the interpreter's registered enum_def during import; JIT keeps them.

## Confirmed: variants absent from ALL registries (not a shadowing issue)

Tried preferring whichever of `enums` / `BLOCK_SCOPED_ENUMS` / `GLOBAL_ENUMS`
actually declares the variant — no effect. The variants are missing from every
registry, so the imported enum's `variants` are dropped at **import/registration
time**, not merely shadowed by a stale stub. The fix must restore variants when
an imported enum with inline `static fn` methods is loaded.

## Suspected root cause

The module-import enum registration likely processes the enum's inline methods
into the impl/method table but registers an enum_def whose `.variants` is empty
or stale (a forward/partial entry overwriting the full one), so the later
`SdnValue.Int` lookup at calls.rs:508 misses. Compare with the inline-define
path, which registers variants intact. Audit the import path that populates
`enums` / `GLOBAL_ENUMS` / `BLOCK_SCOPED_ENUMS` for enums that carry inline
methods — ensure variants survive when the inline methods are split out.

## Repro files (scratch)

`/tmp/cl_sdn.spl`, `/tmp/cl_enum.spl` (passing inline control).
