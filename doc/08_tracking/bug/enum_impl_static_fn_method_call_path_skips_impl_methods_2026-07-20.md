# Bug: `EnumName.static_method()` call-expression path ignores `impl EnumName:` static methods (only checks inline enum-body methods)

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/shared/control_flow/static_fn_spec.spl`)
- **Area:** `src/compiler_rust/compiler/src/interpreter_method/mod.rs` (`Value::EnumType` method-call dispatch), deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`test/shared/control_flow/static_fn_spec.spl`, all 4 examples under "Direction
factory methods" fail identically:

```
✗ creates northeast direction
  semantic: unknown variant or method 'northeast' on enum Direction
✗ creates southeast direction
  semantic: unknown variant or method 'southeast' on enum Direction
✗ creates southwest direction
  semantic: unknown variant or method 'southwest' on enum Direction
✗ creates northwest direction
  semantic: unknown variant or method 'northwest' on enum Direction
```

The spec defines `static fn northeast()`, `southeast()`, `southwest()`,
`northwest()` inside a separate `impl Direction:` block (not inline in the
`enum Direction:` body), each returning `Direction.Custom(degrees: N)`. Every
other `static fn` in the same file -- on `class Point`, `class Color`, `class
CallEventRecorder` (also all declared via a separate `impl X:` block) -- works
fine (18 of 22 other examples in the file pass). Only the enum's `impl`-block
static methods fail.

## Minimal repro

```simple
enum Direction:
    North
    South
    East
    West
    Custom(degrees: i32)

impl Direction:
    static fn northeast() -> Direction:
        Direction.Custom(degrees: 45)

describe "repro":
    it "creates northeast direction":
        val d = Direction.northeast()
        match d:
            case Direction.Custom(deg):
                expect(deg).to_equal(45)
            case _:
                expect(false).to_equal(true)
```

Actual (`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`):
```
✗ creates northeast direction
  semantic: unknown variant or method 'northeast' on enum Direction
```

Expected: pass (`deg == 45`).

Note: `bin/release/.../simple run <repro>.spl` (i.e. the file interpreted
directly, not through the SSpec `test` command) does NOT throw this error --
`Direction.northeast()` is callable there. The bug is specific to the
call-expression code path used when the call sits inside a `describe`/`it`
SSpec block under `bin/simple test`.

## Root cause (confirmed by source read)

There are two different call sites in the Rust seed interpreter that resolve
`EnumName.method(...)`-shaped expressions, and only one of them checks
`impl_methods`:

1. `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` (~line
   538-565), the field-access-then-call path: after checking variant names
   and inline enum-body methods, it explicitly falls back to `impl_methods`
   (both the module-local map and `GLOBAL_IMPL_METHODS`) before erroring.
   This path is exercised by `bin/simple run`, which is why the repro above
   works there.

2. `src/compiler_rust/compiler/src/interpreter_method/mod.rs` (~line
   953-1003), the `Value::EnumType` method-call dispatch (used for calls
   nested inside other call/method-chain expressions, which is what an
   SSpec `it` block's expression evaluation goes through): it checks variant
   names, then `enum_def.methods` (methods declared *inline inside the enum
   body*, e.g. `enum Direction: ... fn foo(): ...`), and if neither matches
   goes straight to `unknown_enum_variant_or_method(method, enum_name)` at
   line 1006 -- **it never consults `impl_methods` at all**, unlike path (1).

Because the spec's `static fn northeast()` etc. are declared in a *separate*
`impl Direction:` block (not inline in the enum body), path (2) can never find
them, while `class` static methods work fine in the same code path elsewhere
in `interpreter_method/mod.rs` presumably because the class-method dispatch
arm does consult `impl_methods` (not verified in this pass, but consistent
with all 18 class-based static-fn examples in the same spec file passing).

## Suggested fix shape (not applied -- compiler-internals change, out of scope for this pass)

In `src/compiler_rust/compiler/src/interpreter_method/mod.rs`, the
`Value::EnumType { enum_name }` arm (~line 954-1006) should add the same
`impl_methods` / `GLOBAL_IMPL_METHODS` lookup that
`src/compiler_rust/compiler/src/interpreter/expr/calls.rs` (~line 546-561)
already performs, before falling through to
`unknown_enum_variant_or_method`.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/shared/control_flow/static_fn_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Both reproduce the identical "unknown variant or method" semantic error for
all 4 `impl`-block enum static methods. Not checked against the pure-Simple
self-hosted compiler/interpreter (`src/compiler/`) or the JIT/native path --
only the Rust seed interpreter (the path `bin/simple test` exercises) was
probed. Not fixed here per task scope (source-level fix in
`interpreter_method/mod.rs` needs a full rebuild to validate, which this pass
is scoped to avoid).
