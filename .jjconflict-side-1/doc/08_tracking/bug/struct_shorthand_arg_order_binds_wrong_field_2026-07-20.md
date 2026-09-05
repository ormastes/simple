# Bug: struct-literal shorthand argument binds to `nil` when it follows an explicit named argument

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/struct_shorthand_spec.spl`)
- **Area:** struct-literal call argument binding (interpreter or HIR lowering,
  not isolated further in this pass), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`struct_shorthand_spec.spl`, 2 failures:

```
✗ uses explicit then shorthand
  struct Point: x: i64, y: i64
  val y = 20
  val point = Point(x: 10, y)      # shorthand `y` means `y: y`
  expect point.y == 20             --> expected nil to equal 20

✗ mixes in complex struct
  struct Config: host: text, port: i64, timeout: i64
  val config = Config(host, port: 8080, timeout)
  expect config.host == "localhost" --> expected nil to equal 30 (timeout check;
                                          host check also fails per the batch run)
```

The sibling example in the same file, "mixes shorthand with explicit named
argument" (`Point(x, y: 20)` — shorthand **first**, explicit **second**),
**passes**. Only the reverse order (explicit first, shorthand after) breaks.

## Minimal repro

```simple
struct Point:
    x: i64
    y: i64

describe "repro":
    it "explicit then shorthand":
        val y = 20
        val point = Point(x: 10, y)
        expect point.x == 10
        expect point.y == 20
```

## Root cause

Not isolated to a specific source location in this pass (would need to trace
struct-literal call lowering / argument binding). The order-dependence (works
shorthand-then-explicit, fails explicit-then-shorthand) suggests the binder
processes explicit-named and positional/shorthand arguments via two separate
passes or index-tracking mechanisms that get out of sync once an explicit
named arg appears before a shorthand one — e.g. the shorthand arg after the
named one may be getting bound by positional index against the wrong
struct-field slot (or dropped) rather than resolved by its identifier name.

## Fix direction (not applied — compiler-internals change, needs rebuild)

Trace struct-literal call argument binding (likely
`src/compiler_rust/compiler/src/interpreter*` or HIR lowering for
`Expr::Call`/`StructInit`-shaped nodes) and confirm shorthand args are always
resolved by matching their identifier name against the struct's field name,
regardless of whether preceding arguments were explicit or shorthand.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.
