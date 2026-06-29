# Interp: enum method not found in nested/chained call context

**Status:** FIXED in seed source; pending seed rebuild + deploy to default `bin/simple`
**Found:** 2026-06-29 (noise sweep — riscv64 target spec)
**Area:** interpreter / method dispatch (Rust seed)

## Symptom

Calling a method on an enum value that is itself the result of a nested call —
e.g. `t.arch().to_string()` where `arch()` returns an enum — fails in
chained-call position:

```
semantic: method 'to_string' not found on value of type enum in nested call context
```

The same chain works in a plain function body (`bin/simple run` main()); it only
fails when evaluated through the nested/chained-call dispatcher (observed in an
`it` block under `bin/simple test`). Repro:

```simple
enum Color:
    Red
    Green
    fn label() -> text:
        match self:
            Red: "red"
            Green: "green"
class Box:
    pass_dn
impl Box:
    static fn create() -> Box: Box()
    fn color() -> Color: Color.Green
# b.color().label() -> errored in nested position
```

Surfaced as `target_riscv64_spec.spl` "reports RiscV64 architecture"
(`t.arch().to_string()`).

## Root cause

`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs` (the
chained/nested-call dispatcher) handled `Value::Object` (class methods, impl,
trait, UFCS) but had no arm for `Value::Enum`, so enum receivers fell through to
the generic "method not found … in nested call context" error. The primary
method evaluator (`interpreter_method/mod.rs`) handles enum receivers; the
nested dispatcher did not mirror it.

## Fix

Added a `Value::Enum { enum_name, .. }` arm to the nested dispatcher that mirrors
the primary path: look up the method in the enum's impl blocks, then in the enum
body via the local `enums` map and `GLOBAL_ENUMS` (cross-module enums), and call
it with the enum value bound as `self`.

## Verification

Regression test `bdd_enum_method_in_nested_call_context` in
`src/compiler_rust/driver/tests/interpreter_bdd.rs`; end-to-end the
`target_riscv64_spec.spl` "reports RiscV64 architecture" example passes with the
rebuilt binary.

## Deploy gate

Seed-side fix; effective for `bin/simple` after seed rebuild + deploy. Combined
with the falsy-call matcher fix
(`sspec_matcher_falsy_call_result_false_red_2026-06-29.md`), the riscv64 target
spec goes from 2 failures to 0.
