# Seed: unit value methods fail in chained (nested) call position

- **Status:** verification-pending
- **Date:** 2026-11-16
- **Component:** Rust seed interpreter (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`, `call_method_on_value`)

## Symptom
After PR #9585 (unit construction), `mk(4096).unwrap().value()` fails with
`semantic: method 'value' not found on value of type unit in nested call context`,
while `val f = mk(4096).unwrap(); f.value` works. `.to_i64()` fails the same way.

## Root cause
Direct receivers dispatch through `interpreter_method/mod.rs:1170` ->
`special::handle_unit_methods`; chained receivers go through
`call_method_on_value`, which had no `Value::Unit` arm and fell to the
METHOD_NOT_FOUND error.

## Fix
`Value::Unit` arm in `call_method_on_value`: `value`/`suffix`/`family`/
`to_string`/`to_text` mirror `handle_unit_methods`; every other method is
forwarded to the inner numeric value (`to_i64`, `abs`, ...). Unit-to-unit
`to_<suffix>` conversion in chained position is not covered (forwarded to the
inner number, which errors) — bind to a variable for that.

## Specs
- Repro + generalization: `test/01_unit/compiler/interpreter/unit_nested_method_dispatch_spec.spl`
  (chained `.value()`, chained `.to_i64()`, parity with bound form, chained `.to_text()`).

## Pure-Simple parity gap
Not changed here: the pure-Simple compiler (`src/compiler/30.types/units/unit_ops.spl`,
HIR/MIR lowering) was not audited for a `.value()` method on unit receivers;
open gap to check once a pure-Simple binary with unit construction is deployed.
