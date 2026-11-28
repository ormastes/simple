# Dict methods not found in nested call context (seed interpreter)

- id: seed_nested_call_dict_methods_missing_2026-11-28
- status: fixed (seed side, work/seed-libc-externs-dict-chain-20261128); workaround removed
- component: seed interpreter (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`, `call_method_on_value_with_args`)
- found by: `test/01_unit/app/orchestrator/host_action_command_v1_spec.spl`
  ("accepts the plan form and the confirm form, nothing in between") under the Rust seed
- sibling of: `seed_nested_call_rfind_missing_2026-11-15`, `str_byte_len_not_found_in_nested_call_context_2026-11-12`

## Symptom
`plan.unwrap().contains_key("--confirm")` fails under `<seed> test` with
`semantic: method 'contains_key' not found on value of type dict in nested call context`.
Binding the receiver first (`val opts = plan.unwrap()`, then `opts.contains_key(..)`) works.

## Root cause
Chained receivers are dispatched through `call_method_on_value_with_args`, which has
arms for Str, Array, ByteArray, enums, objects and the BDD matchers but **no
`Value::Dict` / `Value::FrozenDict` arm** (the only Dict mention is the trait-impl
type-name table). The direct-receiver path `handle_dict_methods`
(`interpreter_method/collections.rs`) supports `has` / `contains_key` / `contains`,
`get`, `keys`, `len`, ... so only the chained form fails.

## Minimal repro (Rust seed interpreter, diagnostic, 2026-11-28)
```simple
use std.spec.*

fn mk() -> Result<Dict<text, text>, text>:
    Ok({"a": "1"})

describe "chained dict contains_key":
    it "bound receiver":
        val d = mk().unwrap()
        expect(d.contains_key("a")).to_equal(true)
    it "chained receiver":
        expect(mk().unwrap().contains_key("a")).to_equal(true)
```
Result: `executed=2 passed=1 failed=1` — the chained case fails with the message above.

## Workaround applied
`host_action_command_v1_spec.spl` binds `plan.unwrap()` to `plan_options` before
`contains_key`, tagged `@workaround bug=seed_nested_call_dict_methods_missing_2026-11-28`.
The assertion is unchanged.

## Seed fix
Add a `Value::Dict` / `Value::FrozenDict` arm to the chained dispatcher that delegates
the read-only methods (`len`, `is_empty`, `has`/`contains_key`/`contains`, `get`,
`get_or`, `keys`, `values`) to the same logic as `handle_dict_methods`, with a unit
test next to `nested_rfind_and_last_index_of_dispatch_on_temporary_text`. Then drop
the workaround once frozen pre-fix seeds are superseded.

## Fix (2026-11-28)
`call_method_on_value_with_args` gained a `Value::Dict` / `Value::FrozenDict`
arm delegating to `dict_read_method_on_values` (`interpreter_method/collections.rs`:
`len`, `is_empty`, `has`/`contains_key`/`contains`, `get`, `get_or`, `keys`,
`values`, with the same namespace gates as `handle_dict_methods`). Test:
`nested_dict_read_methods_dispatch_on_temporary_dict`. The workaround in
`host_action_command_v1_spec.spl` is removed, so pre-fix seeds (including any
shared seed built before this change) fail that example again until rebuilt.

Rust seed interpreter, diagnostic: before `executed=8 passed=7 failed=1`
(`'contains_key' not found on value of type dict in nested call context`);
after `executed=8 passed=8 failed=0`.
