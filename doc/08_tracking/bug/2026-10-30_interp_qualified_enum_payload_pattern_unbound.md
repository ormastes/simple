# Interpreter: `case Type.Variant(x):` fails with "undefined variable: x"

- Status: FIXED 2026-10-30
- Component: pure-Simple core interpreter (`src/compiler/10.frontend/core/interpreter/eval.spl`, `match_pattern`)
- Found by: post-merge review of PR #5333 (`enum_instance_method_dispatch_spec` 2/3 on release)

## Symptom

`test/01_unit/compiler/interpreter/enum_instance_method_dispatch_spec.spl`
example "resolves payload and unit variants through the enum impl" returned 0
instead of 73. Probing showed the owner dispatch from #5333 was fine
(`Ticket.Ready(7).one()` returned 5). Every `match` with a qualified payload
pattern failed, with or without an impl method around it:

```
match t:
    case Ticket.Ready(value): value    # -> error "undefined variable: value"
```

Unqualified `case Ready(value):` worked.

## Root cause

The core parser builds `Ticket.Ready(value)` as `EXPR_METHOD_CALL` (receiver
`Ticket`, method `Ready`). `match_pattern` handled `EXPR_CALL` over an
`EXPR_FIELD_ACCESS` callee, but had no `EXPR_METHOD_CALL` arm, so the pattern
fell to the equality default, which evaluates the pattern with `value` unbound.

## Fix

`match_pattern` now treats an `EXPR_METHOD_CALL` whose receiver is a
capitalised identifier as a variant pattern when the scrutinee is a boxed enum,
the variant is Option/Result, or the variant name is declared.

## Specs

- Reproducer: `test/01_unit/compiler/interpreter/enum_instance_method_dispatch_spec.spl` (now 3/3)
- Generalisation: `test/01_unit/compiler/interpreter/enum_qualified_payload_pattern_spec.spl`
  (binder names, `_`, `Type::Variant`, unit fall-through, mismatch fall-through; 5/5)
