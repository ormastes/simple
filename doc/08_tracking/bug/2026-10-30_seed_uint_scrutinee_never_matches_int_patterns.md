# Seed: a UInt value never matches integer literal or range patterns

- Status: OPEN
- Component: Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter_patterns.rs` (~200-205, ~549-551)
- Found by: Fable review of PR #5370 (`to_u64()` now yields `Value::UInt`)

## Symptom

Integer literal and range pattern arms return `false` unless the scrutinee is
`Value::Int`. With PR #5370 an untyped `val u = x.to_u64()` is `Value::UInt`, so

```
match u:
    case 0: ...
    case 1..=9: ...
    case _: ...
```

silently takes `_`. A typed `val u: u64` binding was already `UInt` and already
had this gap. No `match <expr>.to_u64()` site exists in `src/` today.

Related gaps from the same review:
- A `UInt` argument bound to an `i64` parameter stays `UInt`
  (`interpreter_call/core/arg_binding.rs` ~250-275 only coerces toward u*).
- `to_u64()` on Float/Float32 receivers still returns `Value::Int`
  (`method_dispatch.rs` Float arms, `primitives.rs` ~281), while HIR types the
  result as U64 for any receiver.

## Unblock / fix

Compare literal and range patterns numerically for `UInt` (value fits i64, or
pattern literal is non-negative), and return `UInt { width: 64 }` from the
Float `to_u64` arms.
