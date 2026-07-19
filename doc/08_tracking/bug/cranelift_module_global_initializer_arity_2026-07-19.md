# Cranelift rejects a function-initialized module global

- **ID:** cranelift_module_global_initializer_arity_2026-07-19
- **Status:** OPEN
- **Severity:** high
- **Backend:** Cranelift only; LLVM passes

## Reproducer

Run case `hyphenated_module_init` from `scripts/check/native-smoke-matrix.shs`
with `NATIVE_SMOKE_BACKEND=cranelift`. Its source is:

```simple
fn init_value() -> i64: 4
val module_value = init_value()

fn main() -> i64: module_value
```

The build fails before code generation with
`semantic: function expects 2 argument(s), but more were provided`. The same
case passes with LLVM and returns `4`. The matrix marks only the Cranelift row
XFAIL so every hosted platform keeps the reproducer active.
