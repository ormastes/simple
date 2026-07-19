# Cranelift module-global initializer fails before code generation

- **ID:** cranelift_module_global_initializer_arity_2026-07-19
- **Status:** FIXED
- **Severity:** high
- **Backend:** Cranelift trigger; shared pure-Simple MIR/startup follow-on

## Reproducer

Run case `hyphenated_module_init` from `scripts/check/native-smoke-matrix.shs`
with `NATIVE_SMOKE_BACKEND=cranelift`. Its source is:

```simple
fn init_value() -> i64: 4
val module_value = init_value()

fn main() -> i64: module_value
```

The build failed before code generation with
`semantic: function expects 2 argument(s), but more were provided`.

## Root cause and fix

The pure-Simple Cranelift adapter first passed `(module, name, context)` to a
two-argument `(module, context)` wrapper. Fixing that exposed the shared MIR
gap: a non-foldable module binding had no storage or runtime initializer, and
the hosted entry shim never called module-init symbols. The adapter now uses
the wrapper contract; MIR emits a zero-backed global plus runtime init/store
function; and the hosted entry calls discovered init symbols before `main`.

## Verification

- `hyphenated_module_init`: LLVM PASS, return code 4, no fallback.
- `hyphenated_module_init`: Cranelift PASS, return code 4, no fallback.
- `scripts/check/check-bootstrap-portability.shs`: PASS.
