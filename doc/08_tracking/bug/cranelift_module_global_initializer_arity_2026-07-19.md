# Cranelift rejected a function-initialized module global

- **ID:** cranelift_module_global_initializer_arity_2026-07-19
- **Status:** FIXED (focused LLVM/Cranelift smoke PASS; cross-target gates scheduled)
- **Severity:** high
- **Backend:** Cranelift trigger; shared pure-Simple MIR/startup follow-on

## Reproducer

Run case `hyphenated_module_init` from `scripts/check/native-smoke-matrix.shs`
with `NATIVE_SMOKE_BACKEND=cranelift`. Its source is:

```simple
fn init_value() -> i64: 4
fn init_next(value: i64) -> i64: value + 1
val module_value = init_value()
val next_value = init_next(module_value)

fn main() -> i64: module_value * 10 + next_value
```

The build failed before code generation with
`semantic: function expects 2 argument(s), but more were provided`.

## Root cause and fix

The pure-Simple Cranelift adapter passed `(module, emit_name, finished)` to the
two-argument `(module, context)` wrapper. The wrapper already expands that call
to the four-argument runtime ABI, whose name fields are intentionally unused;
the SFFI generator spec now pins that ABI. Fixing the call exposed the shared
MIR gap: a non-foldable module binding had no storage or runtime initializer,
and the hosted entry shim never called module-init symbols. MIR now emits a
zero-backed global plus runtime init/store function, and hosted entry calls
discovered init symbols before `main`.

## Verification

- Original single-initializer fixture: LLVM PASS, return code 4, no fallback.
- Original single-initializer fixture: Cranelift PASS, return code 4, no fallback.
- `scripts/check/check-bootstrap-portability.shs`: PASS.

The Pure binding parser and flat bridge now preserve module-global source spans;
the shared MIR owner orders multiple dynamic globals by those spans before
emitting sequential stores. The dependent fixture returns
`45` when rebuilt, proving the second initializer observes the first global's
stored value; current-source native execution remains pending.

`native_module_global_initializer.spl` is the shared strict fixture. FreeBSD
schedules it as a scoped Cranelift smoke after the default LLVM matrix. The
aggregate ABI unit spec rejects the former three-argument adapter call. The
shared `native_crossmodule_result_u8` fixture repeats the dependent `4 -> 5 ->
45` startup oracle for AArch64/RV64 LLVM+Cranelift execution and
ARM32/RV32/Windows-ARM64 object gates. Fresh staged receipts remain pending.
