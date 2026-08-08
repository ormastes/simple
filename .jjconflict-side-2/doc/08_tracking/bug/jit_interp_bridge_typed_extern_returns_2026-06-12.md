# JIT InterpCall bridge: f64/text extern returns not representable

- **ID**: jit_interp_bridge_typed_extern_returns
- **Date**: 2026-06-12
- **Severity**: P3
- **Status**: open
- **Component**: seed compiler — cranelift JIT hybrid execution

## Context

`run_file_jit` now routes extern declarations the JIT cannot link (symbol
absent from the runtime provider, e.g. all `rt_torch_*` in a torch-less
build) through the `rt_interp_call` interpreter bridge instead of letting
them bind to a null pointer and SIGSEGV (fixed 2026-06-12, see commits
"route JIT-unresolvable externs to interpreter bridge" and follow-ups).

The bridge returns boxed `RuntimeValue`s. Compiled callers of typed externs
expect raw machine values, so `compile_interp_call` unboxes results for
`rt_*`/`spl_*` callees via the new `rt_value_raw_i64` helper (bool → 0/1,
int/handle → i64, nil/error → 0).

## Gap

Two extern return types are not faithfully representable through this path:

1. **f64 returns** (e.g. `rt_torch_nn_mse_loss`): `rt_value_raw_i64`
   truncates the float to an integer i64. The destination vreg expects f64
   bits. Correct handling needs the callee's declared return type at
   lowering time.
2. **text returns** (e.g. `rt_torch_version`): the interpreter produces a
   heap `Value::Str`; raw-i64 coercion yields 0 (null text) instead of an
   `rt_string` pointer.

## Why not fixed in the same change

`MirInst::Call`/`InterpCall` carry no return type, and
`build_vreg_types` (codegen/instr/body.rs) has no arm for call dests, so
the lowering site cannot dispatch on type. The clean fix is to add a
`return_type: TypeId` field to `MirInst::InterpCall`, populated by
`apply_hybrid_transform` from HIR extern signatures (available in
`run_file_jit` via `hir_module`), then dispatch in `compile_interp_call`:
BOOL/int → `rt_value_raw_i64`, F64 → `rt_value_as_float` (needs an F64
RuntimeFuncSpec), STRING → a boxed-Str → rt_string conversion helper.

## Impact

Only affects JIT execution of programs that call f64/text-returning
externs whose symbols are missing from the seed binary (torch dylib
absent). These calls were a hard SIGSEGV before the bridge landed; now
bool/int/handle externs are correct and f64/text externs degrade to wrong
values instead of crashing.

## Repro

```bash
# torch-less host:
cat > /tmp/r.spl <<'EOF'
use std.nogc_async_mut.torch.sffi.{rt_torch_version}
fn main():
    print(rt_torch_version())
EOF
src/compiler_rust/target/release/simple run /tmp/r.spl   # null text, not a version string
```
