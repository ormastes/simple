# Native build source closure reports locationless array-to-int conversion

## Status

Resolved on 2026-08-26. The no-stub pure-Simple CLI build reached the
source-closure inventory and exited with only:

`error: semantic: type mismatch: cannot convert array to int`

The diagnostic does not identify the source file, expression, or call stack.

## Reproducer identity

- source revision base: `03432f5ea555ff73d772a40285ca77e2abb59ec2`
- Rust bootstrap compiler SHA-256:
  `ffb639cf56605bfaf719db4e456d410a22f90604c3bc9bf7fdc322b13ab36d9d`
- backend/profile: Cranelift, dynload, entry closure, no stub fallback
- entry: `src/app/cli/_CliMain/main_and_help.spl`
- focused shard: `--parse-shard=0/8`
- log: `build/native_probe/render-shard0-diagnostic2.log`

The shard resolves more than 320 closure files before the failure. The prior
`mission_critical/__init__.spl` Dedent parse defect is fixed and no longer
appears in this run.

## Resolution

`SIMPLE_DEBUG_AS_INT_BT=1` localized the conversion to
`interpreter_extern::sffi_array::rt_array_free_fn`. Native code passes an i64
runtime handle, but interpreted lexer arrays are `Arc`-managed `Value::Array`
objects. The bridge comment already promised a managed-array no-op while its
implementation unconditionally called `as_int()`.

The bridge now leaves interpreter-managed array storage to Rust ownership and
only forwards integer handles to `rt_array_free`. The existing focused test
`rt_array_free_leaves_interpreter_managed_arrays_to_arc` passes. A post-fix
shard advances beyond the former failure through closure item 704/1046 without
an array-to-int conversion.
