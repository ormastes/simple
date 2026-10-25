# Module-scoped mono raises no E-MONO-040 when the template is not visible

**Status:** open. Owner: P-G3 (#4598).
**Filed by:** P-G5 (#4628), at the lead reviewer's request.

## Symptom

`run_monomorphization_module_scoped_v1(f, {})` returns **0** diagnostics for a module whose
`main` calls the imported generic `id(1)` when the templates dict is empty. The expected result
is exactly one `E-MONO-040: template id not visible to module ...`.

The per-file lane relies on this diagnostic. Without it:

- `native_file_worker_missing_templates_v1` finds no missing template;
- the reader, widen and MONO-PENDING fallback (`native_file_worker_mono_fallback_reader_v1`)
  never fires;
- an object that still contains an unresolved generic call could be emitted instead of failing closed.

## Repro

`test/01_unit/compiler/mono/mono_module_scoped_spec.spl`, case
`fails closed with E-MONO-040 when the template is not visible`. It fails with
`array index out of bounds: index is 0 but length is 0`, because `diags.len()` is 0.

This case was never executed before P-G5. Its fixtures were plain string literals, so
`"use t.{id}"` was interpolated, and the whole file failed to load with
`variable 'id' not found`. P-G5 made the fixtures raw strings. Since then the other three
P-G3 cases pass and this one fails.

Host: Windows, seed `bin/simple.exe` interpreter.

## Where to look

`MonomorphizationPass.module_scoped_visibility_check_v1` in
`src/compiler/40.mono/monomorphize_integration.spl`:

- `callee_local_plain` or the `sym_names` lookup may treat the unresolved imported `id` as local;
- the evidence probe may find a concrete signature row.

Either way, the call site never reaches the `E-MONO-040` push.

Do not skip or weaken the case.
