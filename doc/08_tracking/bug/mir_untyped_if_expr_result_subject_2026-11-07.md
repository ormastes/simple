# Native-build lowering leaves an `if c: Ok(a) else: Err(b)` subject untyped

Status: OPEN (compiler). Source annotated at the one Stage 2 site so the
bootstrap is unblocked; the lowering defect is not fixed.

## Symptom (bootstrap run 15, Stage 2 row `compiler_cli_build`)

In `src/compiler/99.loader/loader/jit_instantiator.spl` `do_jit_compile`:

- `enum match: bare variant 'Ok' / 'Err' is ambiguous (declared in multiple
  enums); qualify it as EnumName.Ok; subject expression at
  jit_instantiator.spl:419:15 has type unresolved`
- `enum construction 'JitInstantiationResult.Success' / 'CompilationError':
  payload type mismatch at 0` (the `case Ok(compiled_code)` / `case Err(msg)`
  binders had no type).

Source shape:

```
val code_result = if typed_result.success:
    Ok(typed_result.code)
else:
    Err(if typed_result.has_error: typed_result.error else: "Unknown error")
match code_result:
    case Ok(compiled_code): ...
```

## Reproduction

Single-file program with this shape plus any other enum declaring `Ok`/`Err`
variants, built with the run-15 Stage 2 binary
(`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 <stage2>/simple native-build main.spl`):
fails with exactly the four errors above. With
`val code_result: Result<[u8], text> = ...` it builds and the binary prints the
expected result.

The same source passes the seed-interpreted `HirLowering` + `MirLowering`
spec harness at both `dba24b97b4d` and `fe52a1431e6` (also with
`new_for_target`), so the defect is specific to the native-build path (an
un-inferred if-expression join, or a Stage 2 miscompile of the lowering) and
has no seed-side red test yet.

## Next step

Reproduce inside a spec that drives the native-build HIR path, then type the
value-producing `if` merge from its `Ok`/`Err` arms. Remove the annotation in
`jit_instantiator.spl` once fixed.
