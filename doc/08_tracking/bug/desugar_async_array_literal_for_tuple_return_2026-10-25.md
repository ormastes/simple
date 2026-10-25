# desugar_async returns array literals from tuple-typed functions (2026-10-25)

## Symptom
Phase 3 Stage 3 (`simple.pu3` + fixes, run-27e objects), in-process bypass route
(`native-build <file>.spl` positional, no `--entry`): hello world SEGVs right
after parse in `compiler.frontend.desugar.desugar_async.desugar_module+0x1ab0`,
`ldr x8,[x8]` with x8 = 0x100000000.

## Root cause
`desugar_async_function_with_body_name` and `desugar_async_body_with_name` are
declared `-> (ParserFunction|Block, [ParserEnum], [ParserFunction])` but return
array literals (`return [func, [], []]`, `[transformed_func, ...]`, ...). The
interpreter tolerated this. Natively the caller treats the value as a tuple:
`_destruct_2[0]` loads word 0 of the object, which for an array is its heap
header (`0x0000000100000002`, kind ARRAY), then dereferences it as the
ParserFunction struct.

## Fix
Return tuple literals at all five sites (and the four in the
`src/compiler/90.tools/desugar_async.spl` copy).
Spec: `test/01_unit/compiler/async/desugar_async_tuple_return_spec.spl`.

## Compiler gap (separate)
The type checker accepted an array literal where a tuple return type was
declared. That should be a compile error; recorded here, not fixed in this
change.
