# Native cross-module arithmetic probe exits 5

## Status

Open. The focused default-LLVM native build links successfully, but the
resulting fixture exits with status 5 before printing `result-u8-ok`.

## Reproduction

Use the current Stage3 compiler and bootstrap runtime with
`scripts/check/check-native-crossmodule-result-u8.shs`. Retained evidence:

- build log: `/tmp/check-native-crossmodule-result-u8-final-2850000/build.log`
- executable: `/tmp/check-native-crossmodule-result-u8-final-2850000/result-u8-default`

The build reports three compiled modules and no failures. Running the binary
returns 5 with empty stdout.

## Boundary

Exit 5 maps to `cross_target_arithmetic_ok()` in
`test/fixtures/native_crossmodule_result_u8/main.spl`. It checks mixed
signed/unsigned/float comparisons, unsigned division/remainder and shift,
signed arithmetic shift, and signed division/remainder. The exact
subexpression is not yet isolated.

This appeared only after restoring the missing Core-C `rt_array_last` and
`rt_getpid` ABI owners. Link and runtime-symbol selection now succeed; the
remaining arithmetic-path failure may be in lowering, codegen, or runtime
semantics and needs the subexpression isolation below.

## Next step

In a fresh verification session, split the arithmetic predicate into uniquely
identified checks or a minimal fixture, then fix the shared lowering/codegen
owner. Do not weaken or delete the cross-module fixture.
