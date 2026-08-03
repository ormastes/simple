# Pure-Simple LLVM shard emits invalid `bitcast i1` to `ptr`

- **Date:** 2026-08-03
- **Status:** FIXED
- **Severity:** P1
- **Area:** pure-Simple LLVM MIR lowering
- **Verified owner:**
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl::value_as_type`
- **Reproducer:** `src/lib/nogc_async_mut/env/paths.spl` compiled as the
  focused pure-Simple Stage 4 shard

## Reproduction

The diagnostic compiler was a freshly rebuilt pure-Simple Stage 3
(`725 compiled, 0 failed`) targeting `x86_64-unknown-linux-gnu`. It compiled
`src/lib/nogc_async_mut/env/paths.spl` as a single positional native-build
input, which `bootstrap_main.spl` routes through the in-process pure-Simple
CompilerDriver. `SIMPLE_BOOTSTRAP_STAGE4` was not set and the command did not
pass an explicit entry-closure flag. After the separate target-triple lifetime
repair, this focused shard emitted a valid LLVM header and reached `llc`.

`llc` then rejected `/tmp/simple_llvm_3450082.ll` at line 2874, column 19:

```llvm
%t281 = bitcast i1 %l162 to ptr
```

The diagnostic is `invalid cast opcode for cast from 'i1' to 'ptr'`. This is a
new downstream blocker; it is not a recurrence of the former
`<invalid-heap:...>` target triple.

## Root-cause direction

`translate_terminator` routes return coercions through `value_as_type`, whose
generic cast selector falls back to LLVM `bitcast` whenever no known cast
matches. LLVM does not permit an integer boolean to be bitcast to a pointer.
Adjacent comparison lowering already records the valid conversion shape:
zero-extend `i1` to the target native integer, then use `inttoptr`.

Do not weaken LLVM verification or replace the value with zero. A repair must
preserve the boolean value, handle the reverse pointer/integer neighbor where
applicable, and add exact plus adjacent lowering tests before retrying only the
failed shard.

The focused regression models a defined SSA value only. The observed
`env/paths` diagnostic IR also contains a separate upstream missing-store/value
loss defect; legal cast emission must not be used as evidence that that defect
is fixed.

## Verification

`llvm_bitcast_pointer_bool_spec.spl` passes all four focused examples in strict
interpreter mode: exact `i1 -> native-int -> ptr`, reverse `ptr -> i1`
truthiness, and adjacent `i64 -> ptr` / `ptr -> i64` conversions. Unsupported
value coercions now fail closed instead of falling through to `bitcast`.

This result closes only the LLVM cast-emission defect. It does not claim the
separate `env/paths` missing-store/value-loss defect, shard, or full Stage 4 is
fixed.
