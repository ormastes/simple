# Pure-Simple LLVM shard emits invalid `bitcast i1` to `ptr`

- **Date:** 2026-08-03
- **Status:** OPEN — CLAIMED by the x86 Stage 4 root lane
- **Severity:** P1
- **Area:** pure-Simple LLVM MIR lowering
- **Likely owner:**
  `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl::translate_bitcast`
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

`translate_bitcast` currently emits a raw LLVM `bitcast` whenever source and
target types differ. LLVM does not permit an integer boolean to be bitcast to a
pointer. Adjacent comparison lowering already records the valid conversion
shape: zero-extend `i1` to the target native integer, then use `inttoptr`.

Do not weaken LLVM verification or replace the value with zero. A repair must
preserve the boolean value, handle the reverse pointer/integer neighbor where
applicable, and add exact plus adjacent lowering tests before retrying only the
failed shard.

## Scope boundary

This session records and claims the P1 blocker only. It intentionally makes no
source change for the cast and does not claim that the `env/paths` shard or
Stage 4 succeeds beyond this next LLVM verifier frontier.
