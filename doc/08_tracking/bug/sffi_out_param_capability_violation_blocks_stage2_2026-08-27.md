# `ec6a500b42` breaks every Stage-2 build: `&mut` out-param fails the capability checker

**Date:** 2026-08-27
**Area:** `src/lib/nogc_sync_mut/sffi/dynamic.spl`
**Offending commit:** `ec6a500b42` "perf(sffi): remove checked i64 result allocation" (2026-08-26)
**Status:** OPEN — confirmed by a controlled A/B, fix not yet chosen

## Symptom

`native-build` of `src/app/cli/bootstrap_main.spl` (the Stage-2 build) aborts on
ONE file, taking the whole build with it:

    FAILED FILES (1):
      - src/lib/nogc_sync_mut/sffi/dynamic.spl => hir: Capability error:
        Aliasing violation: reference 2 already has Exclusive capability,
        cannot acquire Exclusive
    Build failed: native-build aborted: 1 file(s) failed to compile

## Cause

`ec6a500b42` replaced an allocating `[status, value]` array transport with a
raw out-parameter:

    -    val result = _sffi_call_i64_raw_checked(self.fptr, args)
    -    if result.len() != 2:
    -        return Err("E-SFFI-017: corrupt checked transport result: {self.symbol}")
    -    val status = result[0]
    +    var value: i64 = 0
    +    val status = _sffi_try_call_i64_out(self.fptr, args, &mut value)

and declared `_sffi_try_call_i64_out(fptr: i64, args: [i64], out_value: *mut i64)`
with `capabilities: [ffi, raw_ptr]`. The capability checker rejects the `&mut
value` borrow at the call site. A perf change that removed one allocation also
removed the ability to build the compiler.

**It is NOT the `4edef8fab8` clobber** — the file is 553 lines against 554
pre-snapshot. It is a fresh regression.

## Evidence — controlled A/B, same tree, one file reverted

| tree | result |
|---|---|
| origin tip as-is | `FAILED FILES (1)` … `Aliasing violation`, build aborted |
| **only `dynamic.spl` reverted to `ec6a500b42~1`** | **`Build complete: 770 compiled, 0 cached, 0 failed`**, binary linked (28,882 KB), 797.8s compile + 75.8s link |

Nothing else was changed between the two runs, so the attribution is exact.

### A probe that does NOT discriminate — recorded so it is not repeated

Compiling the file standalone (`simple compile <file> --format=smf`) fails on
BOTH sides with `Undefined("undefined identifier: runtime_file_rename")` — an
out-of-context artifact that never reaches the capability check. Reading that
shared failure as "both broken" would be wrong. Only the full native-build
discriminates.

## Why no gate caught it

`check-c-runtime-compiles-push.shs` covers C only. No mandatory gate compiles
the Simple stdlib through a real Stage-2 native-build before a push, so a change
that is syntactically fine and semantically rejected lands green. This is the
same shape as the 2026-08-11 seed incident, one layer up.

## Fix options (not yet chosen)

1. Keep the out-param and satisfy the checker (hoist the borrow, or give the
   callee a shared-reference contract).
2. Revert to the array transport and find the allocation win elsewhere.

Option 2 is proven to build. Option 1 preserves the perf intent but is unproven
— do not assume it type-checks without running a full Stage-2 build.
