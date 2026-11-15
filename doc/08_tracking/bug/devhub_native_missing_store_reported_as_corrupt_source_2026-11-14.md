# Native devhub reports a missing SQLCipher store as `corrupt-source`

**Status:** verification-pending
**Found:** 2026-11-14
**Severity:** P2 — wrong error class, native only; still fails closed (exit 2, nothing leaked)

## Symptom

With the messenger config pointing at a file that does not exist:

```
interpreter: {"target":"","action":"rooms","status":"error","code":2,"error":"config_error: source-unavailable","warnings":[]}
native:      {"target":"","action":"rooms","status":"error","code":2,"error":"config_error: corrupt-source","warnings":[]}
```

## Root cause

`rt_file_read_bytes` is declared `-> [u8]?`. The Rust runtime returns nil on
failure. The C runtime linked into native binaries
(`src/runtime/runtime_native.c`) returned a raw `0`, and a `0` word is not nil.
So natively a missing file read back as present with zero bytes:
`file_read_bytes_result` said `Ok` (length 0), and the SQLCipher open then
failed the "whole number of pages" check and reported `CorruptSource` instead of
`Io`. The error-variant matching in
`src/app/devhub/messenger/adapter/db_common.spl` was never at fault.

## Fix

The six failure returns of `rt_file_read_bytes` in `src/runtime/runtime_native.c`
return `rt_core_nil()`, as `rt_file_mmap_read_bytes` already did.

## Evidence

Minimal repro (read a missing path, test the result five ways), native, Windows,
llvm-mingw 20260922:

```
before: unsafe_block=not-nil plain_val=not-nil typed_val=not-nil match=some len=0 present=present
after:  unsafe_block=nil     plain_val=nil     typed_val=nil     match=none       present=absent
after, existing file: unsafe_block=not-nil plain_val=not-nil present=present
```

Regression spec `test/01_unit/compiler/missing_file_read_bytes_native_spec.spl`:
interpreted `Results: 3 total, 3 passed, 0 failed`.

`sh scripts/check/check-c-runtime-compiles-push.shs` on this Windows host:
`runtime_native.c` is among the 338 files that compile clean. The gate's overall
verdict here is FAIL for 15 other files this change does not touch (ARM NEON /
SVE / RVV vector providers, baremetal `.inc.c`, POSIX file-lock tests,
`runtime_sqlite_demand.c`).

Native devhub rebuilt with the fixed seed and runtime:

```
DEVHUB_NATIVE_BIN=<abs>/build/nb/devhub_g.exe simple test test/03_system/app/devhub/messenger/messenger_read_verbs_damaged_store_spec.spl
```

```
seed 97728d94d5f devhub (before): Results: 7 total, 6 passed, 1 failed
fixed build devhub (after):       Results: 7 total, 7 passed, 0 failed
interpreted:                      Results: 7 total, 7 passed, 0 failed
```

The new regression spec has not been run through a native test lane; its native
evidence is the minimal repro.
