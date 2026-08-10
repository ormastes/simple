# `rt_dir_list` C platform-header helper collides with the real extern

**Date:** 2026-08-10
**Status:** OPEN — gate is RED at origin because of this row
**Family:** `doc/08_tracking/bug/rt_extern_abi_divergence_family_2026-08-10.md`

## Symptom

`scripts/check/check-extern-abi-signatures.shs` reads
`FAIL — 470 symbols checked, 2 new mismatch(es)` at origin
(`d008ebb8260`), on:

```
extern_abi_mismatch_new=rt_dir_list	ret:int	ret:ptr	platform_win.h
extern_abi_mismatch_new=rt_dir_list	ret:int	ret:ptr	unix_common.h
```

This is NOT a regression of the extern-ABI campaign; the campaign's own
baseline is clean at 14 rows. It is a new divergence introduced with the
`src/runtime/platform/` headers.

## What is actually wrong

Three declarations of one global symbol, and they do not agree:

| where | signature |
|---|---|
| `runtime_sffi.rs:1894` (what the compiler emits) | `(I64, I64) -> I64` — `(ptr, len)` text ABI, returns a RuntimeValue array |
| `runtime/src/value/sffi/file_io/directory.rs:40` | `(*const u8, u64) -> RuntimeValue` — agrees with the compiler |
| `src/runtime/platform/unix_common.h:98`, `platform_win.h:110` | `const char** rt_dir_list(const char* path, int64_t* out_count)` |

The C headers define this **non-`static`**, so it is a global symbol, and its
only caller is the C-internal `runtime.c:1875`. It is plainly meant as a private
platform worker, not as the extern.

## Why this is worse than an arity row

The second parameter changes *meaning*, not just width. The compiler passes a
**length** (`u64`); the C definition treats that same register as an
**`int64_t*` out-pointer and writes through it**. Under `-z muldefs` the winner
is decided by link order, so on any link where the C copy wins, a call to
`rt_dir_list` stores the entry count to an address formed from a string length —
a wild write, plus a `const char**` returned where the caller decodes a tagged
RuntimeValue. This is the same shape as the `rt_file_close` /
`fclose((FILE*)3)` SIGSEGV closed in `fb1208c6980`, which was found the same way.

## Fix

The established precedent in this family: rename the private C worker so it
cannot collide, exactly as `rt_file_open_stream` / `rt_file_close_stream` were
renamed. Suggested `rt_dir_list_entries`, touching three places only —
`unix_common.h:98`, `platform_win.h:110`, and the caller `runtime.c:1875`.
`rt_dir_list_free` needs no change (no extern of that name exists).

Then recompile every runtime TU under `-Werror=int-conversion
-Werror=incompatible-pointer-types -Werror=implicit-function-declaration`, and
the gate should return to `PASS — 470 symbols checked, 14 baselined, 0 new`.

## Why this was filed rather than fixed

The `src/runtime/platform/` headers were added by a concurrent session that was
still mid-flight on them at the time this was found. Editing files another live
session owns is how this same afternoon produced a 133-file clobber; the rename
is small and unambiguous, so it is recorded here for that session to apply
rather than raced.
