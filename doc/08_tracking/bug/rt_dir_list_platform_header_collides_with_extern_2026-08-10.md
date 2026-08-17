# `rt_dir_list` C platform-header helper collides with the real extern

**Date:** 2026-08-10
**Status:** RESOLVED 2026-08-17 — the rename this doc requested was applied
(worker is `rt_dir_list_cpath` in both `unix_common.h:108` and
`platform_win.h:120`, with in-header comments explaining the old collision).
`scripts/check/check-extern-abi-signatures.shs` no longer emits any
`rt_dir_list` mismatch row (verified 2026-08-17; the gate's residual FAIL is
10 unrelated pre-existing rows — `rt_db_get/delete`, `rt_dir_glob`,
`rt_file_find`, `rt_file_open` in `descriptor.rs`, `rt_invlpg`,
`rt_process_run_with_limits`, `rt_struct_alloc`, `rt_write_cr3` — same family,
separate work). Regression specs (green):
`test/01_unit/runtime/rt_dir_list_header_no_collision_spec.spl` (repro +
renamed-worker generalization) and mirror
`test/unit/runtime/rt_dir_list_header_no_collision_spec.spl`. Related fix same
day: the pure-Simple backends' 3-arg `rt_file_open` declaration was corrected
to the 4-arg (ptr,len,ptr,len) ABI in `llvm_backend.spl:386` and
`llvm_lib_translate.spl:286`, gated by
`test/01_unit/compiler/backend/rt_extern_decl_arity_spec.spl` (+ mirror).
**Status:** FIXED — verified by content grep 2026-08-17 (os/runtime lane). The
suggested rename landed as `rt_dir_list_cpath` (not `rt_dir_list_entries`), and a
real `rt_dir_list` extern now exists in C:

- `src/runtime/platform/unix_common.h:108` — `const char** rt_dir_list_cpath(const char* path, int64_t* out_count)`
- `src/runtime/platform/platform_win.h:110` — same rename, same comment block
- `src/runtime/runtime.c:2206` — `int64_t rt_dir_list(const uint8_t* path_ptr, uint64_t path_len)`,
  which matches `runtime_sffi.rs:1877` `RuntimeFuncSpec::new("rt_dir_list", &[I64, I64], &[I64])` exactly.
- `/usr/bin/grep -rn "rt_dir_list" src/runtime/` shows **one** non-static global
  `rt_dir_list` definition; no C copy takes an out-pointer any more.

**The "gate is RED because of this row" claim has DECAYED and is no longer true.**
Re-ran `sh scripts/check/check-extern-abi-signatures.shs` (exit 1, read off the
line after the command, not through a pipe): the failure is now
`FAIL — 289 pure-Simple backend declarations checked, 2 arity mismatch(es)` on
`rt_file_open 4 vs 3` in `llvm_backend.spl` / `llvm_lib_translate.spl`. The run
short-circuits at that earlier pure-Simple-declaration check and **never emits the
`470 symbols checked` C-header comparison at all**, so it neither confirms nor
denies this row — the content grep above is what closes it. The new RED is filed
separately as `rt_file_open_arity_oracle_disagrees_with_only_definition_2026-08-17.md`.
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
