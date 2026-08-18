# `rt_file_open` — extern-ABI oracle declares 4 args; the only definition takes 3

**Date:** 2026-08-17
**Status:** FIXED 2026-08-17 (this row) — `runtime_sffi.rs:1888` corrected to 3
args; `extern_abi_spl_backend_arity_mismatches=0`. The gate as a whole is still
RED, but on 8 DIFFERENT rows in its second half that were previously never
reached — see "Resolution" below.
**Family:** `doc/08_tracking/bug/rt_extern_abi_divergence_family_2026-08-10.md`
**Found by:** os/runtime bug lane, while reproducing
`rt_dir_list_platform_header_collides_with_extern_2026-08-10.md` (that row is now
FIXED; this is the *different* defect the same gate is actually failing on).

## RED evidence (measured)

```
$ sh scripts/check/check-extern-abi-signatures.shs
$ rc=$?     # taken on the line AFTER the command, never through a pipe
exit=1
...
extern_abi_spl_backend_arity_mismatches=2
rt_file_open	4	3	llvm_backend.spl
rt_file_open	4	3	llvm_lib_translate.spl
FAIL — 289 pure-Simple backend declarations checked, 2 arity mismatch(es)
```

Binary identity is irrelevant here — the gate is a pure source scan and invokes
no `bin/simple`.

## The defect: the gate is measuring against the wrong oracle

The gate's message says "Fix the list to match
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`". But `runtime_sffi.rs`
is the side that disagrees with reality:

| where | signature | args |
|---|---|---|
| `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1888` (the oracle) | `&[I64, I64, I64, I64] -> &[I32]`, commented `// path, mode -> fd` | **4** |
| `src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs:19` (**the only definition anywhere**) | `(path_ptr: *const u8, path_len: u64, mode: i32) -> i32` | **3** |
| `src/compiler/70.backend/backend/llvm_backend.spl:386` | `declare i32 @rt_file_open(ptr, i64, i32)` | 3 |
| `src/compiler/70.backend/backend/llvm_lib_translate.spl:286` | `llvm_function_type(i32_ty, [ptr_ty, i64_ty, i32_ty], false)` | 3 |
| `src/runtime/runtime_native.c:9664-9665` (comment, C lane) | documents the compiler as declaring `i32 rt_file_open(const uint8_t* path, uint64_t path_len, i32 mode)` | 3 |

Searched for a C definition: `/usr/bin/grep -rn 'rt_file_open[ ]*(' src/runtime/
--include=*.c --include=*.h` (excluding `rt_file_open_stream`) returns **nothing**.
`src/runtime/simple_core/` has none either. So `descriptor.rs` is the sole
implementation, and it takes 3 arguments with `mode` as a plain `i32` enum code —
not a `(ptr, len)` text pair.

**Three independent declarations plus the runtime's own C comment agree on 3.
`runtime_sffi.rs` alone says 4.** The `// path, mode -> fd` comment reads as
someone assuming `mode` was a text and expanding it to `(ptr, len)`; the
implementation was never changed to match.

Consequence if `runtime_sffi.rs` is what the Rust codegen actually emits: a
call site pushes a 4th argument the callee never reads (harmless on SysV, where
the extra register is simply ignored) — but the *declared* return/param shape
diverges, and any future ABI that passes the 4th slot on the stack, or any
`-Wl`/LTO type check, turns this into a real mismatch. More immediately, it keeps
the extern-ABI gate permanently RED and short-circuiting, which is why the
`470 symbols checked` C-header half of that gate **currently never runs at all** —
a whole class of C-header collisions (exactly the `rt_dir_list` class) is being
silently skipped.

## Fix direction — NOT applied here

The one-line fix is in `runtime_sffi.rs:1888`:
`&[I64, I64, I64, I64]` -> `&[I64, I64, I32]` (or `&[I64, I64, I64]`, matching how
sibling 3-arg specs encode a small int), and correct the comment to
`// path_ptr, path_len, mode -> fd`.

Not applied by this lane: `src/compiler_rust/**` is owned by another lane in this
campaign and is explicitly off-limits. Do **not** "fix the list" in the two
pure-Simple backends as the gate message suggests — they are the correct side, and
padding them to 4 args would make them diverge from the only real implementation.

## Resolution (2026-08-17, applied)

Applied exactly the one-line fix above, in `runtime_sffi.rs:1888`:

```rust
-    RuntimeFuncSpec::new("rt_file_open", &[I64, I64, I64, I64], &[I32]), // path, mode -> fd
+    RuntimeFuncSpec::new("rt_file_open", &[I64, I64, I32], &[I32]), // path_ptr, path_len, mode -> fd
```

Binary identity of the tree at the time (the gate itself does not use it):

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000
```

Gate re-run (rc read on the line after the command, not through a pipe):

```
$ sh scripts/check/check-extern-abi-signatures.shs
$ rc=$?
exit=1
extern_abi_spl_backend_arity_mismatches=0      <-- was 2; this bug's row is gone
extern_abi_mismatches_current=22
extern_abi_mismatch_new=rt_db_delete	2	3	runtime_db.c
extern_abi_mismatch_new=rt_db_get	2	3	runtime_db.c
extern_abi_mismatch_new=rt_dir_glob	2	4	directory.rs
extern_abi_mismatch_new=rt_file_find	4	5	directory.rs
extern_abi_mismatch_new=rt_invlpg	ret:int	ret:void	runtime_native.c
extern_abi_mismatch_new=rt_struct_alloc	ret:int	ret:ptr	runtime_memory.c
extern_abi_mismatch_new=rt_struct_alloc	ret:int	ret:ptr	runtime_native.c
extern_abi_mismatch_new=rt_write_cr3	ret:int	ret:void	runtime_native.c
FAIL — 510 symbols checked, 8 new mismatch(es)
```

`rt_file_open` no longer appears anywhere in the output, and the second half of
the gate (510 symbols, the C-header/definition comparison) now RUNS for the first
time — exactly the consequence this record predicted. The 8 rows it reports are
**not** introduced by this change: the earlier run exited during the arity half
and never reached this code path. They are a separate, larger defect class and
are NOT fixed here.

**No `src/runtime/*.c` file was touched by this change**, so
`check-c-runtime-compiles-push.shs` was not applicable to it.

## Not verified

- Whether the Rust LLVM codegen materially mis-emits the call today (needs a
  rebuilt seed and a real `rt_file_open` call through the native path). The
  divergence is proven statically; the runtime consequence is inferred.
- The `470 symbols checked` C-header half of the gate has not been observed
  passing or failing at HEAD, because the gate exits before reaching it.
