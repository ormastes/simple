# C process spawn facades read Rust-owned text past its length (2026-11-21)

**Status:** CLOSED for `src/runtime/runtime_native.c` (PR #10636 spawn facades;
follow-up sweep of every remaining `rt_interp_cstr` site, see "Sweep" below).
The fix takes effect in a
compiler only after its runtime is rebuilt (next bootstrap). Binaries built
before the fix, including the integ22 Stage 2
(`.../bootstrap-s2probe-integ22/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
55,013,256 bytes, 2026-11-19 21:58, source pin `e1b8cc353599`), keep the defect.

## Symptom

The native codegen pool (`native_codegen_pool_v1.spl`) runs every llc job as
`/bin/sh -c "<llc argv> > job-N.log 2>&1"` through
`rt_process_spawn_session_value`. In a live Stage 2 run, 11 of 47 captured
`/bin/sh` command lines carried heap bytes after the real end of the line:
`2>&1}`, `2>&1}}}}`, `2>&17}}\``, `2>&1kind":{"Cop?`, `2>&1:"source"}}1`,
`2>&1ffi??`, ... (fragments of freed JSON text). sh failed ("Bad fd number",
"Unterminated quoted string") and the pool fell back to slow serial codegen.
The prefix was always intact; only bytes after `len` were wrong, 1-8 of them.

## Root cause (confirmed)

A seed-built compiler links the Rust `simple_runtime` with the C runtime as a
supplement. Symbol attribution in the Stage 2 binary (`nm` + `objdump`):

- `rt_string_concat` (0x2424168) is the Rust one: it calls
  `simple_runtime::value::collections::alloc_runtime_string`, which allocates
  `size_of::<RuntimeString>() + len` with **no trailing NUL**
  (documented in `src/compiler_rust/runtime/src/value/sffi/package.rs`).
- `rt_interp_cstr` (0x2423280) is the Rust one: `rt_string_data` + raw fallback.
- `rt_process_spawn_session_value` (0x250c2f4) is the **C** facade — the Rust
  runtime has no twin. It read every argument with
  `rt_interp_cstr(rt_array_get_text(args, i))` and handed the pointer to
  `execv` as a C string.

So `exec` copied each argument up to the first zero byte after `len`: whatever
the allocator's slack held. `native_codegen_command_line_v1` itself is correct.
Same class as `core_text_dup_abi` and
`stage2_windows_mixed_runtime_owner_array_handle_2026-11-12.md`.

## Fix

`rt_process_spawn_session_value`, `rt_process_spawn_async_value`,
`rt_process_spawn_guarded_value` and `rt_process_run_inherit_value` now copy
the command and each argument by its byte length (`rt_string_len` +
`core_text_dup_abi`) into owned NUL-terminated buffers and free them after the
spawn. A value with no counted length (a raw `char*`) keeps the old
NUL-terminated reading.

## Evidence

`src/runtime/test/process_spawn_value_counted_text_selfcheck.c` overwrites each
string's terminator in the pure-C runtime (the C allocation is `len + 1`, so the
write stays in bounds) to reproduce the Rust layout. Linked against the core-C
runtime sources:

- before: session spawn `pid=-2` (`/bin/sh}...` not found), async child
  `exit=127` — FAIL
- after: session child `exit=7`, async child `exit=9` — PASS

## Sweep (follow-up, closes the record)

Shared helpers in `runtime_native.c`: `rt_text_view_abi` (borrowed counted
view through the `rt_string_len`/`rt_string_data` ABI, raw `char*` falls back
to `strlen`), `rt_text_cstr_dup` (owned NUL-terminated copy, caller frees) and
`rt_text_cstr_into` (copy into a caller buffer). Every `rt_interp_cstr` site at
`origin/release/1.0.0` 8d850c22c54, classified:

| line | function | consumer | verdict |
|---|---|---|---|
| 888 | `rt_open_fd` | `open(2)` / `_wopen` | fixed: `rt_text_cstr_dup` |
| 4898 | `rt_interp_cstr` | definition | n/a |
| 5938, 5946 | `rt_text_eq_any` non-C operand | `strlen` -> `memcmp` | fixed: counted view (the `->len` branch was already safe) |
| 5973, 5974 | `rt_text_cmp_any` non-C operand | `strlen` -> `memcmp` | fixed: counted view |
| 8270 | `rt_string_to_int_any` raw branch | `strtoll` | fixed: counted view into bounded buffer |
| 9498, 9499 | `rt_strcat_tagged` non-C operand | `strlen` -> concat | fixed: counted view |
| 11690 | `spl_dynlib_snapshot_linux` | `open(2)` | fixed: `rt_text_cstr_dup` |
| 11746 | `spl_dlopen_checked` | `dlopen` | fixed: `rt_text_cstr_dup` |
| 11768 | `spl_dlsym_checked` | `dlsym` | fixed: `rt_text_cstr_dup` |
| 11785 | `spl_dlsym_process_checked` | `dlsym` | fixed: `rt_text_cstr_dup` |
| 17491 | `rt_env_get_value` | `getenv` | fixed: `rt_text_cstr_dup` |
| 19066 | old spawn helper raw fallback | raw `char*` by contract | already safe; helper replaced by `rt_text_cstr_dup` |
| 19098, 19111 | spawn argv builder | NULL-presence probe only, never dereferenced | already safe, left |
| 21099 | `rt_extract_cstr` (8 tcp/udp callers) | `strlen` / `inet_pton` | fixed: `rt_text_cstr_into` 256-byte buffer |
| (P2) | `rt_process_run_inherit` args | `exec` via `rt_string_data` | fixed: `rt_text_cstr_dup` per arg, freed |

Red/green: `process_spawn_value_counted_text_selfcheck.c` now has one case per
consumer class (exec x3, open, getenv, dlsym, strtoll, inet). Against the
pre-sweep runtime: 6 FAIL (`run_inherit exit=2`, `open fd=-1`, `getenv len=-1`,
`dlsym rc=3`, `int 127`, `udp bind accepted`); after: PASS, also under ASan with
leak detection. The `memcmp`/concat fallbacks are reachable only by a non-C
string, so the pure-C selfcheck covers their shared view through the `strtoll`
case (a text data pointer).

Not covered by this record (other compositions, same pattern, still open):
`runtime_dynload.c:2007,2063,2085,2102` (twin dlopen/dlsym owners) and
`runtime_renderdoc.c:129`.
