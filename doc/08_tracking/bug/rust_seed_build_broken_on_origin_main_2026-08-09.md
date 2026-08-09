# Rust seed build broken at `origin/main` — two independent breaks (blockers 10 & 11)

Date: 2026-08-09
Status: **RESOLVED upstream — both fixes now present on origin/main** (verified
2026-08-09 later same day: `resolve_command_path(&cmd_str)` at
`env_process.rs:1223`, and both `"counterpart_abi_runtime.c"` /
`"runtime_packed_span.c"` present in the hosted C source list in
`src/compiler_rust/runtime/build.rs`). Landed by another lane independently of
this doc; unblocks a genuine bootstrap-from-scratch attempt for
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`.
Area: bootstrap / Rust seed / runtime build

Found while running an instrumented full bootstrap from a **clean pinned
checkout** of `origin/main` `63ee79be7ee` (`/home/ormastes/dev/simple-s3bisect`,
`git clean -xfd`, only CRLF noise in two `.bat` files). These are NOT
working-copy contamination — they reproduce from a pristine `origin/main`
checkout, and they block **every** full bootstrap on `main`.

## Blocker 10 — `simple-runtime` does not compile (E0308)

```
error[E0308]: mismatched types
   --> runtime/src/value/sffi/env_process.rs:1223:57
1223 |     let mut command = Command::new(resolve_command_path(cmd_str));
     |                                    -------------------- ^^^^^^^ expected `&str`, found `String`
error: could not compile `simple-runtime` (lib) due to 1 previous error
```

`resolve_command_path(cmd: &str) -> &str` (`:66`) has 9 call sites; 8 pass a
`&str` and compile. Only `:1223` passes the `String` returned by `ptr_string`.
Introduced by `48f49e11883` ("fix(windows): Vulkan DXVK/VKD3D probe, /bin/sh
process_run, fail_test builtin").

**Fix:** `resolve_command_path(&cmd_str)` at line 1223. One character.

## Blocker 11 — seed link fails, 18 undefined symbols

With blocker 10 fixed, the seed link fails:

```
rust-lld: error: undefined symbol: rt_counterpart_open
  >>> referenced by simple_compiler::interpreter::interpreter_extern::call_extern_function_with_values
... (18 total)
error: could not compile `simple-driver` (bin "simple")
```

Full symbol list, two families:

- `rt_counterpart_{open,close,invoke,reset,probe_abi,manifest_text,response_text,trace_text,last_error_text}` (9)
- `rt_packed_span_v1_{resolve_raw,resolve_count,struct_size,flags_bits,probe_verdict,last_verdict,last_rejection,admitted_element_count,rejected_count}` (9)

The C implementations **exist in the tree** — `src/runtime/counterpart_abi_runtime.c`
(`rt_counterpart_open` at `:449`) and `src/runtime/runtime_packed_span.c` — but
neither is listed in the seed runtime's C source list in
`src/compiler_rust/runtime/build.rs` (~line 137). The Rust seed's
`interpreter_extern` layer references them, so the link fails.

This is the same omission class as the `rt_opengl_*` / `rt_oneapi_*` lane already
documented in a comment immediately below that list in the same file.

**Fix:** add `"counterpart_abi_runtime.c"` and `"runtime_packed_span.c"` to the
hosted C source list in `src/compiler_rust/runtime/build.rs`.

**Do NOT add `counterpart_worker_runtime.c`** — it is a standalone worker
translation unit, it provides none of the missing symbols, and adding it fails
the build outright:

```
src/runtime/counterpart_worker_runtime.c:39:10: fatal error: simple_counterpart_abi.h: No such file or directory
```

(verified empirically: added, build failed, removed, build succeeded).

## Verification

With both fixes applied locally, the seed built, and the bootstrap reached
**Stage 2 GREEN** and ran **Stage 3 to a verdict** — see
`placeholder_lambda_fix_missed_driver_native_build_parse_path_2026-08-09.md`.

## Note

Both fixes are Rust-seed/build-system changes and were applied only in the
pinned bisect checkout to unblock measurement. They are genuine forward fixes to
an outright-broken `main` (not workarounds for any `.spl` defect) and should be
landed by whoever owns the two originating lanes.
