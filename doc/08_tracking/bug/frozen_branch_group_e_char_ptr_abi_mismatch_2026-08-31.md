# Frozen bootstrap branch carries char*-ABI Group E exports (tagged-value callers)

- **Date:** 2026-08-31
- **Status:** OPEN — blocked on the running bootstrap in `C:\Users\ormas\dev\simple-rebase` (must not be touched while it runs)
- **Severity:** HIGH (latent garbage-read / crash class, not a link failure)

## Defect

`simple-rebase`'s `src/runtime/runtime_core_exports.c` (Group E of
`doc/08_tracking/bug/stage2_windows_unresolved_inventory_2026-08-31.md`)
defines four of its seven symbols with `const char*` text arguments/returns,
copied from `runtime.c`:

- `rt_readdir(const char* path)` — text ARG wrong
- `rt_mkdir(const char* path, i64)` — text ARG wrong
- `rt_readdir_entry(...) -> const char*` — text RETURN wrong
- `rt_shell_output(const char*) -> const char*` — ARG and RETURN wrong

None of the 19 Stage-2 export names appears in `text_arg_indices`
(`src/compiler/50.mir/text_extern_abi.spl` or the Rust twin
`codegen/instr/calls.rs`), so every native backend passes a `text` argument
as ONE **tagged runtime value** and reads a `text` return as a tagged value
(precedent: `rt_file_read_text_rv(path: RuntimeValue) -> RuntimeValue`,
`runtime/src/value/sffi/file_io/file_ops.rs`). The branch TU therefore
receives a tagged value where it expects a NUL-terminated `char*`
(strlen/opendir on tag-encoded heap data) and hands back a raw `char*`
where the caller expects a tagged value. The actual unresolved-symbol
callers are generated modules (`mod_767`:
`lib__nogc_async_mut__io__file__AsyncDir.readdir` etc.), i.e. exactly the
tagged convention. The branch's io TU additionally lacks the fixes listed
below.

## Fixed in MAIN (this record's sibling commit `c3d9a4a9`)

- `src/runtime/runtime_core_exports.c` — tagged ABI for all four, UTF-8 ->
  UTF-16 wide Windows APIs, urandom EINTR/short-read loop.
- `src/runtime/runtime_core_io_exports.c` — wide APIs (`_wstat64`,
  `FindFirstFileW`; ACP 65001 on the dev host masked the ANSI failure),
  EINTR-on-stdin fix, snprintf-truncation guards.
- `src/runtime/runtime.c` + `runtime.h` — same family converted to the
  tagged ABI (this file is compiled wholesale by the pure-Simple backend
  lane, `70.backend/backend/runtime_compiler.spl`, so its char* versions
  were the same live bug in that lane).
- `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` — E TU
  wired into the seed core-C list (nm re-verified: 1007 defined symbols
  across all 19 list members incl. conditional ones, zero overlap).
- Behavioural tests: `src/runtime/test/rt_core_exports_behaviour_selfcheck.c`
  (72 assertions green + fresh-process stdin/term cases).

## Unblock condition

When the `simple-rebase` bootstrap completes: re-sync both TUs (and the
`runtime.c`/`runtime.h`/`tools.rs` deltas) from MAIN into the branch before
any further stage relink, then rerun the selfcheck driver there. Until
then, any stage2+ binary produced on the branch has the wrong ABI on these
four symbols; if `AsyncDir.readdir`/`AsyncFile.write_all`/shell-capture
paths execute, expect garbage or SIGSEGV, not an error message.

## Why the reproducing test is a C driver, not a `.spl` spec

A Simple spec cannot reach these TUs: `bin/simple test` runs the Rust-seed
interpreter, whose shims (`interpreter_extern/file_io.rs`,
`mod.rs:275` aliasing `rt_string_from_byte_array` to the Rust
`rt_bytes_to_text`) are a DIFFERENT implementation, and the native lane
that does link the TUs is the broken Stage-2 lane this work exists to fix.
The C driver links the exact objects under test.
