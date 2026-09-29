# interpreter: `rt_print` unregistered in extern dispatch, exposed by `diag.spl` global shadow of `print_raw`

Date: 2026-08-31
Status: FIXED (this session) — `rt_print` registered in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`

## Symptom

`bin/simple.exe run src/app/mcp/main.spl` (and the interpreted test runner)
died with `error: semantic: unknown extern function: rt_print` and rc=1,
producing no JSON-RPC response at all. Reproduced on a 105 MB bootstrap-profile
seed built 2026-08-31 18:12 from a merge of `work/windows-bootstrap-msvc-rebased`
into `origin/main` (`2d03a48d87a`). An older 28 MB seed (built 2026-08-24, from
a base predating the merge) ran the same command fine.

## Root cause

`src/lib/nogc_sync_mut/sffi/diag.spl` (new file, landed in
`7b876e89edd feat(tools): rt_migrate rewrite tool + rt_alias_map`, present at
`origin/main`) declares:

```
extern fn rt_print(msg: text)

@always_inline
fn print_raw(msg: text):
    unsafe(capabilities: [ffi]):
        rt_print(msg)
```

The interpreter's function table is name-keyed and program-wide: as soon as
ANY transitively-imported module pulls in `diag.spl`, this real `fn print_raw`
SHADOWS the interpreter's builtin `print_raw` for the whole program (a
diagnostic already warns about this: "`fn print_raw` ... shadows the prelude
builtin `print_raw` and is being called INSTEAD of it"). Every ordinary call
to `print_raw(...)` (e.g. `src/app/mcp/main.spl:311`, writing the JSON-RPC
response) now runs this wrapper instead, which calls the literal extern name
`rt_print`.

`rt_print` is a real, registered codegen alias
(`codegen/instr/calls.rs:3111 "rt_print" => Some("rt_print_value")`,
`runtime/src/value/sffi/io_print.rs #[export_name = "rt_print"]`) — but it was
never added to the INTERPRETER's static extern dispatch table
(`interpreter_extern/mod.rs`), which only registered the higher-level builtin
names `print` / `print_raw` themselves, not the raw `rt_print` primitive they
compile down to. Ordinary Simple source never called `rt_print` directly
before `diag.spl` started wrapping it, so the gap was latent.

Dispatch path when `rt_print` is called from interpreted code
(`interpreter_sffi.rs:783`): names starting with `rt_` route to
`call_extern_function_with_values` (`interpreter_extern/mod.rs:3004`), which
has no `rt_print` entry, falls through every family-prefix arm, and reaches
`dynamic_sffi::try_call_dynamic` (`mod.rs` tail before `unknown_function` at
`mod.rs:3215`) — a dlopen/dlsym fallback that needs a `simple_runtime.dll`.
This Windows tree only produces a static `.lib` (`build/simple-core/simple_runtime.lib`,
`target/release/build/*/out/...`), never a `.dll`, so the dynamic fallback
cannot resolve it either, and the call dies with
`unknown extern function: rt_print`.

## Verdict: origin/main IS affected right now

`d150a169f26` (the tree exhibiting the bug) is a confirmed ancestor of
`origin/main`'s tip `2d03a48d87a` (`git merge-base --is-ancestor` true), and
`git show origin/main:src/lib/nogc_sync_mut/sffi/diag.spl` returns the exact
shadowing wrapper above. This is a genuine source-level regression, not a
build-profile artifact of the one 105 MB binary — the base checkout that
lacks `src/lib/nogc_sync_mut/sffi/diag.spl` entirely (it does not exist there)
does not exhibit the bug. Any interpreted run whose import closure reaches
`diag.spl` is affected; runs that don't (e.g.
`test/01_unit/lib/common/array_at_option_spec.spl`, verified green) are not.

## Fix

Registered `rt_print` in `interpreter_extern/mod.rs`'s dispatch table,
mapping to the existing `io::print::print_raw` handler (no-newline, mirrors
the `rt_print_value`/no-newline semantics of the codegen alias). Purely
additive: a `HashMap` entry for a name nothing could previously resolve, no
`cfg`, no platform branch — Linux/macOS previously fell through to
`try_call_dynamic`, which CAN find a real `.so`/`.dylib` there, so the added
entry only short-circuits an equivalent successful dynamic lookup on those
platforms; nothing is narrowed.

## Known adjacent gaps (NOT fixed here, same shadow mechanism)

`diag.spl` also wraps `rt_println`, `rt_println_value`, `rt_print_err`,
`rt_debug_exit_success`, and `rt_stdout_write` behind builtin-shaped names
(`println`, `eprintln`, ...). `rt_println` / `rt_println_value` /
`rt_stdout_write` are similarly absent from the interpreter dispatch table;
`rt_print_err` and `rt_debug_exit_success` have no implementation anywhere in
the tree at all (not just unregistered — genuinely unbacked). Any program
whose import closure reaches `diag.spl` AND calls the builtin `println` /
`eprintln` in interpreted mode will hit the same failure class the next time
its import graph changes. Left unfixed pending a dedicated pass; flagged here
so it isn't rediscovered as a surprise.
