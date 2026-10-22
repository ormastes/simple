# Stage 4 live-request filter drops public runtime API that has no `rt_`/`spl_` prefix

- **Date:** 2026-10-20
- **Status:** open; worked around at the one live call site (`src/app/editor/tui_shell.spl`)
- **Where:** `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` `stage4_live_runtime_requests` (~:962-975), consumed by `build_stage4_runtime_capsule_archive`

## Symptom

Phase 4 full-CLI link (authorized entry, `SIMPLE_LINKER=lld`, all providers matched):

```
ld.lld: error: undefined symbol: stdin_read_char
>>> referenced by simple_module   (app__editor__tui_shell__editor_tui_run)
```

`stdin_read_char` is defined in `src/runtime/runtime_native.c:3125`, declared public in
`runtime.h:368`, and present in the core-C archive; 22 `.spl` modules declare it as a bare
`extern fn stdin_read_char() -> text`.

## Root cause

The Stage 4 profile keeps only the symbols the live projection *requests*, and the request
filter admits `rt_*`, `spl_*` and a short fixed list (`panic`, `stderr_write`, `stderr_flush`,
`__simple_runtime_*`, `__simple_call_module_inits`). `stdin_read_char` matches none, so it is not
requested, the capsule localizes it, and the final link fails on a symbol the archive does define.

## Workaround landed

`tui_shell.spl` reads one byte through `rt_stdin_read_chars_text(1)` (the prefixed entry point,
`runtime.h:367`). The 21 other declarations are dead in the CLI closure and GC away.

## Fix wanted

Either admit every name `runtime.h` exports (the header is the authority the C census already
uses) or rename the C entry point to `rt_stdin_read_char` and migrate the 22 declarations.
Until then any un-prefixed public runtime function that becomes live in a Stage 4 closure fails
the link with no hint that the archive actually owns it.
