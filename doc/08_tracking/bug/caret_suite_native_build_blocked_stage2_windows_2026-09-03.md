# Caret suite cannot native-build with the Phase-2 (Stage-2-admitted) Windows compiler

Date: 2026-09-03
Binary: `build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`
sha256 `fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86` (verified)
Env: `. scripts/setup/windows-msvc-bootstrap-env.shs` sourced.

All four caret-suite components fail `native-build`. None of the failures is in
the caret sources themselves except B5 (fixed here); the rest are stdlib /
compiler-frontend gaps in the Stage-2 compiler.

## Repro

```
simple.exe native-build src/app/llm_caret/main.spl              -o out.exe  # rc=1
simple.exe native-build src/app/llm_caret/agent_manager_view.spl -o out.exe # rc=1
simple.exe native-build src/app/slang_pack/main.spl              -o out.exe # rc=1
simple.exe native-build src/app/hosted_apps/smux_client.spl      -o out.exe # rc=1
```

## Root causes (distinct)

- **B1 parser: `@attr(...)` in a class body is rejected.**
  `[parser_error] line 136:5: unexpected token in class body` /
  `kind 171 text '@'` at `src/std/nogc_sync_mut/atomic.spl:136`
  (`@unsafe(reason: ..., capabilities: [ffi])` on a method). Blocks caret at
  phase 1 — caret never reaches HIR.
- **B2 HIR: `unresolved type: SqliteConnection`** in all five `src/app/io/*.spl`
  modules (`mod`, `cli_ops`, `env_ops`, `process_ops`, `process_env_ops`).
  Poisons `app.io.*`, which caret / agent manager / slang all import.
- **B3 HIR: `unresolved type: Id`** — 11 errors across
  `src/std/common/search/types.spl` and `ranking.spl`.
- **B4 HIR: `unresolved name: cwd`** at `src/std/nogc_sync_mut/cli/cli_util.spl:11:5`.
- **B5 HIR (caret source, FIXED here): `untyped function returns a value`** —
  `agent_manager_view.spl` `fn main():` ended with `return ()`. Removed the
  `return ()`; interpreter lane re-verified identical output afterwards.
- **B6 HIR: `unresolved type: int`** — 385 errors, 5 poisoned modules, across
  `src/os/apps/smux/{smux_remote,api,contract,service,buffer}.spl`. The bare
  `int` alias does not resolve in the Stage-2 frontend. Blocks smux entirely.
- **B7 diagnostics: `phase 3 FAILED (diagnostics unreadable: error array did not
  survive transport)`** printed on every HIR failure — the structured error
  array is lost between phases; only the `[hir-fatal]` trace lines are usable.

## Interpreter-lane defect found in the same pass

- **B8 `rt_stdin_read_line` boxed-result truncation panic.**
  `bin/simple.exe run src/app/hosted_apps/smux_client.spl < cmds` prints
  `smux_remote_main: service started, session=default` then PANICs:
  `rt_value_raw_i64: refusing to truncate a non-float heap-boxed InterpCall
  result (tag=1) to a raw i64` at `runtime/src/value/sffi/value_ops.rs:116`.
  Exit 127, crash report written. `rt_stdin_read_line() -> text?` returns a
  boxed optional that the JIT call path unboxes as i64.
  Related: `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`.
