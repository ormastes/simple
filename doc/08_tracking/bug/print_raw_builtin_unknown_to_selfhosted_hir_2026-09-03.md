# `print_raw` is a Rust-seed builtin the self-hosted HIR does not know

- Date: 2026-09-03
- Status: OPEN
- Platform: platform-independent (measured on Windows x86_64-pc-windows-msvc)
- Severity: poisons `std.tui.terminal`, which cascades into any app using it

## Observed

`native-build src/app/devhub/main.spl` with the admitted Stage 2 compiler
(sha256 `fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86`),
exit status read directly on the next line, never through a pipe:

    src/lib/nogc_sync_mut/tui/terminal.spl:38:14 unresolved name: print_raw
    src/lib/nogc_sync_mut/tui/terminal.spl:38:14 unresolved name: substring
    src/lib/nogc_sync_mut/tui/terminal.spl:38:14 unresolved name: len

Line 38 is `print_raw(data)` inside `_terminal_stdout_write`. The `substring`
and `len` errors carry the SAME span and are very likely cascade from the one
failed call lowering, not three independent gaps.

## Root cause

`print_raw` is a builtin of the **Rust seed** only:
`src/compiler_rust/common/src/runtime_symbols.rs:184` and
`src/compiler_rust/compiler/src/codegen/instr/core.rs:774-783`.

`/usr/bin/grep -rn print_raw src/compiler/20.hir/` returns **zero** lines, and
`grep -rl '"print_raw"' src/compiler/` returns **zero files** — the self-hosted
front end has no such builtin at all. The comment at
`src/lib/nogc_sync_mut/tui/terminal.spl:33-36` asserts it is "the portable
language builtin"; that is true of the seed and false of the self-hosted
compiler.

## Cascade

`terminal.spl` is poisoned and DROPPED, so `terminal_stdout_is_tty` (defined at
`terminal.spl:72`) then comes out `unresolved name` in
`src/app/devhub/output.spl:18` — 2 further errors that disappear on their own
once this one is fixed.

## Fix direction (not attempted)

Either register `print_raw`/`eprint_raw` in the self-hosted builtin tables
alongside `print`/`println`, or change `_terminal_stdout_write` to an
`extern fn` call that both front ends back. The first keeps the seed and
self-hosted surfaces equal and is preferred; it needs a stage2 redeploy to
verify, which is blocked separately.

## Cross-platform

No platform-specific content — a missing front-end builtin, identical on Unix.
