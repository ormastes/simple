# `print_raw` is a Rust-seed builtin the self-hosted HIR does not know
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-03
- Status: CLOSED 2026-11-06 — `terminal.spl` now declares `extern fn print_raw(data: text) -> i64` (200debf89df), backed by `src/runtime/runtime_native.c` `print_raw`; resolves as an ordinary extern in the self-hosted HIR. **Closure re-verified 2026-11-11 by lane compiler6 — see the addendum at the end of this file.**
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


## Verification addendum 2026-11-11 — lane compiler6 (STALE, closure confirmed)

Lane compiler6 re-verified the 2026-11-06 closure on the tracked fresh seed
(`bin/simple.exe`, build 46fe8f6b6def, seed-smoke):

1. Fixing commit `200debf89df9` ("fix(io): bind Vulkan raw owner and terminal
   print ABI", 2026-10-04) is in this branch's history; its diff adds
   `extern fn print_raw(data: text) -> i64` to
   `src/lib/nogc_sync_mut/tui/terminal.spl` (present today at line 38).
2. Runtime backing exists: `src/runtime/runtime_native.c:4031`
   `int64_t print_raw(int64_t value)`.
3. Seed-lane execution evidence: a spec importing
   `std.tui.terminal.{terminal_get_size, terminal_stdout_is_tty}` and calling
   both (the latter is the devhub/output.spl:18 cascade casualty the record
   named) runs GREEN — `outcome=OK, 1 passed, 0 failed`. The module is not
   poisoned; the extern declaration coexists with the seed's print_raw
   builtin and the named collateral resolves.

Limitation: the self-hosted HIR native-build lane the record originally
measured on (devhub entry-closure) requires a stage2 deploy this lane is not
granted; the structural evidence (extern declaration + runtime symbol) plus
the seed-lane GREEN are the verification this lane can stand up. No code
change was needed; the record's CLOSED status stands.
