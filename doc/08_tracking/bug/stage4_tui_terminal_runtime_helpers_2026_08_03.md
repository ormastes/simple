# Stage 4 TUI terminal runtime helper resolution

Status: focused repair verified; full x86 cycle 3 pending
Severity: P1 bootstrap blocker
Owner: pure-Simple nogc_sync_mut TUI terminal facade
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `59f07b4fb3b`

## Exact failure

The third and final focused HIR compile of the real DevHub wiki closure proved
the process-import and JSON-facade blockers absent, then advanced into
`src/lib/nogc_sync_mut/tui/terminal.spl`. Phase 3 failed on unresolved
`print_raw` (twice), `len`, and `substring`.

The focused command exited 1 after 3.02s at 180,444 KiB max RSS. No Stage 4
candidate or deployment exists.

Retained evidence:

- `build/focused/stage4-json-root-facade/cmd-wiki.log`
- `build/focused/stage4-json-root-facade/contract.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle2.log`

## Focused repair audit

Three pure-Simple focused variants were evaluated and then removed:

1. An explicit established `print_raw(text) -> i64` declaration plus
   `content.len()` and `content.substring(...)` cleared the local HIR errors,
   but staged MIR could not resolve the substring method.
2. Slice syntax lowered to the same unsupported MIR `slice` method.
3. Calling `std.common.string_core.str_slice` directly cleared the local slice
   path but expanded the full string-core closure, which then failed on its
   unrelated staged-MIR `join` and `merge` methods.

Per the three-attempt guard, no fourth focused variant or full cycle 3 was run.
The unverified production edits were restored; this claimed bug and its logs
are the handoff for a fresh, scoped session.

## Fresh-session repair

The owner-local repair explicitly declares the established typed `print_raw`
language ABI and consumes its result. It replaces the unresolved global
`len`/`substring` calls with `_terminal_fit_line`, using the Stage 4-safe
indexed `content.len()` plus `content.char_at(i)` pattern to truncate and pad.
It deliberately avoids `for ch in text`, which has a recorded bootstrap-native
element-corruption bug. It adds no raw `rt_*` shortcut and does not import the
broader string-core closure.

Focused fixture:

- `test/03_system/native/stage4_tui_terminal_helper_contract.spl`
- Exact assertion: `"abcdef"`, width `3` produces `"abc"`.
- Adjacent assertions: width padding remains exact, zero width is empty, and a
  complete UTF-8 code point is preserved.

The first fresh-session variant used `for ch in content` and compiled and ran
for ASCII, but independent lower-model review found the recorded staged-native
text-iteration corruption in
`src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`. That variant was
rejected before commit. The accepted indexed variant matches the established
safe loop in `text_layout/font_renderer.spl`.

The final focused LLVM/core-C-bootstrap build reused the isolated cache,
compiled two modules with one cache hit, and linked successfully in 1.82s at
157,184 KiB max RSS. The executable exited 30, emitted the exact bytes `abc`,
and wrote no stderr. This directly exercised `_terminal_fit_line`,
`terminal_write`, `terminal_flush`, and the typed `print_raw` path.

Retained evidence:

- `build/focused/stage4-tui-terminal/contract-attempt2.log`
- `build/focused/stage4-tui-terminal/contract-attempt2.stdout`
- `build/focused/stage4-tui-terminal/contract-attempt2.stderr`

## Required regression evidence

1. A focused TUI terminal HIR/SMF route resolves all four helper calls.
2. An adjacent terminal operation retains its existing behavior or compile
   contract.
3. Do not rerun the capped DevHub wiki oracle. The final full-resource x86
   Stage 4 run is cycle 3/3.

## Cycle accounting

- Cycle 1/3: lint enum collision, repaired.
- Cycle 2/3: wiki process import plus JSON root facade blockers repaired; this
  TUI helper blocker was exposed by the capped focused route before cycle 3.
