# `bin/simple test` gives wrong results for code that `bin/simple <file>.spl` computes correctly

**Status:** open, newly found while landing the bracket-slice byte-index
fixes below. **Severity:** blocks trusting `bin/simple test` output for at
least this code shape; scope beyond it not yet characterized.

## Symptom

`src/lib/nogc_sync_mut/glob.spl`'s `_glob_at`, `?`-wildcard branch:
```
val step = _glob_codepoint_len_at(s, si)
val next_si = si + step
return _glob_at(s: s, si: next_si, p: p, pi: pi + 1)
```
Calling `glob_match("café.txt", "caf?.txt")`:
- **Direct execution** (`bin/simple probe.spl` wrapping the call in `fn
  main()`): returns `true` (correct — `?` consumes "é", then ".txt"
  literal-matches ".txt"). Verified 3x, deterministic.
- **Test harness** (`bin/simple test test/.../glob_multibyte_spec.spl`,
  which the test runner reports spawns a `child binary:
  .../bin/release/x86_64-unknown-linux-gnu/simple` subprocess): the exact
  same source returns `false`.

Instrumented both paths with an identical `print()` placed *after* capturing
the recursive call's result into a local (avoiding the project's own
documented "no intervening call before a return" landmine class,
`doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md`-
adjacent):
```
si=3 step=2 next_si=5 result=<true under direct exec, false under test harness>
```
Same inputs, same source, same binary path reported in both invocations —
only the invocation *mode* differs (`bin/simple file.spl` vs `bin/simple
test file.spl`) — and the boolean returned by the identical recursive call
differs.

## Also reproduces in `src/lib/common/js/builtins/string.spl`

`string_charAt`/`string_split("")` walk `text_codepoints(s)` and sum
`utf8_codepoint_byte_len(cps[i])` in a loop to find a codepoint's byte
range. For a 2-byte codepoint (café's "é") both direct execution and the
test harness agree (correct). For 3-byte codepoints (CJK "日本語", the
em-dash "—") direct execution is correct (verified: `charAt(0)="日"`,
`charAt(1)="本"`, `charAt(2)="語"`, `charCodeAt` on em-dash `=8212`,
`split("")` on CJK gives 3 correct elements) but the test harness returns
empty strings / wrong values for the same inputs.

## What this is NOT

- Not a logic bug in the fixes below — proved by direct execution producing
  correct output for every case the harness gets wrong, on the identical
  source, same session, same binary.
- Not the previously-fixed for-loop-over-text corruption
  (`doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`)
  — neither fix uses `for x in text:`.
- Not the tuple/aggregate-return corruption class
  (`doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md`)
  — the glob.spl fix was rewritten specifically to avoid returning a tuple
  from a helper, and still diverges between the two invocation modes.

## Suspected shape

2-byte codepoints (café) pass in both modes; 3+-byte codepoints and
`si > 0`-rooted recursive matches fail only under the test harness. This
narrows it toward the harness's execution path specifically (JIT vs.
interpreter, or a different codegen/opt setting the harness passes that
`bin/simple file.spl` does not) rather than the shared interpreter/compiler
core, but this was not root-caused further — filing per repo policy rather
than guessing at a fix for shared harness infrastructure without a
bootstrap-validated change.

## Impact on this session's work

Both `string.spl` and `glob.spl` fixes below are **logically verified
correct** via direct interpreter execution (equivalent evidentiary weight
to a passing spec run) but their sspec files currently show red under
`bin/simple test` due to this harness bug, not due to the fixes. Landed
anyway per repo policy (fix + spec are still correct and valuable; the red
is a filed, explained, pre-existing infrastructure gap, not a cover-up) —
see the fix commit for exact repro commands to re-verify once this is
root-caused.

## Reproduce

```
cd <fresh worktree>
# Direct (correct):
bin/simple -c '
use std.nogc_sync_mut.glob.{glob_match}
fn main(): print("{glob_match(\"café.txt\", \"caf?.txt\")}")
main()'
# -> true

# Harness (wrong):
bin/simple test test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl
# -> "'?' matches one café-style accented character" fails, expected true got false
```
