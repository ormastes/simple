# linker_gen `format_hex` emits blank/control characters for any nonzero input

**Filed:** 2026-09-06
**File:** `src/app/linker_gen/main.spl:127-140` (`format_hex`)
**Reproduced by:** `test/03_system/feature/app/linker_gen_spec.spl` — "formats 1MB
as 0x100000" (`# @req REQ-LNK-018`)

## Symptom

`format_hex(1048576)` (the 1MB linker origin, `0x100000`) returns `"0x"`
followed by six low-ASCII control characters that render as blank/space in a
terminal, instead of `"0x100000"`. `format_hex(0)` is unaffected because it
takes an early-return special case (`if n == 0: return "0x0"`) that never
reaches the buggy loop.

Reproduced directly, isolated from the rest of the pipeline:

```
val h = format_hex(1048576)
print("h=[{h}] len={h.len()}\n")
# h=[0x     ] len=8
```

## Root cause

`format_hex`'s digit-to-character step is:

```simple
val ch = if digit < 10: ('0'.to_int() + digit).to_char() else: ('A'.to_int() + digit - 10).to_char()
```

This assumes `'0'.to_int()` returns the ASCII code point of `'0'` (48), so
that `48 + digit` lands on the correct ASCII digit character. Measured
directly:

```simple
print("'0'.to_int()={('0'.to_int())}\n")   # -> 0, not 48
print("'A'.to_int()={('A'.to_int())}\n")   # -> 65 (correct ASCII code point)
```

`Char.to_int()` on a decimal-digit character returns the character's
**numeric value** (0-9), not its ASCII code point, while on a letter it
returns the actual ASCII code point. That inconsistency means the `digit <
10` branch computes `(0..9) + digit` (landing on ASCII control characters 0-18,
which print as blank/invisible), while the `>= 10` branch (`'A'.to_int() +
digit - 10`, i.e. base 65) is correct — which is exactly why every hex value
in the failing scenario (`0x100000`, digits `1,0,0,0,0,0`) came out blank
while a value with a genuine A-F digit would not have exposed this.

This is either:
1. A bug in `Char.to_int()` — digit characters should return their ASCII code
   point like every other character, for arithmetic code like this to work; or
2. A bug in `format_hex` — it should not assume ASCII-arithmetic semantics for
   `to_int()` on digit characters, and should instead index a literal
   `"0123456789ABCDEF"` string or otherwise special-case the digit branch.

Either way, `format_hex` on any nonzero input has been silently wrong;
nothing previously exercised it, since the prior version of
`linker_gen_spec.spl` only compared hand-authored literal text to itself and
never called the real function.

## Impact

Every generated linker script's `MEMORY` block origin (e.g.
`ORIGIN = 0x100000`) is corrupted for any board with a nonzero memory-region
origin — i.e. every real board except one whose first region starts at
address 0. This would produce an unusable `.ld` file for essentially every
bare-metal target `linker-gen` targets.

## Unblock condition

Fix `format_hex` to build hex digit characters correctly regardless of
`Char.to_int()`'s digit-vs-letter semantics (e.g. index a literal
`"0123456789ABCDEF"` string by `digit`), or fix `Char.to_int()` so digit
characters return their ASCII code point consistently with letters — then
remove the `# NOTE:` in the "formats 1MB as 0x100000" scenario.
