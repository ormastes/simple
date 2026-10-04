# `to_int` contract split: interpreter maps a 1-char text to its code point; JIT and C runtime parse it

- **Filed:** 2026-10-05
- **Area:** string `to_int`/`to_i64`/`to_i32` in the interpreter
  (`compiler/src/interpreter_method/string.rs:419`,
  `interpreter_helpers/method_dispatch.rs:136`), the seed runtime
  (`runtime/src/value/collections.rs` `rt_string_to_int`), and the C runtime twin
  (`src/runtime/runtime_native.c` `rt_string_to_int`)
- **Status:** OPEN — owner decision required; nothing changed in this lane

## The question that was asked

`"x".to_int() ?? 7` gives 0 under the JIT and 120 under the interpreter, while
7 was expected. Both engines agree that `to_int` is **total**: it never returns
nil, so `?? 7` is dead code on it. The Option-returning parse is `parse_int()`,
and `"x".parse_int() ?? 7` is **7 in both engines** today.

Changing `to_int` to return nil on failure would change 5,300 call sites that
use `.to_int()`/`.to_i64()` without `??` (823 use `??`), and would also need
the same change in the pure-Simple lowering and in the C runtime. That is a
language-contract change, so it is left to the owner.

## The real divergence

| expression | JIT (seed) | interpreter | C runtime (self-hosted) |
|---|---|---|---|
| `"x".to_int()` | 0 | **120** | 0 |
| `"q".to_int()` | 0 | **113** | 0 |
| `"12x".to_int()` | 0 | 0 | **12** (strtoll prefix) |
| `"xy"` / `""` / `"12"` / `" 7 "` / `"-5"` | 0 / 0 / 12 / 7 / -5 | same | same |
| `for ch in "ab": ch.to_i32()` | **0, 0** | 97, 98 | 0, 0 (strtoll) |
| `"x".parse_int() ?? 7` | 7 | 7 | — |

Why: there is no runtime `char` value. `for ch in text` yields a one-character
text, and the seed types it as `str`, so no engine can tell a character from a
text at the call. The interpreter therefore added a heuristic in `string.rs:419`
(parse; on failure, a single character gives its code point) so that char-code
hash loops do not collapse to 0. The JIT and the C runtime parse strictly. The
interpreter also disagrees with itself: `method_dispatch.rs:136` returns `nil`
on failure for the same method names.

Consequences:
- A djb2/FNV-style hash over `ch.to_i32()` gives a different checksum per
  engine. Under the JIT, every non-digit character contributes 0.
- `"-".to_int()` is 45 in the interpreter and 0 elsewhere.

## Options

1. Keep `to_int` a strict, total text parse everywhere. Drop the interpreter
   heuristic, and give characters a real API (`ch.char_code()`, or typing
   `for ch in text` as `char` with code-point `to_i32`).
2. Adopt the interpreter heuristic in the seed runtime and the C runtime twin.
   This changes `"-".to_int()` from 0 to 45, and similar cases, everywhere.
3. Make `to_int` Option-returning (5,300 sites).

Option 1 is the only one that does not silently change existing numeric parsing.

## Also found

A raw-string literal `'x'` (Simple has no char literal) is accepted for a
`char`-typed parameter. Under the JIT, `c.to_int()` then returns the string
handle, 5265067951073: `char` is a raw scalar in the JIT ABI. This is a type
check gap.

## Pinned behaviour

`compiler/tests/to_int_parity_jit.rs` pins the cases where all engines agree,
plus `parse_int` returning nil. Its results match the interpreter.
