# Seed interpreter: `ch.to_i32()` on a for-in-text char parses (yields 0), not codepoint

**Filed:** 2026-08-31 · **Status:** OPEN
**Host:** Windows 11 (MSYS2), seed `bin/simple.exe` (28,291,570 bytes, rebuilt 2026-08-31 from `531942cb`)
**Severity:** medium — silent wrong data on the seed interpreter lane; any
byte/char hashing or digit-parsing loop degenerates.

## Symptom (measured)

```simple
fn main():
    for ch in "hey":
        print(ch.to_i32())   # prints 0, 0, 0 — expected 104, 101, 121
```

Real consequence: `test/01_unit/tools/shell/checksum_spec.spl`
"produces different hash for different input" FAILS on the seed — djb2 of
"hello" and of "world" both evaluate to 210587549733 because every
`ch.to_i32()` contributes 0.

## Root cause

The seed has no Char value: `for ch in <text>` yields a 1-char `Value::Str`,
and `interpreter_method/string.rs:416` maps `to_int|to_i64|to_i32|...` to
`s.trim().parse::<i64>()` with `Err(_) => 0`. Product code expects
codepoint semantics (`src/compiler/70.backend/inline_asm.spl:423` does
`c.to_i32() - 48`; `smf_writer.spl:448` hashes `byte.to_i32()`).

Related, not duplicate: `for_in_text_iterates_bytes_not_chars_2026-08-01.md`
(FIXED — iteration segmentation), `2026-08-01_interpreter_char_code_at_byte_indexed.md`.

## Fix sketch

Either give the seed a Char value kind for text iteration whose `to_i32` is
the codepoint, or, minimally, make the Str `to_iNN` family fall back to the
first codepoint when `len == 1` and numeric parse fails. The second changes
"a".to_i32() from 0 to 97 — audit callers relying on the 0.
