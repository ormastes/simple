# `text.char_at(i) as i64` parses a digit under jit/cranelift (PPM header `P\x06`)

- **Date:** 2026-11-23
- **Status:** open (compiler); workaround landed in `encode_ppm_p6`
- **Family:** `text_byte_len_vs_codepoint_index_family_2026-08-06.md` (that
  record has the same cast returning a POINTER for non-ASCII text; this is the
  ASCII-digit variant, still live on the 2026-11 seed).

## Symptom

`examples/06_io/ui/web_render_page_ppm.spl` run with `SIMPLE_EXECUTION_MODE=jit`
(or `cranelift`) wrote a PPM whose header began
`50 06 0a 04 00 20 03 00 0a 02 05 05` instead of `P6\n40 30\n255\n`; every
digit of the header became its numeric value. Reproduced with and without
`PAGE_DEVICE_SCALE` (k=1 and k=2); the catalog script never saw it because it
forces `SIMPLE_EXECUTION_MODE=interpreter`.

## Minimal repro

```simple
fn main() -> i64:
    val header = "P6\n12 34\n255\n"
    print "{header.char_at(1) as i64}"
    0
```

| engine | output |
|--------|--------|
| `SIMPLE_EXECUTION_MODE=interpreter` | `54` (code point of `6`) |
| `SIMPLE_EXECUTION_MODE=jit` | `6` |
| `SIMPLE_EXECUTION_MODE=cranelift` | `6` |

Whole header through `char_at(i) as i64`: interpreter `80 54 10 49 50 32 51 52
10 50 53 53 10`, jit/cranelift `80 6 10 1 2 32 3 4 10 2 5 5 10` — non-digit
characters keep their code point, digits are parsed as numbers (a text->int
parse cast instead of the char->code-point cast).

## Workaround (correct by construction)

Take bytes with `text.bytes()` (agrees on every engine): `encode_ppm_p6` now
builds its header from `"P6\n{w} {h}\n255\n".bytes()`. Verified jit k=1/k=2
headers `50 36 0a 34 30 20 33 30 0a 32 35 35` after the change.

## Other live sites of the same cast (not changed here)

`src/lib/js/node/buffer_module.spl:209-213` and
`src/lib/nogc_sync_mut/js/engine/parser.spl:1232-1236` compute hex digit values
as `ch.char_at(0) as i64 - 48`; under jit a `"5"` gives `5 - 48 = -43`.

## Fix needed

Make the compiled `text as i64` cast on a one-character `char_at` result
return the code point, as the interpreter does (or reject the cast at compile
time and require `.bytes()` / an explicit code-point accessor).
