# `text.char_at(i) as i64` parses a digit under jit/cranelift (PPM header `P\x06`)

- **Date:** 2026-11-23
- **Status:** FIXED 2026-11-23 in the seed (`rt_any_cast_int`); the
  `encode_ppm_p6` `.bytes()` workaround stays (correct by construction)
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

## Root cause (2026-11-23)

`char_at` has no static return type, so HIR types `s.char_at(i)` as `any` and
`x as i64` reaches the `any -> <int>` arm of MIR `lower_cast_expr`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`). Since
`6289aff155b` (2026-11-13, the any-float cast fix) that arm called
`rt_any_to_int`, whose text leg is the `.to_i64()` PARSE (`rt_string_to_int`:
parse first, code point only when the parse fails). So `"6"` parsed to 6 while
`"P"` fell back to 80. The STRING-typed cast arm already used `rt_value_as_int`
(one code point -> that code point), which is why a typed
`val s = "7"; s as i64` was always 55.

## Fix

New runtime entry `rt_any_cast_int` (Rust `runtime/src/value/collections.rs`,
C twin `src/runtime/runtime_native.c`): text -> `rt_value_as_int` (the cast
contract), everything else -> `rt_any_to_int` (float truncates; tagged int,
bool and wide int unchanged). `lower_cast_expr` emits it for `any as <int>`;
`.to_i64()` / `.to_int()` keep `rt_any_to_int` and still parse. Registered in
`runtime_symbols.rs`, `runtime_sffi.rs` and `common_backend.rs`.

Red/green: `src/compiler_rust/compiler/tests/any_text_cast_jit.rs`. On base,
3 of 5 FAIL (`char_at(1) as i64` = 6, header checksum 234 vs 54, any `"6"` =
6). With the fix, 5/5 pass and `any_float_cast_jit.rs` still passes 6/6. Runtime
unit test: `test_any_cast_int_text_is_code_point`.

The self-hosted compiler uses `rt_any_to_int` only for the `.to_i64()` method
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). That method
has the parse contract, so it is correct. Its `as` cast lowering was not
changed here.
