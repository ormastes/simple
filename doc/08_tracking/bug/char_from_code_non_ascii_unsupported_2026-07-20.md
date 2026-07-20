# char_from_code / text_dot_from_char_code drop all non-ASCII codepoints

- **Filed:** 2026-07-20
- **Status:** open
- **Severity:** medium (blocks multilingual glyph paths; no crash)
- **Found by:** incidental — while triaging the stale codex font branch (`origin/codex/font-vulkan-static-toolchain-20260719`) against main. Not a branch defect; both defects are on main today.

## Summary

`chr()` / `to_char()` cannot produce any non-ASCII character. The two implementations
that back it are each independently wrong above U+007F, in *different* ways, so the
Simple path and the baremetal path also disagree with each other.

## Evidence (verified on `origin/main` @ dc2e9a675b2)

**1. Pure-Simple path — returns empty text.**
Compiler codegen resolves a bare `char_from_code` call to the pure-Simple implementation
(`src/lib/common/string_core.spl:293`) via suffix-matching in `linker.rs:294-300`. That
delegates to `char_from_code_inline` (`string_core.spl:176`), which is an ASCII table lookup:

    elif code >= 32 and code <= 126:
        val chars = " !\"#$%&'()*+,-./0123456789:;<=>?@ABC...xyz{|}~"
        val index = code - 32
        return chars[index]
    ""                      # <-- everything else falls through to empty text

Any codepoint > 126 (and any < 32 outside the five named control chars) yields `""`.

**2. Baremetal path — returns garbage.**
`examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c`:

    RuntimeValue text_dot_from_char_code(RuntimeValue code) {
        char buf[2];
        buf[0] = (char)(DECODE_INT(code) & 0x7F);   // <-- truncating mask
        buf[1] = '\0';
        return rt_string_from_cstr(buf);
    }

The `& 0x7F` mask silently folds every non-ASCII codepoint onto an unrelated ASCII
character rather than failing. U+00E9 renders as `i`, U+4E2D as `-`, etc.

## Why it matters

This sits directly under the shared-multilingual-GPU-font work. Main already carries
complex-script shapers (`src/lib/skia/feature/shaper/selected_arabic.spl`,
`selected_complex.spl`, `font_fallback.spl`) whose codepoints cannot round-trip through
`chr()`. Per `.claude/rules/board-runnable.md` the baremetal variant must also hold on real
hardware, and today it renders multilingual text incorrectly there.

## Suggested fix

Main **already has** a correct encoder — `src/lib/common/encoding/utf8.spl`:

    fn utf8_encode_one(codepoint: i64) -> [i64]        # :128
    fn utf8_codepoint_byte_len(codepoint: i64) -> i64  # :163

Route `char_from_code_inline` through `utf8_encode_one` instead of the ASCII table, and
replace the C mask with the equivalent UTF-8 encode (keeping main's existing
`RuntimeValue` signature — do **not** adopt the codex branch's `int64_t` signature, which
is caller-convention-incompatible with main).

Return-on-invalid should be agreed once and applied to both paths: reject surrogates
(U+D800..U+DFFF) and anything above U+10FFFF.

## Landmines for whoever fixes this

- `text_dot_from_char_code` is defined in the **x86_64** boot stubs only — arm32, arm64 and
  riscv64 define it zero times. Adding it to those three TUs risks duplicate-symbol/link
  breakage on the OS boot path. Verify per-arch before touching them.
- The codex branch's version of this function is **not** a usable drop-in: it takes a raw
  `int64_t` where main takes a `RuntimeValue` + `DECODE_INT`, and it reroutes codegen away
  from the pure-Simple implementation (violating the repo's Pure-Simple-First rule and
  forcing every runtime profile to export a symbol main does not need).
- A related latent bug in `src/compiler_rust/runtime/src/value/collections.rs`: that
  crate's `text_dot_from_char_code` lacks a `0..=0x10FFFF` guard, so `code as u32`
  truncates and `0x100000041` returns `'A'` instead of NIL. It is currently **dead code**
  on main (codegen routes to the Simple side), so it is not urgent — but fix it in the same
  pass if that function is ever brought back into service.
