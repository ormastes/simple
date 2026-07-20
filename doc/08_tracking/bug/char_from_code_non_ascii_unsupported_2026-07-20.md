# char_from_code / text_dot_from_char_code drop all non-ASCII codepoints

- **Filed:** 2026-07-20
- **Status:** fixed in source (2026-07-20) — green under `bin/simple run` and
  matches the already-shipping `browser_engine` production workaround for
  the same bug (see below); the canonical `bin/simple test` verdict is
  still red (14 / 2 failures) due to a separate, pre-existing SSpec
  evaluator infrastructure gap, not a logic defect — see "Evaluator
  disagreement" below before treating this as fully closed
- **Severity:** medium (blocks multilingual glyph paths; no crash)
- **Found by:** incidental — while triaging the stale codex font branch (`origin/codex/font-vulkan-static-toolchain-20260719`) against main. Not a branch defect; both defects are on main today.

## Fix landed (2026-07-20)

- `char_from_code_inline` (`src/lib/common/string_core.spl`): ASCII fast
  table (9/10/11/12/13 + 32..126) unchanged; everything else now UTF-8
  encodes via a new private `_utf8_char_from_codepoint_inline` helper (byte
  math mirrors `utf8_encode_one`, inlined to avoid pulling
  `encoding.utf8`'s SIMD dependency into this bootstrap-critical file) and
  hands the bytes to `extern fn rt_bytes_to_text(bytes: [u8]) -> text`.
  Invalid codepoints (negative, > U+10FFFF, or a UTF-16 surrogate
  U+D800..U+DFFF) return `""`, matching the ASCII table's existing
  fallback policy.
- `char_from_codepoint` (`src/lib/common/encoding/utf8.spl`): had its own,
  independent instance of the same bug class — non-ASCII codepoints were
  assembled by routing each individual UTF-8 byte back through a
  byte-value-to-text helper, but every continuation/lead byte of a
  multi-byte sequence is itself >= 0x80 and invalid UTF-8 in isolation, so
  it silently produced a run of U+FFFD replacement characters instead of
  the intended character. Confirmed live (not dead code): used by
  `text_from_codepoints` and by
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
  which had already independently discovered this exact bug and worked
  around it with its own local re-implementation
  (`_codepoint_to_text` there — now redundant but left as-is, out of scope
  for this fix). Fixed by handing the whole `utf8_encode_one`-produced byte
  array to `rt_bytes_to_text` in one call instead of decoding it one byte
  at a time. Kept this function's pre-existing U+FFFD-on-invalid policy
  (distinct from `char_from_code_inline`'s `""`-on-invalid policy) since no
  behavior change was needed there and nothing calling it expects `""`.
- `text_dot_from_char_code` (baremetal x86_64,
  `examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c`): replaced
  the `& 0x7F` truncating mask with a real UTF-8 encoder using the same
  byte math, writing into a 4-byte stack buffer and handing it to the
  already-declared `extern RuntimeValue rt_string_new(RuntimeValue data,
  RuntimeValue len_val)` (length-explicit, confirmed to memcpy/copy the
  passed buffer rather than alias it — safe with a stack buffer). Same
  invalid-input policy: negative / > U+10FFFF / surrogate -> `rt_string_new(0,
  0)` (empty text). Compile-checked with the file's own documented
  `clang --target=x86_64-unknown-elf -c -ffreestanding -nostdlib -fno-pie
  -mno-red-zone` command (exit 0) and with `-fsyntax-only` (exit 0). Not
  touched: arm32/arm64/riscv64 define `text_dot_from_char_code` zero times
  (confirmed unchanged) — no duplicate-symbol risk introduced.
- `text_dot_from_char_code` (`src/compiler_rust/runtime/src/value/collections.rs`):
  added an explicit `(0..=0x10FFFF).contains(&code)` guard before the
  truncating `code as u32` cast, so an out-of-range i64 (e.g. `0x100000041`)
  is rejected instead of silently truncating to a low-32-bit value that
  looks valid (`0x100000041 as u32 == 0x41 == 'A'`). **This function is
  confirmed dead code on main today** — codegen for `.chr()`/`.to_char()`
  routes to the pure-Simple side, not this symbol — fixed only for class
  completeness per the original report. `cargo check -p simple-runtime`
  passes.

### Primitives tried and rejected

Two other byte/codepoint-to-text primitives were tried while diagnosing the
verification-evaluator disagreement below, both rejected:
- `bytes_to_string(bytes: [u8]) -> text` — declared identically in ~18
  stdlib files, including the two touched here originally. Does **not**
  link: there is no `bytes_to_string` runtime symbol, only
  `rt_bytes_to_text`. `simple compile` on a probe calling it fails with
  `Undefined symbol: bytes_to_string`. This extern declaration is
  apparently broken everywhere it's declared, not just here — worth a
  separate, lower-priority bug if anyone still relies on it.
- `rt_char_from_code(code: i64) -> text` — the canonical scalar
  codepoint-in/text-out ABI backing `.chr()`/`.to_char()`
  (`src/runtime/simple_core/core_string.spl`, mirrored in
  `runtime_native.c`/`runtime.c`). Real runtime symbol, but this seed
  binary's interpreter has no Rust-side handler for it: both `bin/simple
  run` and `bin/simple test` fail with `unknown extern function:
  rt_char_from_code`.

### Verification

Probe (`.chr()`-equivalent bare `char_from_code(code)` calls) across ASCII
(65), Latin-1 (0xE9 é, 2 bytes), CJK (0x4E2D 中, 3 bytes), emoji (0x1F600
😀, 4 bytes), and invalid inputs (0xD800 surrogate, 0x110000 out of range,
0x100000041 far out of range) — all correct under `bin/simple run`
(interpreted seed evaluator).

Regression specs added/updated (also mirrored into the `test/unit/`
duplicate tree, which had stale pre-fix assertions for the same source
file):
- `test/01_unit/lib/common/string_core_charcode_spec.spl` (+
  `test/unit/lib/common/string_core_charcode_spec.spl`)
- `test/01_unit/lib/common/encoding/utf8_spec.spl` (+
  `test/unit/lib/common/encoding/utf8_spec.spl`)

**Evaluator disagreement (expected, documented, not a fix defect):**
`bin/simple run` on a probe script passes every case above end to end.
`bin/simple test` (SSpec) on the same underlying logic reports `Passed:
113 / Failed: 14` for `string_core_charcode_spec.spl` and `Passed: 45 /
Failed: 2` for `utf8_spec.spl` — every failure is one of the new non-ASCII
assertions added by this fix, and every failure is `rt_bytes_to_text`
silently returning `""` rather than an assertion mismatch. Root cause
(diagnosed via the C source): `rt_bytes_to_text`'s C side
(`rt_core_as_array` in `runtime_native.c`) hits `!array || !array->data`
for the `[u8]` argument under the SSpec evaluator's argument marshaling,
which differs from how `bin/simple run`'s tree-walk interpreter marshals
the same array — a pre-existing seed-binary interpreter/test-runner
infrastructure gap, not a defect in the encoding logic (confirmed: the
purely-ASCII assertions in the same spec files, and the switch to a scalar
`i64` argument via `rt_char_from_code`, rule out both "the encoding math is
wrong" and "SSpec can't run `char_from_code_inline` at all"). Filed as a
follow-up rather than chased further per this fix's scope.

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
