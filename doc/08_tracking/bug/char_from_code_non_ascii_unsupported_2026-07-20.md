# char_from_code / text_dot_from_char_code drop all non-ASCII codepoints

- **Filed:** 2026-07-20
- **Status:** Unicode encoding fix present in source (2026-07-20); native ABI
  convergence is **held, not admitted** (reconciled 2026-08-16). Local commit
  `20b37d580c03` routes Rust codegen to the canonical symbol but is not on
  `origin/main`; the hosted-provider/legacy-alias correction described below
  remains an uncommitted lane change. No current pure-Simple bootstrap PASS,
  deployment, or push is claimed.
- **Severity:** medium (blocks multilingual glyph paths; no crash)
- **Found by:** incidental — while triaging the stale codex font branch
  (`origin/codex/font-vulkan-static-toolchain-20260719`) against main. It was
  not a branch defect; both defects were on main at filing time.

## 2026-08-16 native ABI reconciliation

The canonical cross-runtime contract is exactly
`rt_char_from_code(code: i64) -> i64`. The argument is an untagged Unicode
scalar and the result is the raw `i64` bits of a runtime text handle. Neither
side may be declared through a target-sized/tagged `RuntimeValue` LLVM type.

The intended provider set is now:

- pure-Simple: `src/runtime/simple_core/core_string.spl`;
- core C: `src/runtime/runtime_native.c` plus `src/runtime/runtime.h`;
- hosted Rust: `src/compiler_rust/runtime/src/value/collections.rs`.

The hosted Rust provider is therefore **live design, not dead code**. It
returns a real allocated empty text for invalid scalars (not `RuntimeValue::NIL`)
and exports `text_dot_from_char_code(i64) -> i64` only as a delegating legacy
alias for older seed artifacts. New lowering must call `rt_char_from_code`.

This is recovery-lane state, not release evidence. Commit `20b37d580c03`
contains the held routing change; the exact raw-`i64` LLVM declarations,
hosted provider, legacy alias, registrations, and source-contract assertions
are a follow-up working-tree correction. Rust builds or tests can diagnose
that correction, but cannot admit it. Admission still requires a qualified
pure-Simple self-hosted runtime. At reconciliation time normal bootstrap is
blocked before Stage 1 by the unavailable planner-v2 admission producer, and
the three bounded Stage-3 pure-Simple attempts ended at
`unsupported LLVM value conversion from double to ptr` in
`std.common.format.format_fixed`. Consequently there is no current runtime
PASS or deployment claim for this fix.

## Source-fix history and held correction

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
- Hosted Rust character provider
  (`src/compiler_rust/runtime/src/value/collections.rs`): the July fix first
  hardened the legacy `text_dot_from_char_code` helper with an explicit
  `(0..=0x10FFFF).contains(&code)` guard before `code as u32`, preventing a
  value such as `0x100000041` from truncating to `0x41` (`'A'`). The current
  correction promotes `rt_char_from_code(i64) -> i64` as the hosted canonical
  provider and keeps `text_dot_from_char_code` as a delegating compatibility
  export. Both return an allocated UTF-8 runtime string, including a real
  empty string for invalid input. Historical Rust checks remain diagnostic;
  they are not pure-Simple admission evidence.

### Primitives evaluated during diagnosis

Two other byte/codepoint-to-text primitives were evaluated while diagnosing
the verification-evaluator disagreement below. The byte-array form was
rejected; the scalar form later became the canonical native ABI:
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

### Historical verification (diagnostic only)

Probe (`.chr()`-equivalent bare `char_from_code(code)` calls) across ASCII
(65), Latin-1 (0xE9 é, 2 bytes), CJK (0x4E2D 中, 3 bytes), emoji (0x1F600
😀, 4 bytes), and invalid inputs (0xD800 surrogate, 0x110000 out of range,
0x100000041 far out of range) — all correct under the then-used interpreted
seed evaluator. This result is retained as diagnostic history and is not a
pure-Simple self-hosted PASS.

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

## Historical summary

At filing time, `chr()` / `to_char()` could not produce any non-ASCII
character. The two implementations then backing it were independently wrong
above U+007F in different ways, so the Simple and baremetal paths disagreed.
The source encoding fixes address that original defect; current closure still
depends on admission of the reconciled native ABI described above.

## Historical evidence (verified on `origin/main` @ dc2e9a675b2)

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
hardware. At filing time it rendered multilingual text incorrectly there.

## Historical suggested fix

Main **already has** a correct encoder — `src/lib/common/encoding/utf8.spl`:

    fn utf8_encode_one(codepoint: i64) -> [i64]        # :128
    fn utf8_codepoint_byte_len(codepoint: i64) -> i64  # :163

The original proposal was to route `char_from_code_inline` through
`utf8_encode_one` instead of the ASCII table and replace the C mask with the
equivalent UTF-8 encode. Those source-level encoding changes landed. Its
warning against an `int64_t` signature described the ABI at that historical
revision and is superseded by the reconciled raw-`i64` contract above.

The selected return-on-invalid policy rejects surrogates (U+D800..U+DFFF) and
anything above U+10FFFF. Character-conversion providers return empty text for
those inputs; they must not return NIL or silently truncate the scalar.

## Landmines for whoever fixes this

- `text_dot_from_char_code` is defined in the **x86_64** boot stubs only — arm32, arm64 and
  riscv64 define it zero times. Adding it to those three TUs risks duplicate-symbol/link
  breakage on the OS boot path. Verify per-arch before touching them.
- Do not restore the old `RuntimeValue` + `DECODE_INT` declaration at this
  boundary. The reconciled ABI is exact raw `i64 -> i64` across pure-Simple,
  core C, hosted Rust, Cranelift, LLVM declarations, and runtime registries.
  A target-sized/tagged declaration can narrow the text handle and recreate
  the native failure.
- The hosted Rust provider must retain the pre-cast scalar-range check:
  without it, `code as u32` makes `0x100000041` appear to be `'A'`. Invalid
  scalars must produce an allocated empty text, and the legacy
  `text_dot_from_char_code` export must delegate to `rt_char_from_code` rather
  than becoming a second implementation.
