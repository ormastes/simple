# Native codegen leaves escapes unprocessed after a `{` in a text literal

**Status:** fix-implemented-verification-pending (CoreLexer source fixes landed, including W4-1 `la_is_quote` parity fix; waiting-for: Stage-2 native binary rebuild + `src/app/test/brace_escape_probe.spl` native run printing `LEN=15`). **Found:** 2026-11-26 (work/bug-cuda-module-get-function-abi-20261126). **Severity:** P2.
**Component:** self-hosted CoreLexer (`src/compiler/10.frontend/core/lexer_struct.spl`); first seen as native output. Observed on the integ25 Stage 2 compiler
(`pinned-c1a10190b978`, stage2-admitted sha256 `ef46f0d2ab4274c4`); not re-checked on current source.

A literal like `"a\n) {\n    b;\n}\n"` evaluates to 573 bytes for the
probe PTX under the interpreter (W-STR-BRACE-001 warns and keeps `{` as
text). The NATIVE binary built from the same source passes 591 bytes: every
`\n` after the `{` reaches the runtime as the two bytes `\` `n`. Writing
`{{` gives the same 591 bytes. Seen with gdb at the
`rt_cuda_module_load_data` call (`x1 = 0x24f`, text `... count\n) {\\n    .reg ...`).

Effect: PTX embedded in Simple source is rejected by the driver with -218
`CUDA_ERROR_INVALID_PTX` in native builds. `src/lib/gc_async_mut/processing/cuda_fill_u32.spl:41`
(`_processing_cuda_ptx`) has the same shape, so the native ProcessingIR CUDA
path is likely affected.

Workaround (used in `src/app/test/cuda_module_launch_probe.spl`): put each
brace in its own literal, `... ") " + "{{" + "\n..."`. Then interpreter and
native both give 573 bytes, and the module loads.

## Root cause and fix (2026-11-26, work/bug-native-brace-escape-20261126)

The bug is in the self-hosted CoreLexer (`src/compiler/10.frontend/core/lexer_struct.spl`),
not in native lowering. For a `{` it looked ahead for the matching `}` and
copied the whole region VERBATIM, so the interpolation re-parse could decode
it. When the region was not a valid interpolation, nothing decoded its
escapes. The seed lexer (`compiler_rust/parser/src/lexer/strings.rs`) treats
`{{` and a `{` followed by `\` as literal braces and keeps scanning. The
CoreLexer now does the same: it emits the `{{` escape and keeps scanning, so
escapes after the brace decode normally.

Same root, same fix: `native_string_backslash_brace_escape_kept_2026-11-26`
(filed on work/bug-verify-native-batch-20261126, not on origin yet). The
CoreLexer's escape table had no `\{` / `\}` row, so it kept the backslash.
`\{` / `\}` now emit the doubled `{{` / `}}` escape, which decodes to a bare
brace, as the seed does. Mark that row duplicate of this one when both land.

Both new paths apply only to interpolating literals. Single-quoted literals
(`cur_no_interp`) are never brace-decoded, so they keep the old token text.
A spec row pins that.

Evidence:
- Red, then green: `test/01_unit/compiler/lexer/lexer_brace_escape_literal_value_spec.spl`
  runs the self-hosted lexer -> interpolation -> brace-decode pipeline, which
  is the value a native build embeds, and compares it with the interpreter
  value. Old lexer: 3/5 fail on the brace rows, then 5/6 with the `\{` row
  added. Fixed lexer: 7/7, including a single-quoted row that fails if the
new paths are not gated.
- PTX at `cuda_fill_u32.spl:41`: the fixed self-hosted pipeline's value is
  byte-identical (582 bytes, `cmp`) to the seed interpreter's value of the
  same literal.
- Native red on integ25 Stage 2 (llvm and cranelift):
  `src/app/test/brace_escape_probe.spl` prints LEN=17, where the interpreter
  prints LEN=15.
- Native green: NOT shown. The pinned Stage 2 was built from the old lexer.
  A seed native-build of the fixed tree printed LEN=15 on both backends, but
  the same lane on the unfixed tree timed out (3000 s). With no red in that
  lane, and the seed probably lexing with its own Rust lexer, it is not
  evidence. Verifying needs a Stage 2 rebuilt from this tree.
- Regression specs unchanged: string_interp_brace_escape,
  interp_brace_literal_collision, lexer_interp_null_coalesce_nested_string,
  interpolation_nonascii_unit, lexer, and lexer_comprehensive all pass.
  brace_fastpath_and_unit_exports fails 7/8 with the same pre-existing
  `parse_i64` semantic error at :191 as before the change.

## Source literals and the downstream `\{` rule (review follow-up, 2026-11-26)

A census of 2,238 brace-bearing literals against the seed found that the
corrected lexer changes 1,132 self-hosted values. 917 of them gain holes,
matching the seed. Every no-hole literal now equals its seed value. Fixed in
the follow-up commit:
- 15 static nested-JSON literals that ended in `}}` lost a brace, under the
  seed too. Each closing run is now doubled. The `Content-Length: 84` frame is
  correct again: the body is 84 bytes once the brace is back. The
  container/** Go-template literals were already right.
- `core_widgets.spl` turned a `{"-".repeat(..)}` hole into text. It is now
  bound to a local first.
- `desktop/dialog.spl` `{"OK"}` is an AppleScript list and must stay literal.
  It is now spelled with doubled braces.
- `parse_string_interpolation_regions` skipped any `\` + brace as an escaped
  brace. CoreLexer token text no longer carries a source `\{`, so that rule
  only hit `\\{`, where the seed interpolates (`C:\\...\\{lib}.dll`,
  `{base}\\{filename}`) and where a sed interval (`\\{{0,1\\}`) decodes to
  `\{0,1\}`. The rule is removed.
- Second review: `lsp_transport.spl` fragments that are only closers, or
  that start with a `}}` run, still decoded to one brace, so 9 of 16
  `lsp_build_*` builders emitted unbalanced JSON. Every brace in those
  builders is now doubled. `lsp_transport_json_builders_spec` parses every
  builder output as strict JSON and rejects any single brace. Red on the
  previous and the origin file, green now. Per-site check of the no-hole
  class: `mir_json.spl:182`, `list/main.spl:78` and
  `editor_controller.spl:2157` were unbalanced under the seed too, and are
  doubled now. `virtual_summary_protocol.spl:42,64,77` are correct in both:
  the final `}` after a hole stays its own segment in MIR
  `split_interpolation_segments`.

## W4-1 Follow-up & Verification (2026-11-27, work/w4-1-compiler-lexer-mir-20261127)

- **Seed parity gap closed (`la_is_quote`):** In `CoreLexer.scan_string` (`src/compiler/10.frontend/core/lexer_struct.spl:1147`), `la_literal_brace` handled `{` followed by `{` or `\`, leaving `{` followed by `"` or `'` (`la_is_quote`) unescaped. Thus `"{'a'} {42}"` and `"{'a'}\n"` interpolated `'a'` as a character/string hole instead of matching the Rust seed (`src/compiler_rust/parser/src/lexer/strings.rs:330,339`), which emits literal `{'a'}`. Adding `or la_is_quote` to `la_literal_brace` (gated on `not self.cur_no_interp`) restores seed parity for `{"..."}` / `{'...'}` literals while keeping single-quoted (`cur_no_interp`) strings untouched.
- **Note on duplicate reference:** `native_string_backslash_brace_escape_kept_2026-11-26` is not present in `doc/08_tracking/bug/` on `origin/release/1.0.0`.
- **Sequential Windows interpreter verification (seed `simple.exe --mode=interpreter`):**
  - `test/01_unit/compiler/lexer/lexer_brace_escape_literal_value_spec.spl`: `12 total, 12 passed, 0 failed` (`outcome=OK`), covering backslash escapes after `{`, `\t`/`\x41`/`\u0042`/`\"`, doubled braces, `\{`/`\}`, single-quoted negative control, `{` + quote seed parity, and end-to-end `core_interpret` execution.
  - `test/01_unit/compiler/frontend/string_interp_brace_escape_spec.spl`: `6 total, 6 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/compiler/frontend/interp_brace_literal_collision_spec.spl`: `11 total, 11 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/compiler/lexer/lexer_spec.spl`: `4 total, 4 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/compiler/lexer/lexer_comprehensive_spec.spl`: `3 total, 3 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/lib/editor/services/lsp_transport_json_builders_spec.spl`: `2 total, 2 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/compiler/lexer/fstring_brace_concat_spec.spl`: `2 total, 2 passed, 0 failed` (`outcome=OK`).
  - `test/01_unit/compiler/lexer/string_escaped_backslash_spec.spl`: `5 total, 5 passed, 0 failed` (`outcome=OK`).
- **Remaining verification (`waiting-for:`):** Native Stage-2 compiler rebuild from current source + native execution of `src/app/test/brace_escape_probe.spl` confirming `LEN=15` (and PTX native load where applicable).
