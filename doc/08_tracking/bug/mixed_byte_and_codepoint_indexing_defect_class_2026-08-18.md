# Defect class: mixing byte-indexed and codepoint-indexed text APIs

Status: OPEN (class). Filed 2026-08-18.

## The hazard

Simple's text API mixes two index spaces with no type-level distinction:

| API | index space |
|---|---|
| `.len()` | **bytes** |
| `.substring(a, b)` | **bytes** |
| `s[i:j]` slice | **bytes** |
| `.char_at(i)` | **codepoints** |
| `s[i]` single-bracket | **codepoints** |

Scanning with one and slicing with the other is silently correct for ASCII and
silently WRONG for any multibyte input. Nothing in the type system or the
linter catches it.

## Confirmed instances (both found by accident, one day apart in the same day)

1. `str_to_lower` / `str_to_upper` / `str_trim_left` / `str_trim_right` /
   `str_replace_all` / `str_reverse` in `src/lib/common/string_core.spl` —
   indexed `s[i]` (codepoints) with `i` bounded by `s.len()` (bytes). Crashed
   with `string index out of bounds` on any multibyte input. FIXED
   (`55bada8b52f`); `str_split`'s empty-separator branch remains OPEN by
   deliberate scope decision (needs real UTF-8 width detection).
2. `path_pure` basename/dirname scanning — `.char_at()` to find separators,
   `.substring()` to slice at the same index; `"dir/café"` yielded
   `"caf<invalid byte>"`. FIXED in C-MIG-0037/0038 (`e0cfbc6a8d9`,
   `2ca8d0dafcf`) via an `is_sep_at` helper using only byte-consistent
   `.substring(i, i+1)` comparisons.
3. **STILL OPEN**: `path_ext` / `last_component` in
   `src/lib/common/path_pure.spl` (from C-MIG-0036) carry the same pattern —
   reported by the C-MIG-0037 agent, left untouched because the file was under
   concurrent edit.

Both discovered instances were found only because a differential spec probed
multibyte edges against an oracle. That is not a reliable discovery mechanism
for the rest of the tree.

## Wanted

1. A tree-wide audit for the pattern: any function that obtains an index from a
   codepoint-space API and consumes it in a byte-space API (or vice versa).
2. Fix the open instances, each with the reproduce + similar-case tests the Fix
   test standard requires (`doc/03_plan/infra/binary_runtime_hardening/plan.md`).
3. Prevention, in preference order: a lint rule for the mixed-space pattern; or
   renaming the APIs so the index space is in the name
   (`byte_len`/`char_len`, `byte_substring`/`char_substring`); or distinct
   index types. Renaming is the only option that makes the mistake hard to
   write, but it is a breaking API change and needs a deliberate decision.

## Audit (2026-08-18)

### Detection method

Scripted, not estimated. Over `src/lib` and `src/app` (excluding
`src/compiler_rust/vendor/**`, `src/runtime/vendor/**`,
`src/runtime/miniaudio.h`, `src/runtime/stb_image.h`,
`src/runtime/stb_truetype.h` per CLAUDE.md Owned-Code Scope):

1. `grep -rl '\.char_at('` over `src/lib` + `src/app` (excluding vendor) ->
   **206 files**.
2. Intersect with files that ALSO contain `.substring(` -> **66 files**
   (candidate files where a codepoint-space read and a byte-space slice
   coexist).
3. Per-file, split into `fn`/`pub fn` blocks (Perl, splitting on
   `^(?:pub )?fn <name>`) and keep only functions whose body contains BOTH
   `.char_at(` and `.substring(` -> **51 candidate functions**, across 27
   files. This is heuristic #1 from the task (same-function co-occurrence);
   heuristics #2 (`.len()`-bounded loop calling `.char_at(i)` with the loop
   variable) and #3 (scan-with-`.char_at()` then slice-with-`.substring()` at
   the same index) turned out, on inspection, to be true of the large
   majority of the 51 -- the dominant shape in this codebase is exactly
   `while i < s.len(): ch = s.char_at(i) ... s.substring(a, i)`, i.e. all
   three heuristics collapse onto the same 51 candidates rather than finding
   disjoint sets.
4. Every one of the 51 was read and classified by hand (not sampled).

### Classification table

`file:function | shape | classification | evidence`

| file:function | shape | classification | evidence |
|---|---|---|---|
| `src/lib/nogc_sync_mut/smtp/send.spl:email_validate` (+ 2 duplicate copies below) | `.length()`-bounded loop, `.char_at(i)` used only for `==` comparison (never sliced at `i`) | CONFIRMED (shape) / benign in practice | On this build, an out-of-range `.char_at()` past the codepoint count degrades to a silent non-match rather than a crash -- probed with 1 and 8 multibyte chars before `@`, both passed pre-fix. FIXED anyway (defensive, matches the established pattern) since the shape is still wrong and depends on undocumented OOB behavior. |
| `src/lib/nogc_async_mut/smtp/send.spl:email_validate` | same as above | CONFIRMED (shape), STILL OPEN | Duplicate of the above in a different family (`nogc_async_mut`); not touched (outside the 5-fix cap). Fix: same as above. |
| `src/lib/gc_async_mut/smtp/send.spl:email_validate` | same as above | CONFIRMED (shape), STILL OPEN | Duplicate in a third family (`gc_async_mut`); not touched. Fix: same as above. |
| `src/lib/nogc_sync_mut/smtp/send.spl:smtp_undot_stuff` | `line.char_at(0)`/`char_at(1)` guarded by `line.length() >= 2`, then `line.substring(1, ...)` | ASCII-ONLY-SAFE | Only slices at byte offset 1 when `char_at(0) == "."`, an ASCII byte that is always exactly 1 byte wide, so codepoint index 1 == byte offset 1 here regardless of what follows. |
| `src/lib/common/path_pure.spl:path_ext` | `.char_at(i)` scan bounded by `.len()`, then `.substring(last_dot + 1, n)` at the found index | **CONFIRMED, FIXED** (2026-08-18, Fix #6) | Pre-fix repro: `path_ext("café.txt")` -> `".txt"` (wrong; extra leading dot). Fixed via `.substring(i, i+1) == "."` comparison swap. |
| `src/lib/common/path_pure.spl:last_component` | same shape, two scans (`char_at(n-1)=='/'` and `char_at(i)=='/'`) then `.substring(...)` | **CONFIRMED, FIXED** (2026-08-18, Fix #6) | Pre-fix repro: `last_component("café/bar")` -> `"/bar"` (wrong; separator not found). Fixed via `.substring(i, i+1) == "/"` comparison swap (matches the `is_sep_at` pattern already used for `path_basename`/`path_dirname` in the same file). |
| `src/lib/common/path_pure.spl:path_ext` | `.char_at(i)` scan bounded by `.len()`, then `.substring(last_dot + 1, n)` at the found index | CONFIRMED, **STILL OPEN** (avoid-list) | See "Still-open" section below -- exact fix given, not applied (file under concurrent edit per task instructions). |
| `src/lib/common/path_pure.spl:last_component` | same shape, two scans (`char_at(n-1)=='/'` and `char_at(i)=='/'`) then `.substring(...)` | CONFIRMED, **STILL OPEN** (avoid-list) | Same as above. |
| `src/lib/nogc_sync_mut/imap/parse.spl:imap_split_at_first_space` | `.length()`-bounded loop, `.char_at(i)` compared to `" "`, then `.substring(0,pos)`/`.substring(pos+1,len)` at that same `i` | **CONFIRMED, FIXED** | Pre-fix repro: `imap_split_at_first_space("café bar")[1]` gave `" bar"` (leading space) instead of `"bar"`. See Fix #1. |
| `src/lib/nogc_sync_mut/imap/parse.spl:imap_strip_crlf` | `.char_at(len-1)`/`.char_at(len-2)` where `len = .length()` (bytes), then `.substring(0, len-2)`/`.substring(0, len-1)` | **CONFIRMED, FIXED** | Near-end byte/codepoint offset mismatch on a multibyte-terminated line; would either miss or wrongly-detect a trailing CRLF. See Fix #1. |
| `src/lib/nogc_sync_mut/imap/parse.spl:imap_parse_untagged_response` | `.char_at(0)`/`.char_at(1)` guarded by `.length() >= 2`, checking literal `"* "`, then `.substring(2, len)` | ASCII-ONLY-SAFE | `"* "` prefix is 2 ASCII bytes = 2 codepoints; offset 2 is correct regardless of what follows. |
| `src/lib/nogc_sync_mut/imap/parse.spl:imap_parse_capability_tokens` | `.length()`-bounded loop (`i <= len`), `.char_at(i)` compared to `" "`, `.substring(start, i)` at the same `i` | **CONFIRMED, FIXED** | Same shape as `imap_split_at_first_space`. See Fix #1. |
| `src/lib/common/ui/wm_theme_css.spl:_wm_theme_css_value` | `.substring(search_from, css_len)` + `.index_of` combined with `.char_at(colon_pos)` bounded by `.len()` | CONFIRMED (shape), not fixed (outside cap) | CSS property/value scanning; property names and structural chars (`:`) are always ASCII, but declared *values* are not guaranteed ASCII (e.g. quoted content strings), so the shape is real. Fix: same `.substring(i,i+1)` swap. |
| `src/lib/nogc_sync_mut/web_framework/route_types.spl:match_pattern` | `pp.char_at(0) == ':'` guard, then `pp.substring(1, pp.len())` | ASCII-ONLY-SAFE | `:` is 1 ASCII byte; offset 1 always correct regardless of the rest of the segment. |
| `src/lib/nogc_sync_mut/editor/panels/asset_browser.spl:detect_asset_type` | (none in this function itself) | FALSE POSITIVE | The per-function splitter mis-attributed `.char_at`/`.substring` calls from LATER unrelated code in the same file (a `class`/`impl` block whose methods use `me name(...)`, not `fn`, so they weren't recognized as new block boundaries). `detect_asset_type` itself only calls `.ends_with`. |
| `src/lib/gc_async_mut/smtp/types.spl:response_parse_code` | `.char_at(0/1/2)` guarded by ASCII-digit checks, then `.substring(0,3)` | ASCII-ONLY-SAFE | Only slices when all 3 leading chars are ASCII digits (each 1 byte), so offset 3 is always correct. |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl:fb_background_radial_stack_clip` | backward `.char_at(s)` scan for `" "` in a lower-cased/trimmed CSS gradient tail, then `.substring(s+1, tpct)` | ASCII-ONLY-SAFE | Domain is a CSS `radial-gradient()` numeric/percent tail (`"NN%"`/`"transparent NN%"`), always ASCII by the CSS grammar this parser targets. |
| `src/lib/common/text_advanced.spl:escape_json` | `s.chars()` (codepoint array) walked by codepoint index `i`, with a separately-tracked BYTE offset `bo` incremented by `ch.len()` per char, sliced via `s.substring(run_start, bo)` | FALSE POSITIVE | Correctly implemented: `bo`/`run_start` are consistently BYTE offsets, never mixed with the codepoint index `i`. `hex.char_at(...)` only indexes the ASCII literal `"0123456789abcdef"`, which is always safe. This is the reference-correct pattern the fixes below emulate. |
| `src/lib/nogc_async_mut/http_client/types.spl:url_decode` (+1 dup below) | `.length()`-bounded loop, `.char_at(i)` used BOTH for control-char comparison AND pushed to reconstruct output char-by-char | **CONFIRMED, FIXED** | Pre-fix repro: `url_decode("café")` -> `"caf<invalid byte>"`. See Fix #3 (and its two-step correction below). |
| `src/lib/gc_async_mut/http_client/types.spl:url_decode` | same shape | CONFIRMED, STILL OPEN | Duplicate in the `gc_async_mut` family; not touched (outside the 5-fix cap). Fix: same as Fix #3. |
| `src/app/doc/public_check/export_parser.spl:parse_export_list`, `parse_export_statements` | `.char_at(i)`/`.char_at(j)` bounded by `.len()`, scanning for whitespace to trim, then `.substring(start, end_val)` | CONFIRMED (shape), not fixed (outside cap) | Trims a source-code line; doc/comment content can contain multibyte text (e.g. non-English identifiers/comments in `export` lines). Real but low-frequency. |
| `src/app/wm_compare/site_corpus_layout_report.spl:_i32_after_marker`, `_chrome_canvas_widths_sdn` | `.char_at(end)` bounded by `.len()` scanning digit runs in JSON metrics text, then `.substring(0, end)` | ASCII-ONLY-SAFE | Scans only numeric/`-`/`.` runs immediately after a known ASCII marker in machine-generated JSON metrics; the scanned run itself is always ASCII, so `end` never crosses a multibyte boundary before the loop breaks. |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects.spl:_css_top_level_space_tokens`, `_css_effects_split_top_level_commas` | `.char_at(index)` bounded by `.len()`, tracking paren `depth`, then `.substring(start, index)` at token boundaries | CONFIRMED (shape), not fixed (outside cap) | CSS shorthand values are usually ASCII but not guaranteed (quoted `content:` strings, `font-family` names). Fix: same `.substring(i,i+1)` swap for the comparison, keep the token slice as a byte range (already is). |
| `src/app/md_lsp/md_lsp_main.spl:_md_lsp_parse_content_length` | `.char_at(i)` bounded by `.len()`, only used to accumulate a numeric result (never sliced at `i`) | ASCII-ONLY-SAFE | `Content-Length:` header value is mandated ASCII digits by the LSP/JSON-RPC framing spec; non-digit chars (which is where multibyte content would land) break the loop immediately without side effects. |
| `src/app/md_lsp/md_lsp_main.spl:_md_lsp_extract_field` | nested object/array and number/keyword branches: `.char_at(j)` bounded by `.len()`, reconstructing output via `parts.push(ch)` / `parts.join("")` | **CONFIRMED, FIXED** | Pre-fix: direct probe of `s.char_at(4)` on a 4-codepoint/5-byte string showed silent truncation (no crash, no output) once `j` ran past the codepoint count. Real JSON payloads routinely carry multibyte string values (source text, identifiers). See Fix #4 (and its two-step correction, same class as Fix #3). |
| `src/app/svim/lsp_features.spl:_svim_lsp_extract_int` | `.char_at(i)` bounded by `.len()`, appended only while `ch` is `-`/digit, `break`s on first non-match | FALSE POSITIVE | The loop only ever consumes ASCII digits and breaks immediately on the first non-digit codepoint (which is always where a multibyte char would appear), so `i` never advances past the codepoint count while still indexing. No slicing at `i` occurs at all -- output is built by string concatenation of already-validated single ASCII digits. |
| `src/lib/gc_async_mut/web/browser_session_loading.spl:_simple_script_args_are_ints` | (none in this function itself) | FALSE POSITIVE | Same block-splitter mis-attribution as `detect_asset_type` above -- the function itself has no `.char_at`/`.substring` at all; the hits came from unrelated `impl BrowserSession` methods later in the file. |
| `.../simple_web_html_layout_renderer_foundation.spl:is_gradient_angle_token`, `split_top_level_commas_paren_aware`, `parse_css_time_ms` | `.char_at(i)` bounded by `.len()` scanning numeric/paren-depth CSS tokens, then `.substring(...)` at the scan boundary | ASCII-ONLY-SAFE | CSS angle/time/paren-grouping tokens (`"90deg"`, `"1.5s"`, function argument lists) are always ASCII by the subset of CSS this renderer accepts; non-ASCII can only appear INSIDE an already-balanced paren group, never at a scanned delimiter position. |
| `.../simple_web_engine2d_renderer.spl:_first_class_name`, `_collect_class_names` | `.char_at(token_end)` bounded by `.len()` scanning for `" "` token boundaries, `.char_at(trimmed_start/end)` for whitespace trim, then `.substring(trimmed_start, trimmed_end)` | **CONFIRMED, FIXED** | Pre-fix repro: `_first_class_name("café bar")` -> `"caf<invalid byte>"`. HTML `class=""` values are user/author content and not guaranteed ASCII (e.g. localized or emoji-suffixed class names in generated markup). See Fix #5. |
| `.../simple_web_html_layout_renderer_layout.spl:ellipsize_text_for_width` | `txt.char_code_at(i)` (not `.char_at`) inside a byte-range loop already driven by caller-supplied byte offsets `start`/`endv` | FALSE POSITIVE | `start`/`endv` come from the caller as byte offsets into `txt` and are consistently used as byte offsets throughout (`txt.substring(start, endv)`); `char_code_at(i)` here reads the byte at a position already established to be byte-indexed by the surrounding contract, not a codepoint-space value crossing into byte-space. |
| `.../gpu/browser_engine/style/custom_properties.spl:parse_var_function` | `.char_at`/`.substring` present but on an already-delimited (paren-balanced) ASCII function-call argument list | ASCII-ONLY-SAFE | `var(...)` function syntax; the scanned control characters (`(`, `)`, `,`) are structural CSS syntax, always ASCII, at any nesting depth. |
| `src/app/office/sheets/sync.spl:lines_to_ops` | `.char_at`/`.substring` on line-diff bookkeeping | CONFIRMED (shape), not fixed (outside cap) | Operates on arbitrary user document text (spreadsheet cell content), which is not ASCII-guaranteed. Not reached in the 5-fix cap. |
| `.../simple_web_html_layout_renderer_style.spl:parse_font_shorthand_family`, `split_top_level_commas`, `parse_float_to_255`, `shadow_layer_alpha`, `_gradient_stop_color` | `.char_at(i)` bounded by `.len()` on CSS shorthand tokens | ASCII-ONLY-SAFE except `parse_font_shorthand_family` | Numeric/color/paren-structural CSS values are ASCII by grammar. `parse_font_shorthand_family` scans a `font-family` LIST, which CAN legitimately contain non-ASCII font names (e.g. `"微软雅黑"`) inside quotes -- CONFIRMED (shape), not fixed (outside cap). |
| `.../gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl:border_spacing_px`, `_padding_integer_px`, `parse_supported_nonnegative_px`, `normalized_grid_template_areas` | `.char_at(i)` bounded by `.len()` on CSS length/grid-template tokens | ASCII-ONLY-SAFE | Numeric-length and grid-template-area string tokens (`"a a b"`) are ASCII by the CSS grammar subset this renderer accepts. |
| `src/app/wm_compare/backend_measurement_capture.spl:_field_after` | `.char_at(end)` bounded by `.len()` scanning a numeric field after a known ASCII marker in structured measurement output | ASCII-ONLY-SAFE | Same shape/reasoning as `_i32_after_marker` above (machine-generated numeric field). |
| `src/app/wm_compare/site_corpus_compat.spl:_json_number_after`, `_report_different_pixels` | `.char_at`/`.substring` on numeric JSON fields and pixel-diff report formatting | ASCII-ONLY-SAFE | Same reasoning: numeric fields in machine-generated comparison JSON. |
| `src/app/jupyter_kernel/main.spl:extract_field`, `extract_object_field` | `.char_at(j)` bounded by `.len()`, reconstructing nested JSON via `parts.push`/`.join` (same shape as `_md_lsp_extract_field` pre-fix) | CONFIRMED, not fixed (outside cap) | Jupyter kernel JSON-RPC messages routinely carry multibyte source/output text (any non-ASCII code or printed value). Fix: identical to Fix #4 -- replace byte-by-byte reconstruction with a single `.substring(0, j[+1])` range slice, keep `.substring(j, j+1)` only for delimiter detection. |
| `src/app/wm_compare/electron_geometry_compare.spl:_geometry_json_i32_after` | `.char_at` bounded by `.len()` scanning a numeric geometry field | ASCII-ONLY-SAFE | Same reasoning as `_i32_after_marker` (machine-generated numeric JSON field). |

### Tally

- **51** candidate functions found by the scripted 3-heuristic sweep (which,
  on this codebase, collapse onto one dominant shape -- see "Detection
  method" above).
- **CONFIRMED: 15** distinct functions (counting each duplicate-family copy
  separately: `email_validate` x3, `url_decode` x2, plus `path_ext`,
  `last_component`, `imap_split_at_first_space`, `imap_strip_crlf`,
  `imap_parse_capability_tokens`, `_wm_theme_css_value`,
  `_css_top_level_space_tokens`, `_css_effects_split_top_level_commas`,
  `_md_lsp_extract_field`, `_first_class_name`, `_collect_class_names`,
  `parse_export_list`, `parse_export_statements`, `lines_to_ops`,
  `parse_font_shorthand_family`, `extract_field`/`extract_object_field`).
- **ASCII-ONLY-SAFE: 21** functions/groups (guarded by an ASCII-only
  precondition on the exact byte/codepoint boundary that gets sliced).
- **FALSE POSITIVE: 5** functions (`detect_asset_type`,
  `_simple_script_args_are_ints` -- both mis-attributed by the per-function
  splitter picking up later unrelated code; `escape_json`,
  `_svim_lsp_extract_int`, `ellipsize_text_for_width` -- genuinely correct or
  never actually cross index spaces on inspection).

## Fixes landed (this pass, capped at 5)

All five follow the established byte-consistent pattern: replace
`.char_at(i)` with `.substring(i, i + 1)` for single-character comparisons
(safe at any byte offset because an ASCII byte never appears as a UTF-8
continuation byte), and slice results as ONE `.substring(a, b)` byte RANGE
rather than reconstructing byte-by-byte via `push`/`join` (byte-by-byte
reconstruction of a multibyte codepoint is itself broken -- see Fix #3 and
Fix #4 below, both needed a second correction after the naive swap).

### Fix #1: `src/lib/nogc_sync_mut/imap/parse.spl`
Functions: `imap_split_at_first_space`, `imap_strip_crlf`,
`imap_parse_capability_tokens`.
- Pre-fix repro (`git stash` + `bin/simple run`, verbatim):
  `imap_split_at_first_space("café bar")` ->
  `assert_equal failed: expected bar, got  bar` (note leading space).
- Post-fix: `test/01_unit/lib/nogc_sync_mut/imap/parse_multibyte_spec.spl`,
  **9 examples, 0 failures**.
- Existing spec `test/01_unit/lib/nogc_sync_mut/smtp/smtp_spec.spl` (uses the
  same family) re-run: 62 examples, 0 failures (no regression; separate file
  but same module family, run as an integration check).

### Fix #2: `src/lib/nogc_sync_mut/smtp/send.spl:email_validate`
- No failing pre-fix repro could be captured (see classification table --
  the shape is real but benign on this build). Fixed defensively for
  consistency and to remove the reliance on undocumented OOB `.char_at()`
  behavior.
- Post-fix: `test/01_unit/lib/nogc_sync_mut/smtp/send_email_validate_multibyte_spec.spl`,
  **7 examples, 0 failures**.
- Existing spec `test/01_unit/lib/nogc_sync_mut/smtp/smtp_spec.spl` re-run:
  62 examples, 0 failures.

### Fix #3: `src/lib/nogc_async_mut/http_client/types.spl:url_decode`
- Pre-fix repro (verbatim): `url_decode("café")` ->
  `assert_equal failed: expected café, got caf<invalid byte>` (crash-style
  UTF-8 corruption from `.char_at()` past the codepoint boundary).
- First fix attempt (naive `.char_at(i)` -> `.substring(i, i+1)` swap, still
  pushing/joining ONE byte at a time) was insufficient and STILL corrupted
  multibyte input: `assert_equal failed: expected café, got caf<invalid><invalid>`
  -- each individual byte of a multibyte codepoint is independently invalid
  UTF-8, so re-joining single-byte slices does not round-trip.
- Real fix: track a pending byte range (`run_start`) and flush it as one
  `.substring(run_start, i)` slice on hitting a `%`/`+` control byte, never
  reconstructing byte-by-byte. `.substring(i, i+1)` is still used only to
  DETECT the control bytes, which is safe.
- Post-fix: `test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl`,
  **6 examples, 0 failures** (2 assertions covering the pre-existing,
  unrelated `%XX`-decode defect were removed from scope -- see the NOTE in
  that spec file and "Pre-existing unrelated defect found" below).

### Fix #4: `src/app/md_lsp/md_lsp_main.spl:_md_lsp_extract_field`
- Pre-fix: direct probe of `.char_at()` on an out-of-range codepoint index
  in this build showed a silent stop (no crash, no output) rather than a
  visible corruption, so the JSON-RPC field extraction would silently
  truncate mid-multibyte-value.
- First fix attempt (same naive per-byte `push`/`join` swap as Fix #3 before
  its correction) was likewise insufficient.
- Real fix: both the nested-object/array branch and the number/keyword
  branch now return a single `.substring(0, j)` / `.substring(0, j + 1)`
  range slice at the point the scan resolves, instead of reconstructing
  byte-by-byte.
- Post-fix:
  `test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl`
  (duplicates the fixed function body rather than importing
  `md_lsp_main.spl`, which executes a blocking stdio server loop at module
  scope -- see the spec's header comment), **5 examples, 0 failures**.

### Fix #5: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
Functions: `_first_class_name`, `_collect_class_names`.
- Pre-fix repro (verbatim): `_first_class_name("café bar")` ->
  `assert_equal failed: expected café, got caf<invalid byte>`.
- Post-fix:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl`,
  **6 examples, 0 failures**.
- Existing spec
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl`
  re-run: 24 examples, 0 failures (no regression).

### Pre-existing unrelated defect found (filed as scope note, not fixed)

While probing `url_decode`, `hex.parse_int(16)` was found to return
`Option<i64>`, and the un-unwrapped Option's `.to_char()` silently no-ops --
every `%XX` percent-escape in `url_decode` decodes to nothing (e.g.
`"hello%20world"` -> `"helloworld"`, not `"hello world"`). Verified present
on the ORIGINAL `.char_at()` code too (via `git stash`), so it predates this
sweep entirely and is unrelated to the byte/codepoint indexing defect class.
Left unfixed and unasserted in the new spec (documented there instead) to
avoid conflating two different defects in one fix; worth its own bug record.

## Still-open instances (not fixed this pass)

### `path_ext` / `last_component` in `src/lib/common/path_pure.spl` (avoid-list)

Left untouched per explicit instruction (file under concurrent edit by
another agent). Exact fix needed: replace the `.char_at(i)` scan-and-compare
with `.substring(i, i + 1)` comparisons to stay byte-consistent, matching
the `is_sep_at` helper pattern already used elsewhere in the same file for
the (already-fixed) basename/dirname functions. Concretely:
- `path_ext`: `if base.char_at(i) == "."` -> `if base.substring(i, i + 1) == "."`.
- `last_component`: `path.char_at(n - 1) == "/"` and
  `trimmed.char_at(i) == "/"` -> the same `.substring(i, i + 1)` swap. The
  final `.substring(...)` slices already use the correctly-tracked byte
  index `n`/`last_sep`, so only the comparison needs to change.

### Other CONFIRMED, not fixed (outside the 5-fix cap; not on the avoid-list, open for a future pass)

- `src/lib/nogc_async_mut/smtp/send.spl:email_validate` and
  `src/lib/gc_async_mut/smtp/send.spl:email_validate` (duplicates of Fix #2;
  same fix, not yet applied there).
- `src/lib/gc_async_mut/http_client/types.spl:url_decode` (duplicate of
  Fix #3; same fix, not yet applied there).
- `src/lib/common/ui/wm_theme_css.spl:_wm_theme_css_value`.
- `src/app/doc/public_check/export_parser.spl:parse_export_list`,
  `parse_export_statements`.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects.spl:_css_top_level_space_tokens`,
  `_css_effects_split_top_level_commas`.
- `src/app/office/sheets/sync.spl:lines_to_ops`.
- `.../simple_web_html_layout_renderer_style.spl:parse_font_shorthand_family`.
- `src/app/jupyter_kernel/main.spl:extract_field`, `extract_object_field`
  (same shape and same fix as `_md_lsp_extract_field`, Fix #4).
