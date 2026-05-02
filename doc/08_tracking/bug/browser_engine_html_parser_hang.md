# Bug Report: Browser Engine HTML Parser Hang in Compiled Mode

**ID**: BUG-BROWSER-PARSER-HANG  
**Severity**: High  
**Status**: Partially Fixed (verification 2026-04-27)  
**Date**: 2026-04-09  
**Component**: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`

## Verification Update — 2026-04-27

The "Proposed Fix Options" section below was partially incorrect. After
hands-on investigation this session, two options needed correction and
several fixes were applied. Original option text is preserved below for
historical reference; see inline `**Note (2026-04-27):**` callouts.

### Corrections to original options

- **Option A is unnecessary as a runtime change.** A pure-Simple
  string builder already exists at
  `src/lib/common/string_builder.spl` (`common.string_builder.StringBuilder`)
  with `new()`, `push(part)`, `to_text()`, `is_empty()`, `clear()`. No
  new `rt_string_builder_*` extern is required — just import and use it.
- **Option D is not a perf win.** Both `rt_slice` and
  `rt_string_char_at` call `rt_string_new` identically (see
  `src/compiler_rust/runtime/src/value/collections.rs:1249` and `:718`),
  so substituting one for the other allocates the same. The
  substitution IS still valuable as a **UTF-8 correctness fix** because
  `rt_slice` does byte indexing while `rt_string_char_at` is
  codepoint-aware — but it does not reduce allocation count.

### What was applied this session

- Commit `vqvnsrmo` — `rt_slice` identity fast path: a full-string
  slice (`slice(0, len)`) returns the original heap pointer instead of
  copying. Mark-sweep GC handles the aliasing safely. The same fast
  path was added to the interpreter's `slice` handler. Smoke test:
  100K identity slices on a 5.2KB string → 1.08s wall, 17 MiB peak RSS.
- Commit `rmn` — UTF-8 correctness sweep: replaced `slice(i, i+1)`
  hot-loop calls with `char_at(i)` across `browser_engine`, plus
  StringBuilder conversion of 5 loops in
  `widget_to_dom.spl` (`split_tag_parts`, `split_spaces`,
  `split_semicolons`).
- Commit `rvx` (96f240a) — StringBuilder conversion of 14 tokenizer
  loops in `dom.spl` and `style_block.spl`:
  `strip_css_comments`, `dom_split_ws`, `split_comma`,
  `sb_dom_split_ws`, `split_top_level_commas` (×3),
  `split_shadow_tokens` (×3), `calc_tokenize`, `calc_split_muldiv`,
  `sb_split_char`, `sb_split_ws`.

### What is still pending

- `rt_string_new(_, 0)` shared empty-string interning — **deferred**.
  Needs GC root-set integration; the mark-sweep tri-color GC currently
  has no clean hook for permanently-rooted objects.
- ASCII single-char cache in `rt_string_new` (Option C-style) — **deferred**
  for the same root-set reason.
- Concat-in-loop sites in `src/lib/common/*` (`rope`, `fraction`,
  `base64`, `color`, `rich_text`) — **in progress** in a parallel
  agent F sweep.

## Summary

The browser engine HTML parser hangs (infinite loop or extreme slowness) when compiled with `native-build` and run natively. The parser successfully starts processing HTML but never returns from the tag-parsing phase. This blocks the entire HTML-to-pixel rendering pipeline.

## Reproduction

```bash
cd /path/to/simple

# Build (succeeds — 35 files, 0 failures)
SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/bootstrap/simple native-build \
  --source src/lib --source src/compiler --source test/integration/rendering \
  --entry test/integration/rendering/pixel_verify_browser_glass.spl \
  -o /tmp/test_browser_glass \
  --backend cranelift --runtime-bundle all --entry-closure --no-incremental

# Run (hangs after first tag parse)
timeout 60 /tmp/test_browser_glass
```

### Output before hang

```
=== Browser Engine Glass Theme Pixel Verification ===

=== Test 1: Red div background ===
  html1 len=74
  html1 slice(0,5)='<div '
  calling render_html_to_pixel_array...
[OT] enter 'div style="background-color:#FF0000; width:100px; height:100px"'
```

The process then consumes 100% CPU and never produces further output. Must be killed with `kill` or `timeout`.

## Root Cause Analysis

### Call chain where hang occurs

1. `render_html_to_pixel_array(html, 200, 200)` in browser_renderer.spl:421
2. `browser_renderer_html_string_to_dom(html)` — HTML parser entry
3. `br_handle_open_tag(...)` at line 567: prints `[OT] enter` then calls...
4. `browser_renderer_parse_tag(clean_content)` at line 574 — parses tag name + attributes
5. Inside `browser_renderer_parse_tag` (line 660):
   - `browser_renderer_split_tag_parts(content)` at line 661 — splits tag into parts
   - `browser_renderer_apply_inline_style(node, value)` at line 684 — applies `style="..."` attribute

### Hang location: `browser_renderer_split_tag_parts` (line 690)

This function iterates character-by-character using `text.slice(idx, idx+1)`:

```simple
fn browser_renderer_split_tag_parts(s: text) -> [text]:
    var parts: [text] = []
    var current = ""
    var in_quote = false
    var quote_char = ""
    var idx_1 = 0
    while idx_1 < s.len():
        val ch = s.slice(idx_1, idx_1 + 1)      # <-- hot loop
        if in_quote:
            current = "{current}{ch}"              # <-- string concat per char
            ...
        idx_1 = idx_1 + 1
    ...
```

For a tag like `div style="background-color:#FF0000; width:100px; height:100px"` (74 chars), this loop:
- Calls `text.slice()` 74 times (each allocates a new string via `rt_string_new`)
- Calls `text == text` 74+ times for quote matching
- Builds result via `"{current}{ch}"` string interpolation (each iteration allocates and copies the growing string — O(n^2) memory allocation)

### Why it's slow in compiled mode

1. **O(n^2) string concatenation**: `current = "{current}{ch}"` copies the entire accumulated string on every character. For a 74-char tag, this allocates ~2700 characters total (1+2+3+...+74).

2. **No string builder/buffer**: The runtime `rt_string_new` allocates a new heap object per slice. With 74 slices + 74 concatenations = 148 heap allocations for ONE tag parse.

3. **Recursive HTML structure**: A simple `<div style="...">red</div>` has 3 parse events (open tag, text, close tag). A glass theme test HTML has 50+ elements, each with inline styles containing 10+ CSS properties. Total: 500+ tag parses x 148 allocations = 74,000+ heap allocations.

4. **Cross-module overhead**: After the Phase A-E FieldGet fixes, `browser_renderer_apply_inline_style` now correctly calls `be_dom_set_style(node, prop, value)` which calls into dom.spl's `set_style` method. This method calls `parse_css_value(value)` and `parse_color_value(value)` from css.spl — each of which does its own character-by-character parsing (hex color parsing, number parsing, unit detection). The overhead compounds.

### Estimated per-tag cost

| Operation | Calls per tag | Allocs per call | Total allocs |
|-----------|--------------|-----------------|-------------|
| `text.slice(i, i+1)` | 74 | 1 | 74 |
| `"{current}{ch}"` concat | 74 | 1 | 74 |
| `parse_color_value` | 1-2 | ~20 | 20-40 |
| `parse_css_value` | 3-5 | ~10 | 30-50 |
| **Total per tag** | | | **~200-240** |

With 50+ tags in glass theme HTML: **~10,000-12,000 heap allocations** just for parsing.

### Why interpreter mode doesn't hang

The interpreter uses a different string implementation (Rust `String` with in-process allocation) that doesn't go through `rt_string_new`/`rt_slice` FFI. String concatenation in the interpreter reuses the Rust allocator's fast path. The native compiled binary uses the runtime's `HeapObject`-based string allocation which has higher per-allocation overhead.

## Impact

- **Blocks**: Browser engine HTML-to-pixel rendering pipeline in compiled mode
- **Does NOT affect**: 
  - Direct scene rendering (scene_fill_rect → pixels) — works perfectly (21/21 tests pass)
  - Programmatic DOM creation (BeDomNode.element + set_style) — works for small DOMs
  - Interpreter mode — HTML parsing works (just slower overall)

## Workaround

1. **Use direct scene commands** instead of HTML parsing for pixel rendering tests (glass_pixel_runner.spl does this — 21/21 pass)
2. **Use programmatic DOM** construction instead of HTML strings
3. **Minimize HTML complexity** — simple `<div style="color:red"></div>` might work; complex glass theme HTML with 50+ elements does not

## Proposed Fix Options

### Option A: String builder runtime function (recommended)
Add `rt_string_builder_new()`, `rt_string_builder_append_char()`, `rt_string_builder_to_string()` to the Rust runtime. Replace O(n^2) concatenation with O(n) buffer append.

**Note (2026-04-27):** No new runtime is needed. A pure-Simple
`common.string_builder.StringBuilder` already exists at
`src/lib/common/string_builder.spl` (`new()`, `push(part)`, `to_text()`,
`is_empty()`, `clear()`). The O(n) buffer-append approach is what was
actually applied in commits `rmn` and `rvx` — see Verification Update.

### Option B: Batch inline style parsing
Instead of parsing `style="..."` character-by-character, add a runtime function `rt_parse_inline_style(style_str) -> [(key, value)]` that returns all property-value pairs in one call. This moves the parsing to Rust (fast) and returns structured data.

### Option C: Optimize rt_string_new/rt_slice
The current `rt_slice` allocates a new `RuntimeString` for every call. For single-character slices, a fast path could return a cached single-char string (only 128 possible ASCII chars).

### Option D: Use text.char_at() instead of text.slice(i, i+1)
If `rt_string_char_at` returns an integer (char code) instead of a string, the hot loop can compare integers instead of allocating strings. Rewrite `browser_renderer_split_tag_parts` to use `char_at()` + integer comparison.

**Note (2026-04-27):** This option turned out to be a wash for
allocation count. In the current runtime, `rt_string_char_at` calls
`rt_string_new` exactly like `rt_slice` does
(`src/compiler_rust/runtime/src/value/collections.rs:1249` and `:718`),
so swapping the two does not reduce allocations. The substitution IS
worth doing as a **UTF-8 correctness** fix (`rt_slice` is byte-indexed,
`rt_string_char_at` is codepoint-aware) and was applied in commit
`rmn`. The integer-char-code variant described above (returning an
`int` codepoint with no `rt_string_new`) would still be a real perf
win and remains a viable future option.

## Related Files

| File | Role |
|------|------|
| `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | HTML parser, render entry point |
| `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | DOM node, set_style method |
| `src/lib/gc_async_mut/gpu/browser_engine/css.spl` | CSS value parsing |
| `src/compiler_rust/runtime/src/value/collections.rs` | rt_slice, rt_string_new |
| `test/integration/rendering/pixel_verify_browser_glass.spl` | Test that triggers the hang |
| `test/system/gui/glass_pixel_runner.spl` | Workaround test (uses direct scene commands) |

## Related Bugs

- **Cross-module FieldGet** (fixed): Was causing all-white rendering. Fixed by import loader transitive deps + explicit imports.
- **LLVM text.slice() empty return** (fixed): Missing step=1 default in rt_slice call.
- **parse_f64 stub** (fixed): rgba alpha parsing returning garbage.
