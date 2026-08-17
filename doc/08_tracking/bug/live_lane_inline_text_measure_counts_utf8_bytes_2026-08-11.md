# Live browser lane measures inline text by UTF-8 BYTES, not characters

- **Date:** 2026-08-11
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
- **Found while:** closing blocker 1 (inline text measurement) of
  `doc/03_plan/ui/rendering/blink_wiring_plan.md`

## The primitive mismatch

`text.len()` is BYTE length. `text.char_code_at(i)` is CODEPOINT indexed.
Measured directly on `bin/simple run`:

    val s = "aé漢"
    s.len()             -> 6      # bytes
    s.char_code_at(0)   -> 97     # 'a'
    s.char_code_at(1)   -> 233    # 'é'
    s.char_code_at(2)   -> 28450  # '漢'
    s.char_code_at(3..5)-> 0      # past the end

So `while i < s.len(): s.char_code_at(i)` iterates 6 times over a 3-character
string and reads three phantom zeros.

## The two defective call sites

1. `inline_text_advance_width` (`:492`) loops `while i < raw.len()` calling
   `raw.char_code_at(i)`. For `"aé漢"` at 16px it charges 6 advances (2 of them
   for codepoint 0, which is not a character at all) instead of the correct 4
   drawn columns.
2. `intrinsic_text_width` (`:462`) computes `txt.len() * ink_w` — a straight
   byte count, with the same inflation.

`text_line_advance_width` (`:552`) takes caller-supplied `start`/`endv`
indices, so it inherits whichever framing its caller used; its callers frame by
`len()`.

## Impact

Every non-ASCII run is over-measured by its UTF-8 inflation factor: ~1.5-2x for
Latin-1 accents and Greek/Cyrillic, 3x for CJK and most emoji. The consequence
is over-wide intrinsic widths, premature line wrapping, and mis-centred
`text-align: center` on any page that is not pure ASCII. It is a wrong value
rather than a failure, so no smoke test sees it. Additionally, a CJK glyph is
drawn double-width but the byte count charges it triple, so the error does not
even coincidentally cancel.

## Why it is not fixed here

Correcting it changes live-lane pixel output on every non-ASCII page, so it
must land against the Electron bitmap evidence gates
(`check-electron-simple-web-layout-bitmap-evidence.shs`), not against a
per-file spec run. That is Stage 1 of the wiring plan, which is explicitly
gated on those bitmap gates.

## What was done instead

The correct measurement landed as a new shared leaf,
`src/lib/common/layout/text_metrics.spl`, which iterates codepoints and applies
a wide/zero-width column policy. blink consumes it through
`src/lib/blink/layout/inline_text.spl`. Proven by
`test/01_unit/lib/blink/inline_text_spec.spl` (41/41), which asserts precisely
the cases this defect gets wrong: `"é"` measures the same as `"e"`, `"漢"`
measures exactly twice `"a"`, and a combining accent adds nothing.

**Consequence for the wiring plan:** Stage 3's stated acceptance criterion —
"measure the same strings through both lanes and assert equal advance widths
within 1px" — CANNOT hold for non-ASCII input, and must not be made to hold by
reintroducing the byte count into blink. Parity is achievable for ASCII only
until this defect is fixed on the live side. The plan's acceptance text should
be amended to say so.

## Sweep and fix (2026-08-11, same day)

The family was enumerated repo-wide with unrestricted `/usr/bin/grep` over
`src/` and `examples/` (the wrapped `grep` honours `.gitignore` and
under-reports). 137 sites mix the two index spaces, but the overwhelming
majority are ASCII-only crypto/protocol/hash parsers where the mix is a
byte walk by intent. The **pixel-advance measurement** family — contract (1)
in `common/layout/text_metrics.spl` — is these:

| site | contract | state |
|------|----------|-------|
| `browser_engine/..._layout_renderer_layout.spl` `intrinsic_text_width` | pixel advance | FIXED — `text_cell_width` |
| same file `inline_text_advance_width` | pixel advance | FIXED — `text_codepoints` + `codepoint_cells` |
| same file, `resolved_font_advances.len() == raw.len()` arity guard | pixel advance | FIXED — compares CODEPOINT count |
| `text_layout/font_renderer.spl` `measure_text_width` | pixel advance | FIXED |
| same file `measure_text_advances` | pixel advance | FIXED |
| same file `render_text` | pixel advance | FIXED |
| same file, two `render_text_payload` fallback layout loops | pixel advance | FIXED |
| same file `resolve_font_metrics_*` `character_count` | pixel advance | FIXED |
| `engine2d/helpers/text_fallback.spl` `measure_text` | pixel advance | FIXED — `text_cell_width` |
| `game2d/render/font.spl` `Font.measure` | pixel advance | FIXED — `text_cell_width` |
| `engine2d/helpers_text.spl` `text_metrics` | pixel advance | **STILL OPEN — see below** |

`app/ui.render/layout.spl text_width`, `app/ui.tui/screen.spl _visible_width`
and the `pad_to_width` family were deliberately NOT touched: they are contract
(2), ANSI-stripped visible columns, which counts CJK as one column and strips
ESC runs. Merging them into the pixel lane would be a behaviour change, not a
dedupe. `common/ui/draw_ir.spl` already counts with `for ch in text_value`
(codepoints) and needed nothing.

### Evidence

`bin/simple test <file>` is FAIL-OPEN here: the new spec AND the known-good
41/41 `test/01_unit/lib/blink/inline_text_spec.spl` both emit **zero verdict
lines** on the seed binary, so a green-looking run proves nothing. The fix was
measured instead by direct execution, with a sabotage control:

- fixed:    `measure_text_advances("aéb")` -> 3, `("漢字")` -> 2
- sabotaged (one loop bound restored to `content.len()`):
            `("aéb")` -> **4**, `("漢字")` -> **6**

The 6-for-2 is the documented 3x CJK inflation reproduced exactly, and it
confirms the assertions are a real oracle rather than a tautology.

### `engine2d/helpers_text.spl` is NOT fixed — two blockers

1. **Measurement and rendering would desync.** `text_render_metrics_to_buf`
   and `text_render_metrics_to_buf_scale1` iterate `text_val.len()` bytes with
   `char_code_at(i)` to DRAW. Changing only the width would make the buffer
   width disagree with the glyphs blitted into it — a different wrong value,
   not a fix. Both loops have to move together.
2. **Edits to that module do not reach the running code.** Rewriting
   `char_count` left the observed value at the byte count, and a sentinel
   constant (`char_count = 99`) never appeared at the call site either. The
   cause is module resolution, not the source: a `use` of the browser layout
   module resolves parts of the stdlib out of a SHADOW ROOT,
   `/mnt/data/build-clean/src/lib/**`, whose copy of this file is stale. The
   same session's edits to `text_layout/font_renderer.spl` DID take effect
   (proven by sabotage), so the shadowing is per-path, not global — which makes
   any measurement here unverifiable until it is understood. Do not "fix" this
   site without first confirming which root the running process read.

   This shadow root is also a general measurement trap for this repo: an edit
   under the work tree can be silently invisible to `bin/simple run`.

Filed here rather than half-fixed, because a measurement-only change to this
module is a regression.

## Row triage 2026-08-17 — assigned file `src/lib/blink/layout/inline_text.spl` is ALREADY_FIXED

`src/lib/blink/layout/inline_text.spl` contains no byte-bounded measurement.
It imports the codepoint-correct shared leaf and measures through it:

```simple
use std.common.layout.text_metrics.{
    TextMetrics, monospace_metrics, measure_text, baseline_offset_px,
    wrap_text_lines, wrap_line_end, measure_range, text_cell_width
}
```

Its own loops are bounded by codepoint arrays (`cps.len()`), not by
`text.len()`. Nothing to fix in that file.

The remaining OPEN sites are `src/lib/gc_async_mut/gpu/browser_engine/**`
(out of scope for this lane) and `src/lib/gc_async_mut/gpu/engine2d/
helpers_text.spl`, which this doc already documents as NOT safely fixable in
isolation: its measurement and its draw loops (`text_render_metrics_to_buf`,
`..._scale1`) both walk `text_val.len()` bytes and must move together, and
edits to that module were measured NOT reaching the running process (a
`/mnt/data/build-clean/src/lib/**` shadow root). Left as filed — a
measurement-only change there is a regression, and the shadow-root trap makes
any local measurement unverifiable.

Class-level regression coverage added for the byte-vs-codepoint contract this
bug and `text_byte_len_vs_codepoint_index_family_2026-08-06.md` share:
`test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl`.

## RESOLVED — verified by content + execution 2026-08-17 (lane m7c_lib_async)

Both defective call sites named above now measure CELLS, not bytes, in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`:

- `intrinsic_text_width` (:463-479) computes
  `width + (text_cell_width(txt) as i32) * ink_w` — the byte-count
  `txt.len() * ink_w` is gone, with an in-source comment stating the CJK
  double-width / combining-mark-zero policy.
- `inline_text_advance_width` (:504-534) now builds `val cps = text_codepoints(raw)`
  and loops `while i < cps.len()` over codepoints, accumulating
  `codepoint_cells(ch) as i32 * advance`. The advance-array arity check at :513
  compares against `cps.len()`, not `raw.len()`.

Both consume the shared leaf via line 15,
`use std.common.layout.text_metrics.{codepoint_cells, text_cell_width}`.
`src/lib/blink/layout/inline_text.spl:80` likewise delegates to `text_cell_width`.

Executed proof (`bin/simple run`, seed):

    val s = "aé漢"
    s.len()            -> 6      # bytes
    text_cell_width(s) -> 4      # cells — exactly the "correct 4 drawn columns"
                                 # this doc asked for

Status: RESOLVED. No source change was needed by this lane.
