# Live browser lane measures inline text by UTF-8 BYTES, not characters

- **Date:** 2026-08-11
- **Status:** OPEN (measured, not fixed — fixing it changes live-lane pixel output)
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
