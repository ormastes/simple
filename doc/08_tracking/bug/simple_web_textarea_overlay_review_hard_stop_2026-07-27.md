# Simple Web textarea overlay review hard stop

**Status:** open / fail-closed  
**Affected goal:** WM glass theme on host and SimpleOS  
**Iteration state:** three-cycle cap reached  
**Integration state:** rejected commits are not integrated

## Scope

An isolated lane attempted to extend the reviewed single-line input overlay
owners to production `<textarea>` rendering, editing, selection, caret, and
worker state. The three source commits are:

- `32063ae68a` — initial multiline overlay;
- `259c3e07be` — raw DOM text, multiline geometry, scroll, docs, and first
  cohesive extraction;
- `87a73e9d0d` — CRLF mapping, persistent horizontal reveal, and final
  sub-800-line owner split.

No commit was integrated or pushed. No admitted self-hosted runtime was
available, so no executable, pixel, event, or timing PASS exists. The discovered
test executable identified as the forbidden Rust seed and was not reused.

## Repairs completed statically

Independent review found the final candidate had repaired the earlier
functional defects:

- exact raw textarea descendant text preserves whitespace, LF/CRLF/lone CR,
  `&`, `<`, and non-ASCII bytes;
- CRLF is one logical edit/render newline without a visible `\r` column;
- newline-only selection emits a visible rectangle;
- per-line left/center/right/RTL geometry and later-line pointer placement are
  independent;
- vertical row and persistent horizontal reveal state are independent;
- readonly/disabled, stable author/body-path identity, DOM rebind, clipping,
  theme colors, CPU/Draw IR ordering, single-line input, and password behavior
  remain represented;
- compatibility owners were reduced to 112 and 792 lines.

These are candidate facts only, not landed behavior or runtime evidence.

## Final review rejection

The final cycle still had two P1 release blockers:

1. `simple_web_html_draw_ir_painter.spl` imported the CPU framebuffer owner
   `simple_web_html_layout_pixel_painter.*` and consumed its helpers. This
   reverses the intended owner graph: CPU pixels and Draw IR must both depend on
   a renderer-neutral shared paint/clip owner, never on each other.
2. `browser_text_control.spl` introduced direct
   `rt_text_to_bytes`/`rt_bytes_to_text` externs inside a
   `gc_async_mut` feature helper. New feature code must reuse the text/runtime
   facade (`text.bytes()` plus source-text slicing is already available) rather
   than declare a private runtime boundary.

Per the mandatory cap, there is no fourth repair cycle in this lane.

## Fresh-lane resume contract

Start from current `origin/main`, not from a piecemeal cherry-pick. Reapply the
reviewed functional behavior while:

1. extracting neutral text-control paint/clip helpers used independently by
   the CPU pixel and Draw IR owners;
2. proving neither owner imports the other or the compatibility aggregator;
3. replacing both direct `rt_*` declarations with existing text/facade
   operations and passing working plus staged direct-runtime guards;
4. retaining the exact raw-text, CRLF, newline-only selection, per-line
   alignment/RTL, sequential horizontal-state, readonly/disabled, DOM-rebind,
   single-line, and password regressions;
5. keeping the two compatibility owners below 800 lines;
6. updating the authoritative WM plan/manual without claiming runtime PASS;
7. obtaining independent highest-capability review before integration.

Live completion still requires an admitted source-matched pure-Simple runtime,
focused executed specs, computed-style/Draw-IR evidence, framebuffer pixels,
native events, timing, and RSS.
