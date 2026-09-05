# be_dom path-event family broken by ctor arity; serialize drops <style> text

Status: FIXED (was OPEN P2). Filed 2026-08-19 (found by the chrome counter
component harness, tools/component_diff/CONTRACT.md).

## Fix (2026-09-02, fix/bugdb-batch-g)

The file actually implementing this is
`src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` (not
`gc_async_mut/web/dom_accessors.spl`, which does not exist — same code, path
typo in the original filing).

1. Both wrong-arity call sites fixed to the real 4-param
   `BeDomEvent.create(event_type, namespace_uri, bubbles, cancelable)`
   signature, then set `target_id`/`current_target_id`/`target_tag`/
   `current_target_tag` on the returned struct (mirroring how `target_tag` was
   already being set post-construction):
   - `be_dom_create_event` (~line 612)
   - `_be_dom_dispatch_event_path_with_executor`'s empty-path fallback
     (~line 903), which called `BeDomEvent.create` directly with the same
     wrong 7-arg shape and was not mentioned in the original filing but has
     the identical defect.
2. `<style>` used to be entirely dropped by the HTML tree builder
   (`skipped_raw_text_tag`, `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`)
   — it never became a DOM node at all, so `be_dom_serialize_html` could not
   possibly re-emit it (there was nothing in the tree to walk). Fixed by
   giving `<style>` the same real-element-plus-text-child treatment `<script>`
   and `<title>` already get: a `style` element node is pushed on start tag,
   its raw character data is accumulated, and on the matching end tag it gets
   one `#text` child carrying the accumulated CSS — exactly mirroring the
   pre-existing `<script>` content-collection code immediately above it.
   `<noscript>` is untouched (still fully skipped) — it was not in scope.
   `_token_would_create_node`'s truncation heuristic updated to match (style
   now creates a node; only noscript still doesn't).
   Layout/paint already defensively excluded `style` from the rendered set
   (`simple_web_html_layout_renderer.spl:99`,
   `simple_web_html_layout_renderer_foundation.spl:950`,
   `simple_web_html_layout_renderer_style.spl:343`), and the CSS cascade
   extractor (`style_block_parse.spl`) scans the raw HTML *text*, not the
   BeDomNode tree — so making `<style>` a real DOM node is purely additive to
   serialize output and does not change what CSS gets applied or make style
   text visible on the page.
3. Serializing the new `<style>` text child through the generic `#text` path
   would have entity-escaped it (`_be_dom_push_escaped_html` -> `html_escape_core`
   escapes `& < > " '`), corrupting any CSS containing a child combinator
   (`.a > .b`) or a quoted attribute selector (`[data-x="y"]`) into something
   the raw-text cascade extractor cannot parse back — the same
   re-layout-against-broken-CSS failure this bug describes, one level deeper.
   Per HTML5, `<script>`/`<style>` content is raw text (CDATA), not markup,
   and must serialize unescaped (the tokenizer already treats it this way —
   `html_tokenizer.spl` puts `style`/`script` into a raw-text state, so `>`/`"`
   inside one are never parsed as tag/attribute syntax to begin with). Added
   `_be_dom_push_raw_html` and threaded the parent tag name through
   `_be_dom_open_html_node`'s tree walk so a `#text` node under a
   `script`/`style` parent is emitted verbatim instead of escaped. (This also
   fixes the identical pre-existing escaping bug for `<script>` content, which
   went through the same generic `#text`-escaping path and was not previously
   reported.)

New regression spec:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/be_dom_event_path_and_style_serialize_spec.spl`.

**Verification caveat:** could not execute the spec on this host. The deployed
self-hosted binary (`bin/release/aarch64-apple-darwin/simple`) fails every
spec run — including a one-line `expect(1+1).to_equal(2)` control, and
reproduced identically from `/Users/ormastes/simple` (main repo checkout, not
just this worktree) — with `error: semantic: variable `always_inline` not
found`, a pre-existing stdlib/binary skew unrelated to this fix (the current
`src/lib/nogc_sync_mut/io_runtime.spl` uses `@always_inline`, which the
deployed binary's parser does not support). The fix above is verified by
direct source-level reasoning: reading the real `BeDomEvent.create` signature
and confirming both call sites now match it; reading the layout/paint
exclusion lists and the cascade's raw-text CSS extractor to confirm the
`<style>` DOM-node addition is additive-only and cannot leak into rendering.

1. `be_dom_create_event` (src/lib/gc_async_mut/web/dom_accessors.spl ~615) calls
   `BeDomEvent.create` with 7 args against a 4-param signature — the whole
   path-based `be_dom_dispatch_event_path` family fails at runtime ("unknown
   static method create"). The typed-route family works and is what the
   harness (and browser session) use. Fix the arity or delete the dead family.
2. `be_dom_serialize_html` drops `<style>` element text content, so mutated
   DOM states re-layout against the pristine fixture's static CSS instead of
   the serialized document's.

Repro: tools/component_diff/run_component_diff.shs (see CONTRACT.md).
