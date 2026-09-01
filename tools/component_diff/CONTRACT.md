# Chrome ↔ Simple per-component IO differential — contract

Per-COMPONENT harness on top of the per-stage tools (`tools/layout_diff` et
al.): one interactive widget fixture is loaded by both engines, its IO is
driven through each engine's REAL event path, and the resulting box geometry
is compared per interaction state as canonical text.

## Component set

The driver iterates EVERY `fixtures/*.html` (or one via `--component`),
writing per-component evidence to `out/<name>/{chrome,simple}/` plus
`out/<name>/summary.txt`. Interactions are declared IN each fixture
(`<meta name="component-actions" content="click:#id,fill:#id:value">`,
`<meta name="component-observe" content="<idOfObservedElement>">`); the
Simple side mirrors them per-component in `simple_component_dump.spl`
(`component_step`/`component_steps`/`component_observe`) and the driver's
`states_of` table must agree.

| component | states | exercises |
|---|---|---|
| counter | 3 | click dispatch, set-text/set-attr, re-layout, roundtrip |
| button | 2 | click default action, label mutation (hover deliberately skipped: the typed-route path has no hover pipeline) |
| text_input | 2 | `input` event route, value attr, echo text, caret-area class widening |
| checkbox | 3 | `input-checkbox-toggle` default action, checked attr toggle, roundtrip |
| list | 3 | class-toggled `display:none` add/remove of an item → REFLOW of following siblings, roundtrip (the production applier has no append-child/remove-child action, recorded limitation) |
| table | 1 | static 2x3 table layout — currently a REAL divergence, see bug below |
| float_text | 1 | left float + wrapping text — currently a REAL divergence, see bug below |

Two REAL layout defects (not pixel classes) surfaced by the set and filed:
`doc/08_tracking/bug/browser_engine_table_layout_cells_stacked_vertically_2026-08-19.md`
(td/tr laid out as stacked blocks) and
`doc/08_tracking/bug/browser_engine_float_no_inline_wrap_beside_float_2026-08-19.md`
(no line-box wrapping beside a float). Their full-divergence baselines are
pinned fail-closed until fixed.

Retention nuance: Chrome's DOMSnapshot layout tree OMITS `display:none`
subtrees; Simple's engine produces a positioned 0x0 box for them, so the
Simple extractor drops nodes whose computed `display` is `none` (ancestor
walk) to match.

Chrome under measurement: Google Chrome for Testing 151.0.7922.34, headless,
viewport 800×600, `deviceScaleFactor: 1`, `--force-device-scale-factor=1`,
`--disable-lcd-text`, `--font-render-hinting=none`.

## States

| state | produced by (Chrome) | produced by (Simple) |
|---|---|---|
| 0 | fixture as loaded | fixture through `parse_html → extract_css_vw → compute_styles → layout` |
| 1 | `page.click('#inc')` (real input pipeline, real inline-JS `bump(1)`) | typed-route click dispatch + counter model (below), re-serialize, re-layout |
| 2 | `page.click('#dec')` | same, `bump(-1)` |

## Simple's event path (and its honestly-stated gap)

The Simple side goes through the engine's production event machinery:
`html_tree_builder_build → dom_identity_index_build → route_for_author_id →
be_dom_dispatch_event_to_route` (capture/target/bubble phases; the dispatch
must collect the fixture's REAL inline `onclick` source and yield the
`button-activate` default action — both are recorded as `dispatch_*` keys in
`out/<name>/summary.txt` and asserted by the spec). The DOM update is applied with
the production applier `script_host_apply_action_to_route`
(`set-text:`/`set-attr:` listener actions).

**Gap, recorded not papered over:** Simple's engine does not execute
arbitrary inline JS, so the counter's next display string is computed by the
extractor from the DOM's `data-count` attribute, mirroring the fixture's
`bump()`/`setCount()` JS exactly. The JS-execution step is the ONLY modelled
link; everything before (dispatch) and after (DOM mutation, re-layout) is
the real engine. Display-text agreement with Chrome's real JS at every state
is asserted (`display_match=3`).

Two further engine defects surfaced while building this, worth their own
fixes:

1. `be_dom_create_event` (dom_accessors.spl) calls `BeDomEvent.create` with
   7 arguments against a 4-parameter signature, so the whole path-based
   `be_dom_dispatch_event_path` family fails at runtime under `bin/simple
   run` ("unknown static method create"). The typed-route dispatch family
   does not have this bug and is what this harness (and BrowserSession) use.
2. `be_dom_serialize_html` drops `<style>` element text content, so a
   re-serialized document loses its stylesheet. The harness re-layouts
   mutated states with the PRISTINE fixture's CSS (static by construction
   for this component) and the DOM from the serialized tree.

## Canonical geometry text form

One line per retained node, lexicographically sorted (order-insensitive):

    <key> [x,y wxh] "<normalized text, 40 chars max>"

- Keys per `tools/layout_diff/CONTRACT.md`: `#<id>`, else
  `<parentKey>/<tag>[<ordinal>]` over retained nodes; document root
  normalized to `#root` and excluded from geometry.
- Chrome coordinates are `Math.round`ed to integer css px (Simple is integer
  css px end-to-end); doctype nodes are dropped on the Chrome side (they
  report nodeName "html" and would shift the `<html>` ordinal).
- Dropped on both sides: `head`/`meta`/`style`/`script`/`title`/`link`/`base`
  subtrees and whitespace-only text nodes.
- Text content is whitespace-collapsed, trimmed, truncated at 40 chars.

Differ: `component_geom_diff.spl` via the std debugging tool
`layout_text_diff` (`src/lib/common/ui/layout_text_render.spl`); each state's
diff is retained at `out/counter/counter.stateK.diff.txt`.

## Measured baseline (counter, Chrome 151.0.7922.34)

9 node lines per state; 5 of 9 EXACT (`#counter`, `#display`, `#inc`, `#dec`,
`#root/html[0]`); 4 divergent pairs = 8 diff lines per state, stable across
all three states (`divergent_total=24`), all in known classes:

| pair | class |
|---|---|
| `#root/html[0]/body[0]` | body margin/height resolution (`[0,10 800x120]` vs `[0,0 800x140]`) |
| `#display/#text[0]` | text line height (17 vs 20; x,w exact) |
| `#inc/#text[0]`, `#dec/#text[0]` | Simple does not center button text; line height |

These are pinned fail-closed in the spec (may shrink, must not grow).

## IO invariants (asserted per engine)

- Clicking `#inc` CHANGES geometry (`geometry_changed_*=1` — the display
  text node's box grows).
- Clicking `#dec` afterwards returns geometry EXACTLY to state 0
  (`roundtrip_*=1`).
- Display text agrees between Chrome's real JS and Simple's session event
  path at all 3 states (`display_match=3`).

## Vacuity guards

`component_geom_diff.spl` exits 3 and writes `verdict=ERROR` if it compared
0 states or 0 node lines; `run_component_diff.shs` exits 4 with no Chrome, 5
if the Simple extraction produced no complete state output. The spec
fail-closes on missing/stale evidence and on a chrome side without a real
`Chrome/<version>` string.

## Running it

```sh
sh tools/component_diff/run_component_diff.shs   # ~2 min
bin/simple test test/03_system/browser_engine/chrome_counter_component_spec.spl
```
