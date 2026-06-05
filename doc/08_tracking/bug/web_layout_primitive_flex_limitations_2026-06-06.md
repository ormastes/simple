# Pure-Simple web layout: primitive flexbox limitations (two-column rows)

**Status:** OPEN (known limitation, low priority) — renderer is primitive by design.
**Severity:** Fidelity — multi-column flex pages don't match Chromium; single-column
and block/`width:%` content render correctly.
**Affected:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
(the `display:flex` row branch, ~line 2925).
**Path:** `bug` track.

## Symptom (observed rendering the VanillaStyle demo at 400×720)

Header, nav, blue accent border, and the full-width hero render correctly. The
`.main-layout { display:flex }` two-column section does not:

1. **Flex ratio ignored** — `flex:2` content-area takes ~all the row width and the
   `flex:1` sidebar collapses to a right-edge sliver. The row branch hands the
   first child the remaining width instead of distributing by `flex-grow`.
2. **Article text overlaps** — block children of a block element nested inside a
   flex item stack at nearly the same `y` (vertical advance not accumulating for
   that subtree), so the `<article>` heading/paragraphs render on top of each other.

## Not a regression

These predate this session's changes. The `<title>`-skip and percentage-width
fixes (committed 2026-06-05/06) are regression-free: the bun/node web-layout
bitmap parity gates still pass with `mismatch_count=0`:

- `check-bun-simple-web-layout-bitmap-evidence.shs` (JS_RENDER_RUNTIME=node) → pass
- `check-bun-simple-web-layout-child-scope-bitmap-evidence.shs` → pass
- `check-bun-simple-web-layout-commandbar-taskbar-card-bitmap-evidence.shs` → pass

## Why not fixed here

This file has a documented regression history: prior "closer to Chromium" rewrites
silently broke the `simple-web-layout-*` bitmap parity scenes and had to be
reverted (see memory + `project_web_node_layout_parity_revert`). A flexbox
distribution + nested-block-flow rewrite is exactly that class of change and must
be done against the full parity-gate matrix, not ad hoc. Tracked for a dedicated
pass: (a) distribute row width by `flex-grow`; (b) verify nested block-in-flex
vertical flow accumulates child heights.
