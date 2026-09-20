# blink specs reference modules deleted from src/lib/blink

Date: 2026-09-16

## Observed
Eight specs under `test/01_unit/lib/blink/` fail to resolve modules that no
longer exist anywhere in the tree (also absent on `origin/main`):

- `document_spec.spl` — `std.blink.dom.document` (src/lib/blink/dom/document.spl deleted)
- `flex_spec.spl` — `std.blink.layout.flex` (layout/flex.spl deleted)
- `inline_flow_spec.spl` — `std.blink.layout` (layout/inline_flow.spl deleted)
- `navigation_controller_spec.spl` — `std.blink.navigation.controller` (navigation/ deleted)
- `navigation_fetch_spec.spl` — `std.blink.network.fetch` (network/ deleted)
- `paint_controller_spec.spl` — `std.blink.feature.paint.paint_controller` (feature/ deleted)
- `scroll_manager_spec.spl` — `std.blink.scroll.manager` (scroll/ deleted)
- `paint/style_paint_spec.spl` — `std.common.ui.render_opt.paint_chunk_draw_ir_lowerer`

The files were removed by commit `2cca0bc59c4` ("Track production readiness
convergence", a broad multi-lane sync; its message does not mention any blink
slimming). No replacement symbols (`Document`, flex layout, `NavigationController`,
`ScrollManager`, `PaintController`) exist under `src/lib/` — only an unrelated
async `FetchResponse` in `src/lib/gc_async_mut/gpu/browser_engine/net/entity/request_types.spl`.

## Impact
The specs cannot execute at all (outcome=ERROR, executed=0..N). Blink coverage
for document model, flex layout, navigation, scroll, and paint-controller is
untested; if the deletion was an accidental stale-snapshot clobber (see
anti-revert protocol in `.claude/rules/vcs.md`), the functionality itself is
also gone.

## Expectation
Either the deleted modules are restored (if the deletion was unintentional) or
the specs are formally retired alongside a recorded decision to drop the
functionality — specs and implementation must not drift apart silently.

## Unblock condition
Owner decision: restore `src/lib/blink/{dom/document.spl, layout/flex.spl,
layout/inline_flow.spl, navigation/, network/, scroll/, feature/paint/}` and
`src/lib/common/ui/render_opt/paint_chunk_draw_ir_lowerer.spl` from
`2cca0bc59c4~1`, or delete the orphaned specs in the same change.
