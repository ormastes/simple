# WM Glass Theme Web/GUI Audit — 2026-07-26

> Superseded for current status by
> `doc/09_report/aetheric_host_web_gui_readiness_2026-07-26.md`. This document
> preserves the historical `3b7a11b6cd` audit. Canonical event admission now
> requires a retained Aetheric production proof; no live proof exists.

- Source revision: `3b7a11b6cdf61ce2180886d6ae17fa0e1d9c8204` (`origin/main` at audit start).
- Scope: AC-1, AC-4, AC-5, and AC-7 of `.spipe/wm-glass-theme-host-simpleos/state.md`.
- Status: **BLOCKED before a production browser/host capture; no production PASS is claimed.**

## Confirmed owner behavior

`aetheric_dark` remains the authoritative generated `ThemeRenderSnapshot`.
Hosted startup installs the durable/generated snapshot before compositor creation;
SimpleOS installs the same generated snapshot before framebuffer/compositor
construction. `widget_tree_to_draw_ir_with_theme` projects its material roles
into the existing Draw IR owner.

The Web CSS owner (`src/app/ui.web/html_css.spl`) resolves package CSS and its
fingerprint as scalar values inside `nogc_sync_mut.ui.theme_package`, and only
uses an installed snapshot CSS document when its source fingerprint exactly
matches the resolved package fingerprint. The package document is appended last,
so its selector/cascade overrides remain authoritative. This audit found no
remaining parser/cascade or semantic-owner correction to make in that route.

## Focused diagnostic evidence

The only eligible pure-Simple executable available on this macOS host was
`/Users/ormastes/simple/bin/release/macos-arm64/simple`, SHA-256
`277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`.
These are source/interpreter regressions, not native production evidence:

- `test/01_unit/app/ui/web_theme_css_authority_spec.spl`: PASS, 5 assertions.
- `test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl`: PASS, 2 assertions.
- `test/01_unit/os/wm_theme_bootstrap_contract_spec.spl`: PASS, 6 assertions.

Captured logs are retained under
`build/wm-web-theme-live-20260726/` in this linked worktree.

## AC-7 first unavailable production rung

`tools/web-render-backend/wm_event_check.js` does launch Electron and invokes
the repository `wm.js`, but its `makeHtml` function constructs standalone fixed
light CSS (`#f8fafc`, `rgb(229, 231, 235)`, and fixed traffic-light colors).
It neither uses `generate_wm_html_page` / the Web semantic owner nor binds an
`aetheric_dark` fingerprint. Its validator likewise requires those fixture
values and records no computed backdrop filter, alpha, radius, border, or
shadow. Consequently this receipt is only an event-bridge diagnostic; it is
not evidence that the production Aetheric document was rendered or interacted
with.

Do not launch the canonical host wrapper to compensate: its native host cycles
are already exhausted in the active state. The next valid attempt needs a
current-source production HTML envelope plus its exact resolved fingerprint,
computed glass witnesses, canonical submitted DrawIrComposition receipt,
device readback/checksum, and the existing focus/pointer/move/maximize/
keyboard/text/performance/animation post-state checks with
`blur_or_tolerance=false`.
