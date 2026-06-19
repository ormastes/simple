# HTML/CSS Spec Traceability

## Sources

- HTML inventory: WHATWG HTML Living Standard, `indices.html#elements-3`,
  fetched 2026-06-17; conforming element count: 105.
- CSS inventory: W3C CSS current work index, fetched 2026-06-17; property-like
  CSS entry count used for this audit: 394.

## HTML Tag Coverage

Executable SSpec coverage is split by HTML tag family under
`test/01_unit/lib/common/web/browser_session_html_*_tags_spec.spl`.

The focused audit found one missing WHATWG element, `selectedcontent`; it is now
covered by:

- `test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl`

## CSS Property Coverage

CSS has two coverage levels:

- Functional renderer coverage for the Simple Web implemented subset:
  `align-*`, `background`, `background-color`, `border`, side border
  widths/colors, `box-sizing`, `color`, `display`, `flex`, `flex-*`,
  `flex-basis`, `gap`, `row-gap`, `column-gap`, `font-size`, `font-weight`,
  `height`, `justify-content`, `line-height`, `margin`, side margins, `max-*`,
  `min-*`, `opacity`, `order`, `overflow`, `overflow-x`, `overflow-y`,
  `padding`, side padding, `position`, `left`, `top`, `right`, `bottom`,
  `text-align`, `visibility`, `white-space`, `width`, and `z-index`.
- Traceability inventory coverage for the wider W3C CSS index. Unsupported CSS
  properties are tracked as inventory entries, not claimed as implemented
  rendering behavior. The SSpec owner for those inventory-only entries is
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl`.
  This is a universal assignment: every current W3C CSS property not listed in
  the implemented Simple Web subset maps to that inventory SSpec until a
  property gets functional renderer coverage.

Functional CSS coverage is owned by:

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_css_rule_bounds_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/display_contents_layout_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl`

## Generated GUI HTML/CSS Combinations

Common generated GUI combinations are covered in
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl`:

- semantic app shell: `main`, `header`, `button`, `span`, `section` with flex,
  padding, border, background, color, and text styles;
- form shell: `form`, `fieldset`, `legend`, `label`, `input`, `select`,
  `option`, `progress` with grouped selectors and box styles;
- media shell: `canvas`, `picture`, `source`, `img`, `video`, `object`, `div`
  with overflow, inline/block display, borders, and fallback text.

## Machine Check

Run:

```sh
sh scripts/check/check-html-css-sspec-traceability.shs
```

The checker fetches the current WHATWG HTML element index and W3C CSS index,
then verifies:

- all 105 HTML elements have focused SSpec assignment;
- all implemented Simple Web CSS properties have functional renderer SSpec
  assignment;
- W3C CSS properties outside the implemented subset have inventory SSpec
  assignment through
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl`.

## Restart Checklist

Use this section when restarting the goal from this plan doc.

Goal status command:

```sh
sh scripts/check/check-html-css-renderdoc-goal-status.shs
```

The status command aggregates the completed traceability evidence, Simple
RenderDoc `.rdc` evidence, macOS portability probe, and external-host capture
gate. It exits nonzero until original RenderDoc+Chrome HTML/CSS evidence passes
with `RDOC` magic.

GUI/rendering feature coverage status command:

```sh
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

This lightweight audit does not launch Electron, Chrome, or RenderDoc. It
checks that every `WidgetKind` has `app.ui.render.html_widgets` dispatch and
renderer fixture/spec coverage, runs the typed HTML/CSS SSpec traceability
gate, summarizes the Electron Simple Web layout manifest cases, points at the
production GUI/web parity wrapper, and embeds the current HTML/CSS RenderDoc
goal status. It may report `incomplete` while coverage is structurally mapped
but durable `.rdc` evidence is missing from the local `build/` tree or the
external Chrome/Vulkan gate has not passed.

HTML/CSS SSpec inventory traceability command:

```sh
sh scripts/check/check-html-css-sspec-traceability.shs
```

This non-rendering gate now emits
`build/html_css_sspec_traceability/evidence.env` by default. It proves the
current 105 WHATWG HTML elements and at least 390 W3C CSS property-like entries
are assigned to the SSpec corpus before the rendered fixture manifest and
RenderDoc gates can pass.

GUI widget renderer fixture/spec coverage command:

```sh
sh scripts/check/check-gui-widget-rendering-fixture-coverage.shs
```

This fail-closed gate derives the current 43 GUI widget wire kinds from
`src/lib/common/ui/widget_kind.spl`, checks `render_html_widget` dispatch and
renderer class markers in `src/app/ui.render/html_widgets.spl`, and verifies
that the renderer spec corpus covers all 43 widget markers. It specifically
guards newer direct widget classes such as `radio`, `heading`,
`navigation_bar`, `tab_bar`, `card`, `switch`, `segmented_control`, and
`search_bar`.

HTML/CSS rendering manifest traceability command:

```sh
sh scripts/check/check-html-css-rendering-manifest-traceability.shs
```

This lightweight gate parses the 50-case Electron/Simple layout capture
manifest and the actual fixture HTML emitted by
`scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs`. It proves
that all 105 WHATWG HTML elements and all 62 implemented Simple Web CSS
properties are covered by rendered fixture HTML, not only by text-only SSpec
assignment.

Already completed:

- Typed HTML inventory traceability exists for the current WHATWG element set
  used by this audit, including `selectedcontent`.
- Typed CSS traceability exists for the implemented Simple Web subset and for
  unsupported W3C CSS properties through the inventory SSpec.
- Common generated GUI HTML/CSS combinations have executable SSpec coverage.
- Simple in-application Vulkan/RenderDoc evidence has passed locally with a
  valid `.rdc` magic header.
- RenderDoc helper infrastructure exists through
  `scripts/tool/renderdoc-evidence.shs`,
  `scripts/lib/renderdoc-evidence-common.shs`,
  `test/helpers/renderdoc_capture_helper.shs`, and the setup/check wrappers.
- The macOS portability restart path was run on 2026-06-18 and recorded in
  `doc/09_report/html_css_macos_moltenvk_portability_probe_2026-06-18.md`.
  That report is supplemental evidence for this macOS host: Metal is present,
  Homebrew `vulkan-tools` verifies Apple M4 through MoltenVK, and
  `renderdoccmd` is unavailable, so no macOS `.rdc` capture was produced.
- The GUI/rendering feature coverage audit maps all current
  `src/lib/common/ui/widget_kind.spl` widget wires to HTML renderer dispatch and
  records the current 27-case Electron Simple Web layout manifest as the
  canonical pixel-parity fixture list.
- 2026-06-19 refresh: the Electron Simple Web layout manifest passes with 24
  exact cases, 2 tracked text-raster divergences, 1 tracked Chrome opacity
  compositor-rounding case, and 0 hard failures. The status gate still remains
  incomplete until local Simple RenderDoc and original Chrome/Vulkan RenderDoc
  `.rdc` evidence exist.
- 2026-06-19 follow-up: the rendering manifest traceability gate passes with
  105/105 HTML elements, 62/62 implemented CSS properties, and all 50 manifest
  scenes mapped to fixture HTML. The `border_side_matrix` and
  `flex_grow_shrink_wrap_matrix` exact bitmap scenes were re-run after adding
  missing longhand border and `flex` shorthand coverage; both remained exact
  with zero mismatches.

Do not repeat these completed checks unless a related file changed:

- `sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
- `scripts/tool/renderdoc-evidence.shs capture-simple`
- local host/Docker/QEMU attempts to run Chrome under RenderDoc with the same
  Chrome, RenderDoc, GPU, and VM capability state documented in
  `doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md`.

Completed restart-path goal:

- The plan's alternative restart path to add a macOS/MoltenVK portability
  report is complete for the current macOS host:
  `doc/09_report/html_css_macos_moltenvk_portability_probe_2026-06-18.md`.

Remaining original gate:

- Produce original Chrome HTML/CSS RenderDoc evidence on a host where
  Chrome-on-Vulkan can be captured without the documented GPU-process crash.
  The external-host completion gate below remains the required proof for that
  original Linux/Chrome/Vulkan `.rdc` evidence.

Valid restart paths:

- External Linux host or CI: run `scripts/setup/setup-renderdoc-env.shs
  --check`, register the Vulkan layer, run
  `scripts/tool/renderdoc-evidence.shs capture-html`, then validate the
  resulting `evidence.env` with
  `scripts/check/check-renderdoc-html-external-host-gate.shs`.
  Canonical single-command wrapper:
  `RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs`.
- macOS portability probe: run the macOS checks below and write a new
  `doc/09_report/` entry. Treat the result as supplemental unless it satisfies
  the same original RenderDoc+Chrome `.rdc` gate.
  Canonical wrapper:
  `sh scripts/check/check-renderdoc-macos-portability-probe.shs`.
- Privileged local GPU passthrough: only after operator approval to bind an
  isolated GPU group to `vfio-pci`; then run a desktop guest with real GPU
  Vulkan, Chrome, and RenderDoc.

## Vulkan/RenderDoc Follow-Up

Linux software-renderer SSpec coverage does not prove Vulkan IO-level behavior.
The remaining evidence must run Chrome with Vulkan enabled and capture the
generated GUI HTML/CSS render path with RenderDoc CLI. The capture must show
the Vulkan draw/readback path, not only DOM/style assertions or CPU pixels.

Canonical infrastructure for the follow-up:

- `scripts/tool/renderdoc-evidence.shs capture-simple`: Simple in-application
  `rt_renderdoc_*` Vulkan Engine2D capture.
- `scripts/tool/renderdoc-evidence.shs capture-html`: original
  RenderDoc+Chrome HTML/CSS fixture capture.
- `test/helpers/renderdoc_capture_helper.shs`: test-facing facade with the same
  interface.
- `scripts/setup/setup-renderdoc-env.shs`: shared path discovery and Vulkan
  layer registration.

Do not add new ad hoc `renderdoccmd`/Chrome command variants to specs. Extend
the shared helper interface first, then rerun the canonical command.

Current canonical local evidence:

- `RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-simple`
  passed and produced `build/renderdoc/canonical-probe/simple/simple_gui_capture.rdc`
  with `rdoc_capture_magic=RDOC`.
- `RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe scripts/tool/renderdoc-evidence.shs capture-html`
  failed with `rdoc_capture_reason=missing-rdc`; the Chrome GPU process
  segfaulted through RenderDoc before emitting a capture.

External-host completion gate:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 \
  sh scripts/check/check-renderdoc-external-host-capture.shs
```

The wrapper runs setup, `capture-html`, and the gate in order. For readiness or
dry-run checks, omit `RDOC_EXTERNAL_RUN_CAPTURE=1`; it records typed
`capture-not-requested` evidence without launching Chrome.

Low-level gate:

```sh
RDOC_HTML_EVIDENCE_ENV=<path-to-original-chrome-renderdoc-evidence.env> \
  sh scripts/check/check-renderdoc-html-external-host-gate.shs
```

The gate passes only for original RenderDoc+Chrome evidence with
`rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`, and a real `.rdc` file.

## macOS Portability Probe

macOS is a separate portability investigation lane, not a replacement for the
Linux original Chrome/Vulkan RenderDoc gate. Apple platforms do not provide a
native Vulkan driver stack; Vulkan runs through a portability layer such as
MoltenVK, which maps Vulkan calls to Metal. That makes macOS useful for checking
whether the Simple Vulkan path can run through MoltenVK, but it does not prove
native Linux/NVIDIA Vulkan IO-level behavior.

Planned macOS checks:

- Run `sh scripts/check/check-renderdoc-macos-portability-probe.shs` to record
  host, GPU, Vulkan, RenderDoc, and evidence status into
  `build/renderdoc/macos-portability-probe/evidence.env` and
  `doc/09_report/renderdoc_macos_portability_probe_<date>.md`.
- Install the current LunarG Vulkan SDK for macOS and verify `vulkaninfo`
  reports a MoltenVK or other Metal-backed Vulkan portability device.
- Run `scripts/setup/setup-renderdoc-env.shs --check` on macOS if an official
  or locally built RenderDoc command line is available; record unavailable
  status when RenderDoc cannot capture/replay on macOS.
- Run `scripts/tool/renderdoc-evidence.shs capture-simple` only if the Simple
  Vulkan capture program and RenderDoc CLI are both available on macOS.
- Run `scripts/tool/renderdoc-evidence.shs capture-html` only as an exploratory
  check. Chrome on macOS commonly routes through Metal/ANGLE rather than the
  same Linux Vulkan path, so a macOS browser capture is portability evidence,
  not completion evidence for the original gate.
- Use Xcode GPU Frame Capture for Metal-level inspection when the observed path
  is Metal/MoltenVK and RenderDoc cannot provide useful capture evidence.
- Set `RDOC_MACOS_RUN_CAPTURES=1` only on a macOS host that already has
  Vulkan/MoltenVK and RenderDoc CLI available. The wrapper will then call the
  shared `capture-simple` and exploratory `capture-html` paths and run the
  external-host gate against any HTML evidence file.

Any macOS result must write a report under `doc/09_report/` with:

- macOS version, CPU architecture, GPU model, and Vulkan SDK/MoltenVK version;
- whether RenderDoc CLI was present and whether it produced an `.rdc`;
- whether the browser path was Vulkan-over-Metal, direct Metal, or unavailable;
- the exact evidence file or concrete blocker.
