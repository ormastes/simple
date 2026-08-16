# browser (Simple Browser) Feature Expert

## Role

Own feature-specific process knowledge for **Simple Browser** — the
`app.ui.render`-contract browser app (`src/app/browser/`). Use this skill
when work touches `src/app/browser/`, its wiring into
`src/app/wm_showcase/`, or its specs.

## Pipeline Links

Invoke as slash-commands (`/research`, `/design`, …); sources live in `.claude/skills/`:
[research](../../../../.claude/skills/research.md) ·
[design](../../../../.claude/skills/design.md) ·
[impl](../../../../.claude/skills/impl.md) ·
[verify](../../../../.claude/skills/verify.md) ·
[release](../../../../.claude/skills/release.md) ·
[spipe](../../../../.claude/skills/spipe.md) (spec-writing landmines)

## Feature Links

- [Source](../../../../src/app/browser/) — `main.spl` (CLI entrypoint,
  mirrors `src/app/terminal/main.spl`'s shape), `render_adapter.spl`
  (`render_browser`/`render_browser_html`/`render_browser_text`, the
  `app.ui.render.types.RenderConfig`/`RenderResult` contract ~20 sibling
  apps already use — terminal, ide tools, dashboard, office, ...)
- Consumer: [`src/app/wm_showcase/session.spl`](../../../../src/app/wm_showcase/session.spl)
  — the "Simple Browser" showcase window feeds `render_browser_html(...)
  .html_output` through the same
  `simple_web_render_html_to_readback_result_with_engine2d_backend` cascade
  + layout + paint path every other HTML-backed showcase window uses; the
  window opens `simple://home`, the real Hello World page
  (`browser_page_body_html`), not a placeholder/pixel shortcut.
- Glossary: [Simple Browser](../../../glossary.md#simple-browser)
- Sibling apps this mirrors: [terminal feature expert](../../feature_expert/)
  (if/when one exists) — see `src/app/terminal/render_adapter.spl` for the
  identical contract shape.

## Relationship to other "browser" things in this repo (do not confuse)

Three unrelated modules share the word "browser" — know which is which
before touching any of them:

1. **`src/app/browser/`** (this feature) — hosted, `app.ui.render`-contract
   app. Runs in-process, pure function in → HTML/text out. No event loop of
   its own.
2. **`src/os/apps/simple_browser/`** — baremetal/freestanding-only.
   `spl_start()` entry, VFS externs, boots as a QEMU kernel directly via
   `native-build --entry-closure --target x86_64-unknown-none`. Cannot run
   in a hosted session; do not try to reuse it for hosted work.
3. **`src/app/ui.browser/`** — a standalone winit-windowed GUI-widget-tree
   app with its own event loop and host window (`app.spl`/`main.spl`), not
   an `app.ui.render`-contract app. Predates this feature; not touched by it.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release
artifacts for this feature, update this skill with the new links and the
current handoff notes.

## Handoff Notes (2026-08-06)

- **Created this session**: `src/app/browser/render_adapter.spl` (new),
  `src/app/browser/main.spl` (new), wired into
  `src/app/wm_showcase/session.spl` (new `WmShowcaseWindowSpec` entries for
  `kind: "browser"` and `kind: "terminal"`; desktop height grown 360→430 to
  fit a second HTML-window row without overlap).
- **Recovered once already**: the first landing of these files was silently
  reverted by a shared-working-copy race (a known hazard class in this repo
  — see `[[reference-shared-wc-environment-traps-2026-07-30]]` in memory)
  before it could be committed. Recreated verbatim from the original
  authoring context; land promptly via plumbing CAS next time rather than
  leaving new files uncommitted in the shared tree for long.
- **Spec-tested since 2026-08-06** (supersedes the earlier "not yet
  spec-tested" note): `test/01_unit/app/browser/browser_render_adapter_spec.spl`
  (9 examples, pure dispatch/content logic — engine calls deliberately
  excluded, one alone blows the spec runner's 10M-op budget) and
  `test/02_integration/app/browser_cli_log_modes_spec.spl` (4 examples,
  process-spawns the real CLI). The wm_showcase pixel-parity gate remains
  separately tracked in
  `doc/08_tracking/bug/wm_showcase_session_capture_spec_no_examples_executed_2026-08-06.md`.
- Full HTML-window renders in this environment cost 30-50 CPU-minutes each
  (interpreted cascade+layout+paint) — the wm_showcase suite now has 4
  HTML-backed windows (gui, web, browser, terminal) instead of 2, so a full
  `wm_showcase` spec run costs roughly double what it did before this
  change. Budget accordingly; do not run it synchronously inline.
- **`--open` real-GUI window landed 2026-08-06** (`115e1b522b6` +
  `88df83a75e5` idle-poll fix + `bb106fcc335` fallback fix):
  `main.spl --open` opens a real winit window via `GuiRenderer`, presents
  one engine frame, blocks until close. End-to-end verified under
  Docker+Xvfb (window on screen with real glyph pixels in 59s); usage guide:
  `doc/07_guide/app/browser.md`.
- **Load-bearing structure — do not "clean up"**: `main.spl` renders the
  pixels and passes them into `run_browser_window_gui(url, w, h, pixels)`.
  Moving the render into `gui_window.spl` looks tidier but silently drops
  the entire engine into the tree-walk interpreter (~10-50x, no diagnostic;
  four 1800s-budget runs never finished before the hoist). Compiler defect:
  `doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.
- **2026-08-15 session lanes** (specs under `test/01_unit/browser_engine/`):
  - **Vulkan render lane**: `render_lane.spl` gained a `vulkan` lane
    (CPU paint → engine2d `VulkanBackend` present → `device_readback`,
    fail-closed provenance — never labels software pixels "vulkan");
    `browser_renderer.spl create_with_backend` routes `vulkan`/`webgpu`
    through `Engine2D.create_requested_backend` instead of silently
    degrading. Gate: `browser_vulkan_lane_spec.spl`. Docker lavapipe
    end-to-end: `scripts/check/check-simple-web-browser-docker-vulkan.shs`
    (needs a `simple-runtime/vulkan`-featured build at
    `build/browser-vulkan/simple`; `simple-compiler/vulkan` still blocked on
    an incompletely vendored rspirv — see
    `doc/08_tracking/bug/browser_has_no_vulkan_render_lane_2026-08-15.md`).
  - **Script execution + animation clock**: page `<script>` (JS and
    `text/simple`) executes pre-paint; `browser_engine_animated_frames`
    (render_adapter) drives rAF/CSS clocks per frame. The nogc JS subset
    parser now supports `function name() {}` DECLARATIONS (it previously
    dropped them AND the statement after the closing brace). Gates:
    `browser_script_execution_spec.spl`, `browser_animation_clock_spec.spl`.
  - **Sandbox**: research + gap list in
    `doc/01_research/app/browser/browser_sandbox_model_research_2026-08-15.md`;
    page-script node natives (`require("process")`/`os`, `process.exit/cwd`)
    are now capability-gated (default DENY in `JsRuntime.new_browser`).

## Handoff Notes (2026-08-15, renderer hardening session)

All lanes below verified green this session. Run pattern for specs:
`SIMPLE_TIMEOUT_SECONDS=600 bin/simple test --no-session-daemon <spec>`; add
`SIMPLE_COVERAGE=1` for recordable-coverage runs (quirk: coverage is only
recorded on that flag, and the collector has known decision-skips — see bug
records `coverage_collector_skips_pub_val_and_match_heads_2026-08-15.md` and
`coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md`).

- **Chrome counterpart provider**: `src/lib/nogc_sync_mut/spec/evidence/counterpart/chrome_dom_snapshot_provider.spl`
  — real Chrome over pure-Simple CDP at boundary `chrome.dom_snapshot@1`.
  Spec: `test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl`.
  Details in the [counterpart_conformance expert](../counterpart_conformance/skill.md).
- **Coverage closure**: ~40 `*_coverage_closure_spec.spl` files under
  `test/01_unit/browser_engine/` drive renderer modules (layout, style,
  paint, dom color, file renderers) to 100% recordable branch coverage.
  Counterpart-side closure record (link, don't duplicate):
  `doc/08_tracking/test/counterpart_branch_coverage_closure_2026-08-15.md`.
- **Vector-font differential lane**: `tools/vector_font_diff/`
  (`run_vector_font_diff.shs`, `chrome_vector_font_dump.js`,
  `simple_vector_font_dump.spl`, outputs in `out/`) + system spec
  `test/03_system/browser_engine/chrome_vector_font_differential_spec.spl`.
  See also [vector_fonts expert](../vector_fonts/skill.md).
- **Docker+Vulkan system lane**: `scripts/check/check-simple-web-browser-docker-vulkan.shs`
  (lavapipe in Docker) now gated by
  `test/03_system/browser_engine/docker_vulkan_browser_spec.spl`.
- **Interpreter fixes landed**: ClassInstance `simple` handling and nested
  field-index assignment — unblocked several of the coverage specs above
  (related record: `engine2d_landing_blocked_on_classinstance_seed_infra_2026-08-15.md`).
