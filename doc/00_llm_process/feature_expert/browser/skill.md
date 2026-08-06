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
- **Not yet independently spec-tested** as a standalone app (no
  `test/01_unit/app/browser/` yet — the terminal app itself has none either;
  verification so far is a standalone `bin/simple run` probe confirming
  `render_browser_html`/`render_terminal_html` produce real, correctly-shaped
  HTML output, plus the wm_showcase integration spec, which is a real
  full-render pixel-parity gate — currently blocked by an UNRELATED,
  independently-confirmed pre-existing defect, see
  `doc/08_tracking/bug/wm_showcase_session_capture_spec_no_examples_executed_2026-08-06.md`).
  Follow-up: add a `render_adapter_spec.spl` mirroring whatever pattern (if
  any) covers `terminal/render_adapter.spl`.
- Full HTML-window renders in this environment cost 30-50 CPU-minutes each
  (interpreted cascade+layout+paint) — the wm_showcase suite now has 4
  HTML-backed windows (gui, web, browser, terminal) instead of 2, so a full
  `wm_showcase` spec run costs roughly double what it did before this
  change. Budget accordingly; do not run it synchronously inline.
