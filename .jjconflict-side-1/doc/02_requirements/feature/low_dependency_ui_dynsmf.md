# Low Dependency UI dynSMF Feature Requirements

Date: 2026-06-05

## Selection

Selected path: Feature Option C, expanded from the initial thin slice to cover
all requested default dynSMF libraries.

Default dynSMF libraries: `file_io`, `net_io`, `render2d`, `web_renderer`,
`gui_renderer`, and `tui_renderer`.

## Goal

Prove the low-dependency UI and dynSMF architecture end to end: protect base TUI
dependency closure, introduce explicit HTML/CSS capability loading boundaries,
and load the requested stdlib-like capabilities as session-owned precompiled
dynSMF libraries with autoload, opt-out, unload, stale-handle, and reload
behavior.

## Requirements

REQ-001: TUI dependency closure stays minimal

Base `app.ui.tui` must depend only on common UI/TUI renderer contracts and must
not import GUI, web, TUI-web, browser, HTML renderer, or CSS implementation
modules. The dependency gate must use exact-prefix module matching so
`app.ui.tui` does not match `app.ui.tui_web`.

REQ-002: Common renderer does not force HTML renderer implementation

Generic renderer/widget code must not force `app.ui.render.html_widgets` into
non-HTML lanes. HTML renderer access must be represented as an explicit
capability requested only by HTML-capable widgets or host web adapters.

REQ-003: HTML/CSS capability boundary is explicit

The selected slice must expose a clear capability boundary for HTML renderer and
CSS provider use. Non-HTML widgets must be able to prove they do not request or
load the HTML/CSS implementation closure.

REQ-004: dynSMF manifest contains requested stdlib-like precompiled ids

The dynSMF manifest model must include stable ids for `file_io`, `net_io`,
`render2d`, `web_renderer`, `gui_renderer`, and `tui_renderer`. Each entry must
declare precompiled SMF artifact metadata, a source module, ABI version, default
autoload policy, exported symbols, and a deterministic build plan that maps the
source to `build/dynsmf/<id>.smf`.

REQ-005: requested default libraries load through a session-owned dynSMF path

The `file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, and
`tui_renderer` libraries must load through a dynSMF session abstraction that
owns handles, records generation metadata, and emits inspectable evidence rows.

REQ-006: dynSMF default autoload is policy-controlled

The selected implementation must support default autoload for all enabled
manifest entries and must record load or skip evidence for every requested
default dynSMF id.

REQ-007: arg/env controls can disable dynSMF loading

The selected slice must support skip-all and per-id policy controls:
`--no-dynsmf`, `--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and
`SIMPLE_DYNSMF_DISABLE=<ids>`.

REQ-008: dynSMF unload/reload is testable in interpreter mode

Interpreter-mode tests must be able to load each requested default dynSMF
library, resolve a representative symbol, unload it from the session, observe a
deterministic stale/unloaded diagnostic, reload it, and observe fresh generation
metadata.

REQ-009: Evidence is deterministic

Dependency-gate and dynSMF-session evidence must be deterministic enough for
SPipe manuals and verification. Diagnostics must name the library id or module,
policy source, action, status, reason, handle, and generation where applicable.

REQ-010: All requested default dynSMF libraries are build- and startup-ready

The selected implementation must provide deterministic compile-to-SMF build
plans, generated artifact readiness validation, and checked startup autoload for
`file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, and
`tui_renderer`.

## Scope Exclusions

- Deeper process-callable native symbol execution for SMF payloads remains a
  lower-loader follow-up; this feature verifies the session-owned SMF dynlib
  facade, artifact readiness, policy, and unload/reload lifecycle.
- Startup/RSS performance budgets are not release-blocking in this slice.
- Release is out of scope until verification passes.
