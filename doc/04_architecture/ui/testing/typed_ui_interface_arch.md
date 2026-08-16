# Typed UI Interface + Office Architecture (v1, 2026-08-16)

Applies the research in
`doc/01_research/ui/testing/typed_ui_interface_office_research_2026-08-16.md`
(read its "Fact-check corrections" section — this doc uses the corrected
facts). Companion plan:
`doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md`.

## Decision

The UI ID graph is a **compiled, versioned application interface**:

```
UI source (.spl builders / .sui templates / typed ID patterns)
  → UiInterfaceManifest + lock + generated SSpec symbols + source maps
  → one semantic UI tree per app (TUI / GUI / Web / access / test derive from it)
  → compiled SSpec UiActionPlan (headless / TUI / GUI / Web / remote HTTP)
  → before/action/after evidence → generated Markdown manual
```

Reference vertical: **Calc** (only office app with a session host + HTTP
access path today). No other Office app migrates until Calc Typed UI Contract
v1 passes.

## Verified current state (authoritative)

| Area | Fact | Evidence |
|---|---|---|
| Builder IDs | explicit id first arg | `src/lib/common/ui/builder.spl:55,87,137` |
| Identity store | process-global flat `_widget_registry`; `upsert_widget_record` silently replaces same-id | `src/lib/common/ui/widget_store_ops.spl:20,54-78,204-206` |
| Session store | `WidgetStore` exists, flat, marginal adoption | `widget_store.spl`; `nogc_sync_mut/ui/session.spl:67,89,115,144` |
| Access node | `canonical_id/surface_id/widget_id/kind/focused`; `surface#widget` (`access_types.spl:80-83`), default `main` (`access_snapshot.spl:31-44`) | `src/lib/common/ui/access_types.spl:10-22` |
| SGTTI lookup | exact id then widget_id, **first match, no ambiguity error** | `src/lib/nogc_sync_mut/ui_test/sgtti.spl:250-256` |
| `.sui` | Rust-seed only; raw template string + regex web compiler; no AST; only 3 example `.sui` files in-tree, zero production use | `src/compiler_rust/parser/src/sui_parser.rs:86-88,264-320`; `src/compiler_rust/compiler/src/web_compiler.rs:269` |
| Snapshot names | `text_value = get_prop("text")` only; widgets use label/value/title/placeholder | `access_snapshot.spl:206` |
| Calc dual tree | `SheetsApp.build_ui()` + separate `access_controller` tree + hand JSON | `sheets_app.spl:48`; `access_controller.spl:129-134,190-282` |
| Theme | default is `fluid_light` with `liquid` alias (`config/themes/theme.sdn:1,18`); `aetheric_dark` only the no-registry fallback (`theme_package.spl:97`); GlassDark fallback in widget.spl:114; iOS helper in office | `src/app/office/theme.spl` |
| Evidence | typed evidence/action-trace/terminal-grid/manual renderer exist | `src/lib/common/spec/evidence/` |
| Office web | Calc-only HTTP access host, JSON snapshot polling; others offline html_render | `src/app/office/sheets/access_server.spl`, `calc_access_session_host.spl` |
| Web stack | `src/app/ui.web/` (server, ws, session token, origin guard, `host_adapter_contract.spl`), `ui.vscode/` (backend, protocol), `ui.tui_web/` | see dirs |
| HTTP substrate | hardened `http_core` shared with enterprise suite | `src/lib/common/net/http_core.spl` |
| Slides IDs | index-derived `el_{kind}_{len}` — unstable | `slides_app.spl:155` |

## Contracts (frozen — change requires ADR update)

### Identity
- `UiNodeKey{tree_instance, surface_id, qualified_id}` is store identity;
  `UiQualifiedId{scope: UiScopePath, local: UiLocalId}`.
- Scope = intentional component/domain boundary only (`toolbar.save`,
  `sheet.cell_A1`), never layout ancestry. Authoring: `ui_scope(name, [...])`;
  reusable components take a `UiScope`.
- Duplicate local ID in one scope: UI compile error UIE1002 (both locations).
  Ambiguous short ID in SSpec: UIE1004 (qualified candidates). Unknown ID:
  UIE1001 (did-you-mean + manifest path + declaration site). Never first-match.
- Wire compat: keep `surface#widget` encoding; add `scope_path` additively.
  Expand → migrate (WidgetNode/Store → UITree → layout → renderers → access →
  SGTTI/drivers → office apps) → contract (delete global store, silent upsert,
  first-match).

### Manifest
- `UiInterfaceManifest{schema_version, app_id, interface_version, source_hash,
  surfaces, nodes, aliases, patterns}`; node carries kind, actions, public,
  dynamic_pattern, source file/line/col.
- Lock file `config/ui-locks/<app>.ui.lock.sdn` (NOT under `build/` —
  `.gitignore:4 build/` would make the committed contract silently
  untrackable); add-public = compatible;
  rename/remove public, remove action, incompatible kind = breaking; `aliases:`
  with deprecated_since/remove_after for migration.
- Extraction: `.spl` pass keyed on resolved builder symbols via an SDN builder
  descriptor registry (id_argument, kind, actions); const-eval IDs are static;
  runtime-only IDs flagged unless private. `.sui`: DEFERRED — only 3 example
  files exist in-tree, zero production/Office use, and the parser lives in the
  bootstrap-only Rust seed; wave-1 extraction covers `.spl` builders only. A
  `.sui` template AST (Element/Text/Expression/If/For/ComponentEmbed with
  spans) becomes in-scope only if/when `.sui` gains a production consumer, and
  should then be built pure-Simple, not seed-side. Dynamic entities export
  typed patterns
  (`cell_{CellRef}` + codec); Slides/Draw move to stable document IDs.

### SSpec targets
`# @ui: <app-id>` / `# @ui-target: tui|gui|web|both`. Bare id = compiled
symbol; dotted = qualified; quoted = accessible-name fallback (runtime
strict); `id(expr)` = runtime escape; omitted = focused. Precedence: symbol →
qualified → pattern → runtime id → name fallback.

### ActionPlan + drivers
`UiActionPlan` / `UiActionStep{kind, target, value, preconditions, settle,
source}`. Execution law per live action: manifest hash check → pre snapshot →
resolve exactly-one → capability check → real input → settle → post snapshot →
read-after-write → record. `UiTestDriver` adapters: headless semantic, TUI
in-process, TUI PTY, GUI compositor/DrawIR, **Web (browser)**, **HTTP remote
access**, SimpleOS compositor. SGTTI stays the query substrate, not the
mutation owner. `both` = semantic parity (IDs, state, model results, focus
meaning), never pixel parity.

### Assertions
L0 manifest → L1 semantic snapshot → L2 terminal-grid/DrawIR geometry → L3
controlled pixels (masks, fixed env) → L4 deployed workflow. Cheapest
reliable oracle wins; SSIM/LPIPS diagnostics only.

### TUI evidence
Terminal-state machine → `TerminalFrame` of grapheme-cluster cells (UAX #29,
EAW-tailored width, SGR attrs, cursor, semantic_id regions). Annotation from
the access tree at evidence time. Matching: exact frame, semantic region,
subset, attribute-aware, cursor, focus treatment, layout relation, masked.

### Manuals
ActionPlan is sole source; manual is a projection (purpose, prerequisites,
visible setup incl. any CLI fixture, steps, before/action/after, expected,
troubleshooting, artifacts, provenance, run id). `show screen` lowers to a
capture checkpoint (`target/region/compare/theme` options). Evidence bundle
layout per scenario: compile/ trace/ tui/ gui/ model/ artifacts/ manual/
receipt/ (policy sets the minimum).

## Web host lane (NEW — run Office from a webpage, VS Code-style)

Requirement: Office apps (and eventually the IDE) must be launchable from a
browser against a **remote server**, like VS Code Web. This is a first-class
adapter, not an afterthought.

Design — enhance, don't invent:

1. **HostInterface v2** — extend `src/app/ui.web/host_adapter_contract.spl`
   into the shared host contract every app entry uses (pattern already proven
   by `ui_showcase/hosts/host_web.spl`): `attach(session)`, event in / frame
   out, capability negotiation (pointer, keyboard, IME, clipboard, file
   pickers), auth token, reconnect/resume.
2. **Transport** — replace Calc's ad-hoc snapshot-polling access server with
   `ui.web`'s websocket path (`ws_handler.spl` / `async_ws.spl`) carrying
   (a) the semantic access snapshot diff stream and (b) input events.
   Reality check: `ui.web` does NOT sit on `http_core` today — it carries its
   own server stack (`async_server.spl`, `tls_serve_loop.spl`), i.e. the
   second HTTP stack already exists. Agent N's first task is to migrate
   `ui.web`'s server onto `http_core` (limits/smuggling/path-safety/origin —
   same substrate as the enterprise suite) or, if migration cost is proven
   prohibitive, record an explicit two-stack decision with its security
   parity checklist. New code never adds a third stack.
3. **Remote server mode** — one server process hosts N app sessions
   (`office serve --listen <addr>`): session tokens
   (`session_token.spl`), origin guard, TLS via `tls_serve_loop.spl`,
   per-session `UISession`-owned WidgetStore (this is why identity must be
   session-scoped first — the global registry cannot host two remote users).
4. **VS Code-style shell** — `ui.vscode/backend.spl` + `protocol.spl` become
   the browser workbench backend: app launcher, document tabs, command
   palette, terminal panel (`ui.tui_web/screen_to_html.spl` for TUI-in-web).
5. **Testing** — the Web driver and the HTTP-remote driver run the SAME
   compiled ActionPlan; remote-mode adds gates: auth required, origin
   enforced, session isolation (two sessions never share widget identity),
   reconnect resumes revision-correlated state.

Enterprise co-work: the enterprise store app is today's only http_core-served
UI; the Office web lane and enterprise suite share http_core, session/auth,
and the file/DB backends. Enterprise verticals (store/booking/restaurant)
adopt the UI manifest + ActionPlan testing once Calc v1 proves it — their
web UIs become manifest-bearing apps like Office ones.

## Office layering (target)

`app.office.kernel` (DocumentSession, Command/QueryBus, Selection, UndoRedo,
Clipboard, SearchReplace, Autosave, Recovery, RecentFiles, FileLock,
Diagnostics) / `model.{writer,calc,slides,draw,base,math}` / `service` /
`format` (OfficePackage, ODF 1.4 first, part-based OOXML, lossless unknown
parts) / `ui` (views + manifests) / `adapter` (CLI, TUI, GUI, **Web**,
SimpleOS) / `extension`. MDSOC+; one typed command path for every surface;
no compat claims without corpus round-trip evidence.

## Theme

Default is already `fluid_light` with a `liquid` alias
(`config/themes/theme.sdn`); the Liquid plan therefore (1) introduces one
`ThemeService` authority, (2) evolves the fluid family into
`simple_liquid_light/dark` with compat aliases, (3) deletes the widget.spl
GlassDark fallback (edit executed by Agent B, the file owner), the office iOS
helper, and app-local hardcoded snapshots. Glass =
chrome only (toolbar/sidebar/dialogs); content surfaces opaque. TUI role
mappings never color-only. Tests: functional (theme-free), theme contract
(tokens/contrast/reduced transparency+motion/focus), small visual set.

## Acceptance gates

Compile: UIE1001/1002/1004, wrong action/kind, pattern validation, lock
compat. Runtime: manifest hash, cardinality one, capability,
read-after-write, revision correlation, real input, cleanup; web-remote adds
auth/origin/session-isolation/reconnect. Rendering: TUI frame correctness,
GUI semantic+hit+DrawIR, both=semantic parity, theme gates. Office:
save/reopen, recovery, undo consistency, round-trip loss reports, one
command contract, no test-only code in production closure. Manual: complete,
deterministic, stale-evidence-rejecting.

## First milestone — Calc Typed UI Contract v1

1. scoped identity storage (no silent overwrite; strict ambiguity)
2. Calc manifest (formula_input, confirm_edit, sheet_grid, `cell_{CellRef}`)
3. generated SSpec symbols + 4 compile-failure fixtures
4. ONE Calc semantic view (delete access_controller's parallel tree + hand JSON)
5. unified live flow: 6, 8, `=A1*A2` → 48 on TUI and GUI (keep 20×30 grid +
   deployment/perf evidence)
6. generated manual (annotated frame, screenshot+overlay, IDs, state, provenance)
7. **web-host preview**: same ActionPlan over the ws transport against a
   remote `office serve` Calc session; the polling access server retirement
   (`access_server.spl`, `calc_access_session_host.spl`) is executed by
   Agent H as file owner, with Agent N's transport as the consumer contract
8. Liquid integration deferred to the theme lane; Calc v1 must not block on it
