# Typed UI Interface — Developer Guide

Practical companion to
`doc/04_architecture/ui/testing/typed_ui_interface_arch.md` (contracts) and
`doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md` (phases/ownership).
Core idea: the UI ID graph is a **compiled, versioned application interface** —
IDs are extracted into a `UiInterfaceManifest`, SSpec targets compile against
it, and one compiled `UiActionPlan` runs on every driver.

## 1. Authoring UI IDs

### Today (legacy)
- Builders take an explicit id as first arg (`src/lib/common/ui/builder.spl`).
- Identity lives in a process-global flat `_widget_registry`;
  `upsert_widget_record` silently replaces a same-id widget.
- SGTTI lookup is exact id, then widget_id, **first match — no ambiguity
  error**. Wire encoding is `surface#widget`, default surface `main`.
- Slides uses index-derived `el_{kind}_{len}` IDs — unstable.

### Under the contract
- Store identity is `UiNodeKey{tree_instance, surface_id, qualified_id}` with
  `UiQualifiedId{scope: UiScopePath, local: UiLocalId}`.
- **Scope = intentional component/domain boundary only** (`toolbar.save`,
  `sheet.cell_A1`) — never layout ancestry. Author scopes with
  `ui_scope(name, [...])`; reusable components take a `UiScope` parameter.
- Duplicate local ID in one scope is a compile error (UIE1002). Silent
  overwrite and first-match lookup are deleted in the contract phase.
- **Public vs private:** manifest nodes carry a `public` flag. Adding a public
  node is lock-compatible; renaming/removing a public node, removing an
  action, or an incompatible kind change is breaking (use `aliases:` with
  `deprecated_since`/`remove_after` to migrate). IDs that are runtime-only
  (not const-evaluable) are flagged by extraction unless declared private.
- **Dynamic entities** export typed patterns with a codec, e.g.
  `cell_{CellRef}` for the Calc grid — never open-ended string IDs.
  Slides/Draw move to stable document IDs.
- Wire compat: `surface#widget` is kept; `scope_path` is added additively.
  Migration order: expand → migrate → contract (delete global store, silent
  upsert, first-match).

## 2. Writing a manifest-checked SSpec

Declare the app and target surface at the top of the spec:

```
# @ui: office.calc
# @ui-target: both        # tui|gui|web|both
```

Target forms, in resolution precedence (symbol → qualified → pattern →
runtime id → name fallback):

| Form | Meaning |
|---|---|
| `formula_input` | bare id — compiled symbol from the manifest (UIE1001 if unknown) |
| `sheet.cell_A1` | dotted — qualified id (scope path + local) |
| `cell_{CellRef}` instance e.g. `sheet.cell_B2` | typed dynamic pattern, validated by the codec |
| `id(expr)` | runtime escape hatch |
| `"Formula"` | quoted — accessible-name fallback, runtime strict |
| (omitted) | acts on the focused node |

Calc reference scenario (the v1 milestone flow: 6, 8, `=A1*A2` → 48):

```
# @ui: office.calc
# @ui-target: both

it "multiplies two cells" of:
    step("Type 6 into A1")
    click sheet.cell_A1
    type "6"
    press confirm_edit

    step("Type 8 into A2")
    click sheet.cell_A2
    type "8"
    press confirm_edit

    step("Enter the formula")
    click sheet.cell_A3
    fill formula_input, "=A1*A2"
    press confirm_edit

    expect(sheet.cell_A3.text).to_equal("48")
    show screen              # capture checkpoint (target/region/compare/theme options)
```

`show screen` lowers to a capture checkpoint in the ActionPlan; it is what
feeds the generated manual's before/action/after imagery. `both` means
**semantic parity** (IDs, state, model results, focus meaning) — never pixel
parity.

## 3. Diagnostics you will hit

| Code | Trigger | Fix |
|---|---|---|
| **UIE1001** | Unknown ID — target not in the manifest. Message gives did-you-mean, manifest path, and the declaration site. | Use the suggested symbol; or add/publicize the node in the UI source and rebuild the manifest; or use `id(expr)`/quoted name if genuinely runtime-only. |
| **UIE1002** | Duplicate local ID in one scope (both locations reported). | Rename one, or split into distinct `ui_scope`s — scopes exist exactly for this. |
| **UIE1004** | Ambiguous short ID in SSpec — bare id matches multiple qualified candidates (all listed). | Switch to the dotted qualified form from the candidate list, e.g. `toolbar.save` vs `dialog.save`. |

Also at compile time: wrong action/kind for a node, dynamic-pattern
validation, and lock-compat failures. There is never a first-match fallback.

## 4. Driver matrix

One compiled `UiActionPlan` runs on every driver. Per live action, the
execution law is: manifest hash check → pre snapshot → resolve exactly-one →
capability check → real input → settle → post snapshot → read-after-write →
record. SGTTI stays the query substrate, not the mutation owner.

| Driver | What it exercises | When it runs |
|---|---|---|
| Headless semantic | manifest + semantic tree, no rendering | default fast lane; every spec, CI |
| TUI in-process | terminal-state machine → `TerminalFrame` | `@ui-target: tui` / `both` |
| TUI PTY | real input through a PTY | TUI deployment evidence |
| GUI compositor/DrawIR | hit-testing, geometry, screenshots | `@ui-target: gui` / `both` |
| Web (browser) | browser adapter over the same plan | `@ui-target: web` |
| HTTP remote access | same plan over the ws transport against `office serve` | web-remote gates: auth required, origin enforced, session isolation, reconnect resumes revision-correlated state |
| SimpleOS compositor | on-OS surface | SimpleOS lanes |

Assertion levels — cheapest reliable oracle wins: L0 manifest → L1 semantic
snapshot → L2 terminal-grid/DrawIR geometry → L3 controlled pixels (masks,
fixed env) → L4 deployed workflow. SSIM/LPIPS are diagnostics only.

## 5. Evidence bundle and generated manuals

Per scenario the bundle layout is:

```
<scenario>/
  compile/     # manifest hash, generated symbols, lock check
  trace/       # action trace (pre/post snapshots, settle, read-after-write)
  tui/         # TerminalFrame captures (grapheme-cluster cells, SGR, cursor, semantic_id regions)
  gui/         # screenshots + overlays, DrawIR
  model/       # model-level results
  artifacts/   # files the scenario produced
  manual/      # generated Markdown manual
  receipt/     # run id + provenance (policy sets the minimum)
```

The **ActionPlan is the sole source** of the manual; the manual is a
projection: purpose, prerequisites, visible setup (incl. any CLI fixture),
steps, before/action/after, expected, troubleshooting (from failure codes),
artifacts, provenance, run id. TUI frames are annotated from the access tree
at evidence time. Manual gates: complete, deterministic,
stale-evidence-rejecting.

## 6. Web host lane — opting into `office serve`

Apps become remotely hostable (VS Code Web-style) via **HostInterface v2**,
the shared host contract extended from
`src/app/ui.web/host_adapter_contract.spl` (pattern proven by
`ui_showcase/hosts/host_web.spl`). An app entry implements:

- `attach(session)` — bind to a per-session `UISession`-owned WidgetStore
  (this is why identity must be session-scoped: the global registry cannot
  host two remote users);
- event in / frame out;
- capability negotiation (pointer, keyboard, IME, clipboard, file pickers);
- auth token, reconnect/resume.

Transport: `ui.web`'s websocket path (`ws_handler.spl` / `async_ws.spl`)
carries (a) the semantic access snapshot diff stream and (b) input events, on
top of `http_core` (`src/lib/common/net/http_core.spl`). Note: `ui.web`
carries its own server stack today (`async_server.spl`, `tls_serve_loop.spl`)
and does not yet use `http_core` — the web-host lane's first task is that
migration (or an explicitly recorded two-stack decision). This transport
replaces Calc's ad-hoc snapshot-polling access server.

Server mode: `office serve --listen <addr>` hosts N app sessions — session
tokens (`session_token.spl`), origin guard, TLS via `tls_serve_loop.spl`.
The browser workbench shell is `ui.vscode/backend.spl` + `protocol.spl`
(app launcher, document tabs, command palette, terminal panel via
`ui.tui_web/screen_to_html.spl` for TUI-in-web).

Testing: the Web driver and the HTTP-remote driver run the SAME compiled
ActionPlan; remote mode adds the auth/origin/session-isolation/reconnect
gates. Calc is the reference vertical — no other Office app (or enterprise
web UI) migrates until Calc Typed UI Contract v1 passes, including the
web-host preview over the ws transport.
