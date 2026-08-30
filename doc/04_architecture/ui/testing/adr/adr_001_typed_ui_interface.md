# ADR-001: Typed UI Interface (frozen normative subset)

- Status: ACCEPTED (phase 0 freeze, 2026-08-16)
- Owner: Agent A (architecture). Changes to any FROZEN section below require
  updating this ADR plus foundation-owner (Agent B/C/D) approval.
- Source: `doc/04_architecture/ui/testing/typed_ui_interface_arch.md` (full
  rationale), `doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md`.

## Context

Today's UI identity is a process-global flat `_widget_registry` whose
`upsert_widget_record` silently replaces a same-id record
(`src/lib/common/ui/widget_store_ops.spl:20,54-78,204-206`), and SGTTI lookup
is first-match with no ambiguity error
(`src/lib/nogc_sync_mut/ui_test/sgtti.spl:250-256`). Calc keeps a second,
hand-maintained semantic tree (`src/app/office/sheets/access_controller.spl`).
This ADR freezes the contracts every downstream agent (B..N, H) builds against.

## Decision 1 — Identity (FROZEN)

- Store identity is `UiNodeKey { tree_instance, surface_id, qualified_id }`.
- `UiQualifiedId { scope: UiScopePath, local: UiLocalId }`.
- Scope is an intentional component/domain boundary only (`toolbar.save`,
  `sheet.cell_A1`) — NEVER layout ancestry. Authoring API: `ui_scope(name,
  [...])`; reusable components take a `UiScope` parameter.
- Identity is session-scoped (per-`UISession` WidgetStore). The process-global
  registry and silent same-id upsert are deleted in the contract phase
  (phase 10); until then a compat facade keeps apps running.

## Decision 2 — Duplicate/lookup diagnostics (FROZEN)

| Code | Condition | Required report content |
|---|---|---|
| UIE1001 | Unknown ID at compile or resolve time | did-you-mean candidates + manifest path + declaration site |
| UIE1002 | Duplicate local ID within one scope | UI compile error citing BOTH declaration locations |
| UIE1004 | Ambiguous short ID in an SSpec target | list of fully-qualified candidates |

First-match resolution is prohibited everywhere. Silent duplicate overwrite is
prohibited everywhere. A resolver must prove cardinality exactly-one or fail.

## Decision 3 — Manifest + lock schema (FROZEN)

- `UiInterfaceManifest { schema_version, app_id, interface_version,
  source_hash, surfaces, nodes, aliases, patterns }`.
- Node record carries: `kind`, `actions`, `public`, `dynamic_pattern`, and
  source `file/line/col`.
- Lock files live at `config/ui-locks/<app>.ui.lock.sdn`. NEVER under `build/`
  (`.gitignore` swallows any `build/` path component; the committed contract
  would silently become untrackable).
- Compatibility policy:
  - compatible: adding a public node, adding an action, adding an alias.
  - breaking: rename/remove a public node, remove an action, incompatible
    kind change.
  - migration: `aliases:` entries with `deprecated_since` / `remove_after`.
- Extraction (wave 1): `.spl` builders only, keyed on resolved builder symbols
  via an SDN builder-descriptor registry (`id_argument`, `kind`, `actions`).
  Const-evaluable IDs are static; runtime-only IDs are flagged unless marked
  private. Dynamic entities export typed patterns (`cell_{CellRef}` + codec).
  `.sui` extraction is DEFERRED (3 example files, zero production use,
  seed-only parser); a pure-Simple `.sui` AST becomes in-scope only when
  `.sui` gains a production consumer.

## Decision 4 — SSpec target syntax (FROZEN)

- Header directives: `# @ui: <app-id>` and `# @ui-target: tui|gui|web|both`.
- Target forms: bare id = compiled symbol; dotted = qualified id; quoted
  string = accessible-name fallback (runtime strict); `id(expr)` = runtime
  escape hatch; omitted target = the focused node.
- Resolution precedence: symbol → qualified → pattern → runtime id → name
  fallback. Ambiguity at any stage is UIE1004, never first-match.
- `both` means semantic parity (IDs, state, model results, focus meaning),
  never pixel parity.

## Decision 5 — Compatibility / alias policy (FROZEN)

- Wire encoding stays `surface#widget`; `scope_path` is added additively so
  existing consumers keep parsing. Default surface stays `main`.
- Migration order is expand → migrate (WidgetNode/Store → UITree → layout →
  renderers → access → SGTTI/drivers → office apps) → contract (delete global
  store, silent upsert, first-match).
- Renames of public IDs ship as alias-first (old id remains an alias with
  `deprecated_since`), removal only after `remove_after` and a lock-compat
  major bump.

## Decision 6 — Web-host transport contract (summary, FROZEN direction)

- One HTTP substrate: `src/lib/common/net/http_core.spl`. `ui.web` today runs
  its own `async_server.spl` + `tls_serve_loop.spl`; Agent N's first task is
  migrating it onto http_core, or recording an explicit two-stack decision
  with a security-parity checklist. A third stack is prohibited.
- HostInterface v2 extends `src/app/ui.web/host_adapter_contract.spl`:
  `attach(session)`, event in / frame out, capability negotiation, auth
  token, reconnect/resume.
- Transport: websocket carrying (a) semantic access-snapshot diff stream and
  (b) input events. Calc's polling access server
  (`src/app/office/sheets/access_server.spl`,
  `calc_access_session_host.spl`) is retired by Agent H against N's contract.
- Remote mode (`office serve --listen`): session tokens, origin guard, TLS,
  per-session WidgetStore. Gates: auth required, origin enforced, two
  sessions never share widget identity, reconnect resumes
  revision-correlated state.

## Consequences

- Agents C/D generate manifests/symbols only against Decisions 1–4; drivers
  (F/G/N) execute only compiled `UiActionPlan`s under the execution law in
  the arch doc; Calc v1 (Agent H) is the acceptance vehicle.
- Any schema drift found during implementation comes back here as ADR-00N,
  not as an in-place edit to generated code.
