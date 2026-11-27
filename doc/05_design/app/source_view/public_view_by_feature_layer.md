# MDSOC+ Public View by Feature and by Layer — Design (2026-11-12)

Requirements: `doc/02_requirements/app/lsp/mdsoc_public_view.md` (REQ-PUBVIEW-*).
Architecture: `doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md`
(§ Visibility Rules: tree-private by default, parent-public, next-layer-public).

## Why

When an LLM reviews or fixes code through the LSP (raw, or via the
`simple-lsp-mcp` bridge) or through `source_open`, it must see the *public*
surface by default — and it must be able to tell **from the response itself**
that private symbols exist and how to reveal them. A hidden symbol that leaves
no trace is a silent omission; this design makes every hide produce an in-band
hint and an omission-ledger row.

## Visibility classes

One classifier, `visibility_class_of(symbol, owner_file)` in
`src/app/cli/_QueryVisibility/visibility_class.spl`, maps the language's real
rules to four classes. It composes the existing text-level facts
(`declared_visibility`, `exported_by`, `nearest_boundary_dir`,
`feature_dir_of`, `feature_expose_paths`) — it is **not** a second
effective-visibility engine. Lane U2 (`work/u2-semantic-api-20261112`) is
wiring the exported type graph in `src/compiler/35.semantics/lint/**`; when it
lands, `visibility_class_of` is the single seam to swap to that result.

| class | language rule | reachable from |
|---|---|---|
| `public` | `pub` and named in the **feature capsule root** `__init__.spl` export surface (`export A, B`, `export use m.{A}`, or an `exports { expose = [...] }` port). Without a capsule: `pub` and named in the nearest layer `__init__.spl` export line, or `pub` in an open module (no `__init__.spl` ancestor). | anywhere |
| `feature_private` | `pub` and exported by the nearest layer `__init__.spl` but not by the feature root; also `pub(peer)`, `pub(package)`, `pub(friend)` (they cross layers inside one feature/package). | other layers of the same feature |
| `layer_private` | `pub` but not exported by the nearest layer `__init__.spl`; also `pub(up)` (only the parent facade). | files inside the layer boundary |
| `module_private` | no `pub` (or `pri`). | the declaring file only |

Reveal levels are cumulative: `visibility=public` (default) shows `public`;
`feature_private` adds feature-private; `layer_private` adds layer-private;
`all` adds module-private. Exactly one class is added per step so "each reveal
level shows exactly the expected extra symbols" is a testable property.

**Default scope.** The public-only default applies to files under an MDSOC
boundary (an `__init__.spl` ancestor exists). A file with no boundary (scripts,
specs, fixtures) is an open module: there is no feature or layer to be private
to, so its default is `all` and the response states
`visibility_default: "all (open_module_no_init_boundary)"`. This keeps the
existing `source_open` fixtures (no `__init__.spl`) byte-identical and is still
never silent: the hidden summary reports zero hidden and the narrowing handle.

## Views

| view | selector | population |
|---|---|---|
| file | `path` (`source_open`, `lsp_symbols`, `textDocument/documentSymbol`) | declarations of one file |
| by feature | `feature=<capsule id>` on `workspace/symbol` / `lsp_workspace_symbols` / `query_visibility workspace-symbols --feature` | every file under the capsule root, across all its layers |
| by layer | `layer=<layer dir name>` (e.g. `10.core`, `35.semantics`) | every file whose nearest layer dir has that name, across all features |
| global | neither selector, `query=""` | whole `src/` tree |

All views take the same `visibility` argument and return the same hidden
summary. Feature/layer identity is derived from the path (`feature_id_of`,
`layer_dir_name`) — the same functions the requester-scoped `lsp_visibility`
tool already uses.

## Hidden summary — the in-band hint

Every response that hides at least one symbol carries, **inside the result the
LLM reads**:

1. a structured `hidden_summary`:
   `{"hidden": 12, "visibility": "public", "by_class": {"feature_private": 8, "layer_private": 4},
     "by_kind": {"fn": 8, "type": 4}, "top_names": ["a_core_inner", ...],
     "reveal": {"mcp": {"visibility": "feature_private"}, "lsp": {...}}, "hint": "..."}`
2. a one-line `hint` text that an LLM reads without parsing, e.g.
   `⋯ 12 hidden (8 feature_private fn, 4 layer_private type) — reveal: lsp_symbols visibility="feature_private"; LSP initializationOptions.simple.visibility or workspace/executeCommand simple.setVisibility ["feature_private"]; visibility="all" shows everything`.

Where it lives per surface:

- **MCP `source_open`**: field `hidden_summary`; one `omission_ledger` row per
  hidden top-level node with `reason: "visibility_hidden"`, `visibility_class`,
  and `reopen: {"visibility": "<class>"}`; the rendered text ends with the hint
  line. Members of a shown container stay with their container (a class's
  methods are its surface); hidden-class *top-level* nodes are what is dropped.
- **`lsp_symbols` / `textDocument/documentSymbol`**: a trailing synthetic
  `DocumentSymbol` named with the hint text, `kind` 1 (File), zero range, and
  `simpleHiddenSummary` = the structured summary. LLM bridges drop
  notifications, so the symbol list itself carries the hint.
- **`workspace/symbol` / `lsp_workspace_symbols`**: same synthetic
  `SymbolInformation` entry, `location` = the queried root.
- **Hover**: `textDocument/hover` on a position with no symbol (file header,
  blank line, `use` line) answers with the file's hidden summary as Markdown;
  `simple/hiddenSummary` (custom request `{textDocument:{uri}}`) returns the
  structured summary for a file. `lsp_hover` through the bridge inherits both.

## Reveal mechanisms (exact)

| surface | how |
|---|---|
| `simple-lsp-mcp` tools | `lsp_symbols {file, visibility: "feature_private"\|"layer_private"\|"all"}`; `lsp_workspace_symbols {query, visibility, feature, layer}` |
| raw LSP, session default | `initialize.initializationOptions.simple.visibility = "<level>"` |
| raw LSP, live change | `workspace/executeCommand {command: "simple.setVisibility", arguments: ["<level>"]}` — advertised in `executeCommandProvider.commands` |
| raw LSP, per request | `textDocument/documentSymbol` / `workspace/symbol` params may carry `simpleVisibility`, `feature`, `layer` |
| MCP `source_open` | `visibility`, and the ledger row's `reopen` object |
| CLI | `simple src/app/cli/query_visibility.spl symbols <file> --visibility <level>`; `workspace-symbols --query q --visibility <level> [--feature id] [--layer name]` |

## Omission ledger

`source_open` already lists every omitted range with a reason and a retrieval
handle. Visibility adds `reason: "visibility_hidden"` rows; the invariant
"nothing is omitted without a ledger row" now covers hidden symbols. The LSP
synthetic summary entry is the ledger row of the symbol list.

## Module layout

- `src/lib/nogc_sync_mut/source/visibility_view.spl` — pure: class constants,
  `source_visibility_admits_v1`, `SourceHiddenSummaryV1`,
  `source_hidden_summary_v1`, `source_hidden_hint_v1`, feature/layer selector
  filter. No I/O; both MCP and LSP build on it.
- `src/app/cli/_QueryVisibility/visibility_class.spl` — the classifier seam.
- `src/app/cli/_QueryVisibility/query_commands.spl` — `--visibility`,
  `--feature`, `--layer`, synthetic summary entry.
- `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` — session level from
  initializationOptions / executeCommand, hover fallback, `simple/hiddenSummary`.
- `src/app/simple_lsp_mcp/tools.spl` — tool args forwarded.
- `src/app/source_view/service.spl` — `visibility` arg, ledger rows, summary.

## Fixture

`test/fixtures/mdsoc_pubview/` — two features (`feature_x`, `feature_y`) ×
two layers (`10.core`, `20.app`), each layer with its own `__init__.spl`, and
each file holding one symbol of every class so every reveal step adds exactly
one known symbol.

## Session view state (REQ-PUBVIEW-010..012, 2026-11-13)

Pure transition: `src/lib/nogc_sync_mut/source/visibility_session.spl`
(`SourceVisibilitySessionV1 {level, feature, layer, served, limit, notice}`).
Each server keeps exactly one current value and replaces it with what
`source_visibility_session_set_v1` / `source_visibility_session_serve_v1`
return — no mutation of shared state, no locks.

- **set**: an explicit level (+ scopes) starts a fresh countdown; `public` from a
  private view is a revert with reason `explicit visibility=public`.
- **serve**: a valid per-request level serves once and returns the session
  unchanged; a private session view counts one request and, on the `limit`th
  (default 3, `SIMPLE_VISIBILITY_AUTO_REVERT`), still serves privately then
  reverts. The next public response carries the one-shot revert notice.
- **view line**: `view: <level>[ (feature=…, layer=…)]` + countdown /
  override / revert suffix, stated beside an unchanged listing shape.

Wiring: `src/app/simple_lsp_mcp/visibility_state.spl` (MCP `simple_set_visibility`,
`content[1]` view line) and `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl`
(raw LSP `simple.setVisibility`, documentSymbol/workspace symbol countdown).
MCP `source_open` (simple-mcp) still takes a per-request `visibility` only.
Specs: `test/01_unit/lib/source/visibility_session_spec.spl`,
`test/02_integration/app/lsp/lsp_mcp_visibility_session_spec.spl`,
`test/02_integration/app/lsp/lsp_public_view_handlers_spec.spl`.
