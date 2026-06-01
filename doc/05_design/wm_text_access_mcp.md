<!-- codex-design -->
# WM Text Access MCP — Detail Design

Status: Draft pending final requirement selection.

## Data Model

### Access Source

Fields:

- `source_id`: stable adapter ID such as `trace32`, `simple_ui`, `host_wm`
- `source_kind`: `semantic`, `wm`, `remote`, `vision`
- `confidence`: `high`, `medium`, `low`
- `capabilities`: list of supported operations
- `captured_at`: timestamp for cached material
- `max_age_ms`: adapter-defined freshness budget
- `stale`: true when cached data is older than the adapter budget

### Surface

Fields:

- `surface_id`
- `title`
- `kind`: `trace32_window`, `simple_ui_surface`, `host_window`
- `active`
- `root_node_id`
- `source`
- `window_id` when backed by a top-level host window
- `capabilities`

### Node

Fields:

- `node_id`
- `surface_id`
- `parent_id`
- `role`
- `kind`
- `text`
- `value`
- `bounds`
- `state`
- `capabilities`
- `metadata`

TRACE32 text captures may produce line or field nodes. Host WM top-level windows produce one root/window node per surface. Simple UI adapter keeps existing canonical node identity.

### Selector

Fields:

- `surface_id`
- `node_id`
- `role`
- `kind`
- `text`
- `value`
- `focused_only`
- `limit`

Selector matching is implemented once in the shared core.

### Action Request

Fields:

- `target_id`
- `action`
- `text`
- `value`
- `x`
- `y`
- `refresh_before`

The router validates target capabilities before invoking an adapter.

## Operations

### Snapshot

1. Resolve adapter by source or all enabled adapters.
2. Return cached snapshot when not stale unless `refresh=true`.
3. Normalize adapter output into shared surfaces/nodes.
4. Attach source/capability/staleness metadata.

### Query/Find

1. Get snapshot through the facade.
2. Run shared selector matching against normalized nodes.
3. Return matches with source metadata and stable IDs.
4. Do not call backend-specific parsers from MCP handlers.

### Action

1. Resolve target surface/node.
2. Check requested action against target capabilities.
3. Dispatch to adapter.
4. Invalidate affected snapshot cache after mutation.
5. Return structured result or unsupported error.

### Value

1. Resolve target node.
2. Require `value_read` or `value_write` capability.
3. Return unsupported for host WM top-level nodes unless a semantic adapter owns the node.

## Adapter Designs

### TRACE32 Adapter

Inputs:

- catalog entries from the existing TRACE32 window catalog
- capture commands such as `WinPrint.Register.view`
- fallback capture via `PRinTer.FILE`
- AREA output for headless text
- action and field catalogs

Behavior:

- `snapshot` creates one surface per cataloged/captured window.
- `refresh` opens/captures a selected window when requested.
- text capture is parsed into line nodes by default.
- field catalogs may add field nodes when a parser is available.
- unsupported parser cases still expose raw text lines.

Capabilities:

- `open`
- `capture`
- `query_text`
- `act_catalog`
- `value_read` only for parseable fields

### Simple UI Adapter

Inputs:

- existing `common.ui.access` snapshot model
- `window_surface_registry` metadata when available

Behavior:

- wraps existing canonical access snapshot without changing base contract.
- preserves canonical node IDs.
- adds adapter source metadata around surfaces/nodes.

Capabilities:

- inherits supported Simple UI access capabilities.

### Host WM Adapter

Inputs:

- `wm_list_windows`
- `wm_focus_window`
- `wm_click`
- `wm_type_text`
- `wm_press`
- screenshot when available

Behavior:

- maps each top-level `WindowInfo` to a surface.
- maps each top-level window to one root node.
- internal controls are not invented.
- click/type/focus actions are exposed only at window/coordinate level.

Capabilities:

- `list`
- `focus`
- `type_text`
- `click_xy`
- `screenshot`

Unsupported:

- arbitrary text-field value writes
- button/menu invocation by internal label
- child control tree queries

## CLI/Service/MCP Surface

Proposed operations:

- `wm_access_snapshot`
- `wm_access_surface`
- `wm_access_find`
- `wm_access_act`
- `wm_access_value`
- `wm_access_history`
- `wm_access_adapter_status`

Existing `play_ui_*` and `play_wm_*` tools can remain, but new unified tools should call the shared facade. Existing tools can later become compatibility wrappers.

## Error Model

Use structured errors:

- `adapter_unavailable`
- `unsupported_operation`
- `target_not_found`
- `stale_snapshot`
- `refresh_failed`
- `backend_error`
- `invalid_selector`

Errors include adapter ID, operation, target ID when available, and a short human-readable message.

## Observability

Every adapter status includes:

- enabled/available
- last refresh time
- last refresh duration
- cache age
- cache hit/miss count
- last error

MCP debug output should include whether a response came from cache.

## Test Mapping

- AC/REQ for shared snapshot: adapter fixture snapshot tests.
- AC/REQ for query: selector tests across TRACE32, Simple UI, and host WM fixtures.
- AC/REQ for action routing: supported and unsupported action tests.
- AC/REQ for hot path: repeated query over cached host WM/TRACE32 snapshot does not refresh every call.
- AC/REQ for MCP/CLI/service reuse: handler tests assert unified facade use rather than direct backend query logic.

## Implementation Notes

- Keep OS accessibility adapters out of first implementation unless selected.
- Do not run subprocesses in selector matching.
- Do not add screenshot/OCR as a semantic source; expose it only as low-confidence evidence.
- Promote reusable TRACE32 catalog/capture logic from `examples/` into owned source before relying on it from production MCP.

