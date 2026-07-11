<!-- codex-design -->
# UI CLI LLM Access — Detail Design

## Design target

Implement the selected `REQ-UCLA-001..025` and `NFR-UCLA-001..022` by extracting the reusable portion of T32 GUI CLI grammar into `common.ui`, then wiring thin live UI and WM adapters. Existing snapshot/query/history records remain authoritative.

## Files and ownership

| Path | Change | Owner |
|---|---|---|
| `src/lib/common/ui/access_cli_grammar.spl` | New shared descriptor/request/result/error/safety/output records plus validation and rendering | common UI |
| `src/lib/common/ui/access.spl` | Re-export shared grammar | common UI |
| `src/lib/common/ui/win_text_access.spl` | Remove `WindowInfo` import; accept already-normalized surface/node values | common UI |
| `src/app/t32_cli/commands.spl` | Map overlapping GUI commands to shared descriptors; keep T32-only catalog entries | T32 adapter |
| `src/app/t32_cli/types.spl` | Compatibility alias `T32BridgeResult = AccessResult` | T32 adapter |
| `src/app/t32_cli/render.spl` | Forward to shared human renderer; retain only T32 GUI-status decoration if needed | T32 adapter |
| `src/app/t32_cli/mod.spl` | Parse output mode and map T-code/text failures to `AccessError` | T32 adapter |
| `src/app/ui/access_cli.spl` | New UI descriptor catalog and live test-API/read-only-store adapter | UI adapter |
| `src/app/ui/cli_entry.spl` | Dispatch access verbs before backend modes; preserve existing modes | UI entry |
| `src/app/play/wm_access_cli.spl` | New live WM conversion/dispatch owner | WM adapter |
| `src/app/play/main.spl` | Replace planned WM branches with live calls; preserve spellings | play entry |
| `scripts/check/check-ui-cli-access.spl` | Pure Simple focused scenario checker | evidence |

No renderer, generic adapter trait, or new service is added. The persisted UI
store gains one additive property column so capture/staleness metadata survives
read-only fallback.

## Shared grammar types

Use composition and text-backed validated operation/output types for current compiler compatibility:

```simple
type AccessOperation = text
type AccessOutputMode = text

class AccessSafety:
    read_only: bool
    destructive: bool
    idempotent: bool
    requires_confirmation: bool
    may_prompt: bool
    timeout_ms: i64

class AccessCommandDescriptor:
    name: text
    subcommand: text
    handler_key: text
    operation: AccessOperation
    usage: text
    example: text
    min_args: i64
    description: text
    aliases: [text]
    safety: AccessSafety

class AccessRequest:
    descriptor: AccessCommandDescriptor
    output_mode: AccessOutputMode
    source_id: text
    session_id: text
    correlation_id: text
    args: [text]
    timeout_ms: i64
    confirmed: bool

class AccessError:
    code: text
    message: text
    source_code: text
    hint: text
    retryable: bool
    interaction_required: bool

class AccessResult:
    schema_version: i32
    operation: AccessOperation
    source_id: text
    session_id: text
    revision: i64
    correlation_id: text
    kind: text
    title: text
    rows: [[text]]
    kv_pairs: [[text]]
    scalar_value: text
    raw_output: text
    items: [text]
    payload_json: text
    returned_count: i64
    truncated: bool
    gui_status: i32
```

`AccessResult` retains the existing T32 scalar/table/kv/list/raw constructors so `T32BridgeResult` can be a zero-behavior type alias. New snapshot/document constructors add source, revision, payload, and bounds.

## Common functions

```simple
fn access_find_descriptor(name: text, subcommand: text, descriptors: [AccessCommandDescriptor]) -> AccessCommandDescriptor?
fn access_validate_request(request: AccessRequest) -> Result<(), AccessError>
fn access_validate_snapshot_action(snapshot: UiAccessSnapshot, target_id: text, action: text) -> Result<UiAccessNode, AccessError>
fn access_result_from_snapshot(operation: AccessOperation, source_id: text, session_id: text, snapshot: UiAccessSnapshot, limit: i64) -> AccessResult
fn access_render_human(result: AccessResult) -> text
fn access_render_json(result: AccessResult) -> text
fn access_error_to_json(operation: AccessOperation, request_id: text, error: AccessError) -> text
```

Parsing remains adapter-owned. Common validation owns operation/output validity,
minimum arguments, timeout positivity, confirmation policy, and snapshot action preflight.

## T32 mapping

- Keep `simple t32` as the executable root.
- Existing `T32CliCommand` catalog stays authoritative for all 36 T32 commands.
- Its overlapping `windows`, `window show/describe`, `action do/list`, and `history` entries expose mapped `AccessCommandDescriptor` values.
- `T32BridgeResult` aliases `AccessResult`; existing bridge constructors compile unchanged.
- Existing T-codes remain `source_code`; the boundary maps them to stable common codes.
- T32-only sessions/CMM/jobs/dialog commands retain their existing dispatch and safety checks.

## Live UI adapter

`src/app/ui/access_cli.spl` uses the existing HTTP facade and existing routes:

| Operation | Route |
|---|---|
| `windows`, `snapshot` | `GET /api/test/ui/snapshot` |
| `surface` | `GET /api/test/ui/surface?id=...` |
| `find` | `GET /api/test/ui/query?...` |
| `act` | `POST /api/test/ui/act` followed by one surface/history observation |
| `history` | `GET /api/test/ui/history?...` |

Default endpoint is loopback plus configured `--port`; timeout is finite. HTTP status/body errors map once to `AccessError`. One read operation makes one request. Live GUI/web and TUI-web fixtures use their already-mounted test API.

When `--ui-access-db` is explicitly chosen, the adapter opens the existing `UiAccessStore`, reads surfaces/nodes/events, reconstructs a captured snapshot, and reports capture/staleness. It implements windows/snapshot/surface/find/history only. `act` returns `source_unavailable`; no DB command queue is created.

## WM adapter

`wm_access_cli.spl` calls the WM owner for each inventory operation, converts
private `WindowInfo` values to a `UiAccessSurface` plus root `UiAccessNode`, then
uses common projection/query/rendering. Actions inventory once before dispatch
and once for post-action observation. Text/path/coordinate inputs are bounded,
each owner subprocess is capped at two seconds, and the adapter stops later
phases when the 20-second request deadline expires. Correlation-store failure
is an action failure, not best-effort success. No host type crosses into common UI.

## Identity and ordering

- UI identity remains `surface_id#widget_id` within a UI session generation.
- T32 identity combines session plus catalog/live-window disambiguator; titles remain labels.
- WM identity uses the current native target identifier; title is never the key where a native handle exists.
- A single-source list is ordered by `surface_id`.
- UI may return `stale_target`; WM v1 has revision `0` and re-resolves to typed not-found/state/action errors.

## Rendering and exits

Human and JSON output derive from one `AccessResult`. Human missing values render `-`; JSON uses `null`. JSON stdout is one UTF-8 envelope, never log text. Usage/schema failure exits 2, runtime failure exits 1, and success exits 0. Diagnostics use structured logging/stderr; no production `print` is added outside the intentional CLI output owner.

## Safety and history

Read descriptors are `read_only=true`. `act` re-resolves, checks advertised action and enabled/busy/defunct state, validates bounded input, enforces timeout/confirmation policy, executes exactly one adapter action, then observes once. Missing semantic actions never fall back to raw input. Existing `UiAccessEvent` history remains bounded at 64; request and result share one correlation ID.

## Error mapping

Adapters map private failures to the selected stable codes. Empty is success only when a source was reached. Service refusal maps to `source_unavailable`; DB action maps to `source_unavailable`; T32 dialog state maps to `interaction_required`; missing/removed IDs map to `target_not_found`/`stale_target`; unsupported host descendants/actions map to `unsupported_action`.

## Test and evidence hooks

The Pure Simple checker `scripts/check/check-ui-cli-access.spl` owns deterministic fixtures and calls real common/app entry functions. System scenarios call it through `bin/simple run`, require scenario-specific evidence markers, and capture TUI/protocol/GUI artifacts. The checker has no alternate pass path: missing live fixtures, commands, measurements, captures, or final review evidence fail nonzero.

`scripts/check/check-ui-cli-live-transport.shs` separately launches
`test/fixtures/ui_cli_access/live_server.spl`, drives windows/find/act/history
through a second CLI process, stops the service, and verifies read-only database
fallback plus fail-closed database action.

## Performance plan

The checker constructs the selected 100-window/1,000-node fixture, warms once, measures retained iterations, records p50/p95 and maximum RSS through existing facades, and asserts list/snapshot <=100 ms p95, find/pre-action <=20 ms p95, RSS delta <=20 MiB, history <=64, one refresh/request per read, and no per-record subprocess.

## Compatibility and migration order

1. Add common grammar and focused unit tests.
2. Alias T32 result/rendering and add descriptor parity without changing T32-only commands.
3. Add UI HTTP/store adapter and deployed entry routing.
4. Add live WM adapter and switch planned branches.
5. Implement checker/system evidence and generate/review the manual.
6. Run entry-closure, dependency, runtime-guard, focused correctness, and perf gates once after convergence.
