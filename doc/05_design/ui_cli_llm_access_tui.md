<!-- codex-design -->
# UI CLI LLM Access — CLI/TUI Design

**Feature:** `ui_cli_llm_access`  
**Status:** normative/aspirational mockup; current renderer is simpler
**Requirements:** REQ-UCLA-001..025, NFR-UCLA-001..022

## One grammar, existing command roots

TRACE32, Simple UI, and host WM share the same access grammar; they do not
share backend code. The common library owns the data-only operation descriptor,
result envelope, typed errors, deterministic rendering, canonical identity,
action preflight, and history correlation. Each adapter owns live enumeration,
capture, refresh, and action execution.

The shared vocabulary is deliberately small:

- `AccessCommandDescriptor`: registered name, operation, arguments, output
  modes, and safety declaration;
- `AccessOperation`: `list`, `snapshot`, `surface`, `find`, `act`, or `history`;
- `AccessRequest` / `AccessResult`: versioned request and structured outcome;
- `AccessError`: stable code, message, retryability, and interaction flag;
- `AccessSafety`: read-only/mutating, semantic confidence, confirmation, bounds,
  and timeout metadata;
- `AccessOutputMode`: `human` or `json`.

These are grammar records, not a new snapshot model. Payloads continue to use
`UiAccess*` and `WinText*` records.

| Grammar operation | `simple t32` | `simple ui` | `simple play` host WM |
|---|---|---|---|
| `list` | `windows` | `windows` | `windows` (`wm-list` alias) |
| `snapshot` | `window show <key>` | `snapshot` | `wm-text-snapshot host_wm` |
| `surface` | `window show <key>` | `surface <id>` | not implemented in WM v1; use `wm-text-find` |
| `find` | captured-text query | `find` | `wm-text-find host_wm <text>` |
| `act` | `action do <key>` | `act` | `wm-text-act <canonical-id> <action>` |
| `history` | `history [count]` | `history` | correlated WM access history |

`window show` remains TRACE32's capture spelling. `wm-list` and existing
`wm-text-*` spellings remain compatible. No alias is required merely to make
the command strings identical: parity is defined by the shared descriptor and
result grammar.

Canonical targets remain source scoped:

```text
Simple UI: main#submit
TRACE32:   trace32:register#root
Host WM:   wm:0x04a00007#root
```

## Human output

Human output is the default. It is stable enough to read, but scripts must use
`--json`. An unavailable value is printed as `-`, never inferred.

### `windows`

```text
$ simple ui windows
UI windows (v1)  source=simple_ui  revision=42  captured=2026-07-11T12:00:00Z
ID              TITLE             OWNER       KIND  STATE   GEOMETRY       FOCUS VISIBLE CAPS
main            Simple Editor     simple.ui   gui   ready   0,0 1280x800   yes   yes     snapshot,find,act,history
build-log       Build Log         simple.ui   tui   ready   -              no    yes     snapshot,find,history
2 windows  truncated=no  stale=no

$ simple t32 windows
TRACE32 windows (v1)  source=trace32  session=s1  captured=2026-07-11T12:00:01Z
ID                  TITLE        OWNER    KIND          STATE     GEOMETRY FOCUS VISIBLE CAPS
trace32:register    Registers    trace32  remote_text   available -        -     -       open,capture,find,act
trace32:data.list   Data.List    trace32  remote_text   available -        -     -       open,capture,find,act
2 windows  truncated=no  stale=no

$ simple play wm-list
WM windows (v1)  source=host_wm  captured=2026-07-11T12:00:02Z
ID                TITLE          OWNER      KIND        STATE  GEOMETRY          FOCUS VISIBLE CAPS
wm:0x04a00007     Simple Editor  simple     host_window ready  100,80 1280x800   yes   yes     focus,type_text,click_xy,screenshot
1 window  truncated=no  stale=no
```

Ordering is deterministic: normalized source order, then stable source/session
identity. Geometry, focus, visibility, parent, or capture time may be `-` only
when the source cannot report them.

### `snapshot`

```text
$ simple ui snapshot
UI snapshot (v1)  mode=NORMAL  revision=42  active=main

[main] Simple Editor  gui active
  main#root          panel      ""                    enabled visible
  main#title         text       "Project: simple"     enabled visible
  main#build         button     "Build"               enabled visible  actions=click

[build-log] Build Log  tui
  build-log#root     panel      ""                    enabled visible
  build-log#line_0   text       "Build succeeded"     enabled visible

2 surfaces, 5 nodes, 8 recent events  truncated=no
```

The TUI renderer groups by surface and prints canonical IDs inline. GUI and TUI
trees use the same `UiAccessSnapshot`; rendering technology is metadata, not a
different protocol.

Live `simple ui` reads target the existing local test API (default loopback and
configured `--port`). GUI/web and TUI-web hosts mount that API over their live
`UISession`. An explicitly selected `--ui-access-db` fallback is captured,
stale-aware, and read-only; it rejects `act` instead of simulating execution.

### `surface`

```text
$ simple ui surface main
Surface main  title="Simple Editor"  active=yes  root=main#root  revision=42
  main#root          panel      ""                 actions=-
  main#title         text       "Project: simple"  actions=-
  main#build         button     "Build"            actions=click
3 nodes  truncated=no
```

### `find`

```text
$ simple ui find --surface main --kind button --text build --limit 20
Find source=simple_ui surface=main kind=button text="build" revision=42
CANONICAL ID  KIND    TEXT     STATE                    ACTIONS
main#build    button  "Build"  enabled,visible,unbusy   click
1 match  truncated=no

$ simple play wm-text-find host_wm Editor
Find source=host_wm text="Editor"
CANONICAL ID          KIND         TEXT             ACTIONS
wm:0x04a00007#root    host_window  "Simple Editor"  focus,type_text,click_xy,screenshot
1 match  truncated=no
```

Find is bounded and returns IDs that can be passed unchanged to `act`.

### `act`

```text
$ simple ui act --canonical main#build --action click --timeout 2000
ok  request=act-000184  source=simple_ui  target=main#build  action=click
revision 42 -> 43  observed=yes

$ simple play wm-text-act wm:0x04a00007#root focus
ok  request=act-000185  source=host_wm  target=wm:0x04a00007#root  action=focus
observed=yes
```

Before dispatch the common owner re-resolves the target against the live
revision, checks advertised capability and enabled/busy/defunct state, validates
bounded arguments, and applies confirmation policy. The adapter then executes
the action. Raw pointer or keyboard input is never substituted for a missing
semantic action.

### `history`

```text
$ simple ui history --surface main --count 10
Access history  source=simple_ui  surface=main  newest-first  count=2/64
TIME                         REQUEST     PHASE    TARGET       ACTION STATUS CODE
2026-07-11T12:00:04.042Z     act-000184  result   main#build   click  ok     ok
2026-07-11T12:00:04.011Z     act-000184  request  main#build   click  -      -
```

Request/result records share one correlation ID. Default history stays bounded
at 64 events. It is operational evidence, not a durable audit log.

## JSON output

`--json` writes exactly one versioned UTF-8 object to stdout. Diagnostics go to
stderr. Arrays use the documented deterministic order; clients must not depend
on object-member order.

### Normalized list

```json
{"schema":"simple.access/v1","operation":"list","source":{"id":"host_wm","session":null,"kind":"top_level_wm"},"revision":17,"captured_at":"2026-07-11T12:00:02Z","items":[{"id":"wm:0x04a00007","title":"Simple Editor","owner":"simple","surface_kind":"host_window","state":"ready","geometry":{"x":100,"y":80,"width":1280,"height":800},"focused":true,"visible":true,"parent_id":null,"capabilities":["focus","type_text","click_xy","screenshot"],"captured_revision":17,"captured_at":"2026-07-11T12:00:02Z","stale":false}],"page":{"limit":100,"returned":1,"truncated":false,"next":null}}
```

### Snapshot and find

```json
{"schema":"simple.access/v1","operation":"snapshot","source":{"id":"simple_ui","session":"ui-7","kind":"in_process_semantic"},"revision":42,"result":{"protocol_version":1,"mode":"NORMAL","active_surface":"main","surfaces":[{"surface_id":"main","title":"Simple Editor","active":true,"window_id":"win-1","app_id":"simple.ui","root_canonical_id":"main#root"}],"nodes":[{"canonical_id":"main#build","surface_id":"main","widget_id":"build","kind":"button","visible":true,"focused":false,"enabled":true,"selected":false,"text_value":"Build","props":[],"child_ids":[],"action_names":["click"]}],"recent_events":[]},"page":{"limit":1000,"returned":1,"truncated":false,"next":null}}
```

```json
{"schema":"simple.access/v1","operation":"find","source":{"id":"simple_ui","session":"ui-7","kind":"in_process_semantic"},"revision":42,"query":{"surface":"main","kind":"button","text":"build","limit":20},"items":[{"canonical_id":"main#build","kind":"button","text":"Build","enabled":true,"busy":false,"defunct":false,"actions":["click"]}],"page":{"limit":20,"returned":1,"truncated":false,"next":null}}
```

### Action result and typed failure

```json
{"schema":"simple.access/v1","operation":"act","request_id":"act-000184","source":{"id":"simple_ui","session":"ui-7","kind":"in_process_semantic"},"target":"main#build","action":"click","ok":true,"revision_before":42,"revision_after":43,"observed":true,"safety":{"read_only":false,"semantic":true,"confirmation":"not_required","timeout_ms":2000}}
```

```json
{"schema":"simple.access/v1","operation":"act","request_id":"act-000186","ok":false,"error":{"code":"stale_target","message":"target main#build no longer exists at revision 44","retryable":true,"interaction_required":false},"safety":{"read_only":false,"semantic":true,"confirmation":"not_required","timeout_ms":2000}}
```

## Typed errors and exits

| Code | Meaning | Retry guidance |
|---|---|---|
| `invalid_argument` | malformed option, selector, bound, or payload | fix request |
| `source_unavailable` | session/backend is absent or headless without an adapter | start/select source |
| `interaction_required` | confirmation or prompt boundary blocks dispatch | obtain explicit approval |
| `permission_denied` | adapter or OS rejected access | change permissions |
| `unsupported_action` | target does not advertise the action | inspect capabilities |
| `target_not_found` | no current scoped target | list/find again |
| `stale_target` | prior identity/revision no longer resolves safely | refresh then retry |
| `target_disabled` | target exists but is disabled/defunct | wait or choose another target |
| `target_busy` | target is temporarily busy | retry after observation |
| `timeout` | bounded adapter execution/observation expired | inspect history/state |

Usage/schema errors and runtime errors exit nonzero. A successful empty list
exits 0 with `items=[]`; unavailable, interaction-required, permission denied,
unsupported rendering, and timeout are failures with distinct codes.

## Capture plan

System scenarios capture the real rendered state, not hand-written expected
text:

- CLI and native TUI: save plain/ANSI output under
  `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui/`; capture `windows`,
  `snapshot`, `surface`, `find`, `act`, and `history`, plus one typed failure.
- JSON: save stdout as protocol evidence under
  `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/` and parse it;
  separately capture stderr and exit status to prove clean machine output.
- GUI: capture the live fixture before and after action under
  `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/`.
- Generated manual: embed the paths with `**TUI Captures:**` and
  `**Screenshots:**`; screenshots supplement semantic assertions and never
  replace snapshot/find/action/history checks.

Required fixture matrix: one GUI session, one native TUI session, one TRACE32
catalog/capture session, one host-WM top-level window, one zero-window source,
and typed unavailable/stale/unsupported/disabled/busy/permission/timeout cases.

## Accessibility and terminal behavior

- Never encode focus, state, or failures by color alone.
- Respect `NO_COLOR`; JSON never contains ANSI escapes.
- Tables degrade to one-record-per-block when the terminal is narrow.
- Titles and text are escaped; control characters never execute in the terminal.
- Bounds and truncation are visible in both human and JSON modes.
