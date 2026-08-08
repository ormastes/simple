<!-- codex-design -->
<!-- codex-architecture -->
# UI CLI LLM Access Architecture

**Status:** Accepted for implementation  
**Date:** 2026-07-11  
**Requirements:** `REQ-UCLA-001` through `REQ-UCLA-025`, `NFR-UCLA-001` through `NFR-UCLA-022`

## Decision

TRACE32, Simple UI, and host WM access share one small, data-only CLI grammar:

- `AccessCommandDescriptor`
- `AccessOperation` (`list`, `snapshot`, `surface`, `find`, `act`, `history`)
- `AccessRequest`
- `AccessResult`
- `AccessError`
- `AccessSafety`
- `AccessOutputMode` (`human`, `json`)

The grammar belongs in `src/lib/common/ui/` and has no renderer, WM backend,
TRACE32, process, environment, persistence, or mutable-host dependency.
`UiAccessSnapshot` and `WinTextSnapshot` remain the semantic data models. The
shared grammar describes commands and presentation; it does not introduce a
second snapshot, selector, action, or history model.

Current implementation deltas are explicit: parsing stays adapter-owned;
TRACE32 shares descriptors/results/rendering but keeps its established argument
dispatcher; WM has no `surface` verb or client revision check in v1; and the
actual JSON envelope is the additive `schema_version/kind/rows/kv/scalar/raw/
items/result/page{returned,truncated}` shape emitted by common UI.

Live enumeration, capture, refresh, and action execution remain in the source
that already owns them. Common code owns only descriptor validation,
normalization, ordering, safe pre-dispatch checks, stable errors, bounded
history rules, and human/JSON rendering.

## Why this is the minimum design

The repository already has the semantic core in
`src/lib/common/ui/access_types.spl`, `access_query.spl`, and
`win_text_access.spl`. TRACE32 already has a command registry, bridge result,
renderer, and errors in `examples/10_tooling/trace32_tools/t32_cli/`. Reimplementing either model would
violate `REQ-UCLA-012` and create two parity problems.

The required change is therefore a grammar extraction plus thin source
adapters. There is no new service, plugin, registry framework, transport,
generic adapter trait, dependency, or persistence layer.

## Shared grammar

Simple may represent `AccessOperation` and `AccessOutputMode` as validated text
plus constants if that is the smallest language-compatible form. Their public
names and values are stable.

### `AccessCommandDescriptor`

| Field | Purpose |
|---|---|
| `name`, `subcommand` | CLI spelling; empty subcommand is valid |
| `operation: AccessOperation` | One of the six shared semantic classes |
| `handler_key` | Source-owned dispatch key; data only, never a function pointer |
| `usage`, `example`, `description` | One owner for help and operator guidance |
| `min_args` | Shared usage validation |
| `aliases` | Additive compatibility spellings such as existing WM commands |
| `safety: AccessSafety` | Machine-readable safety policy |

Source-specific commands remain legal. A T32-only command such as `cmm` stays
in the T32 catalog and is not forced into a false common operation. Only the
overlapping access commands use `AccessOperation`; their source catalogs may
carry additional private metadata.

### `AccessRequest`

`AccessRequest` is an ephemeral dispatch envelope, not a semantic query model.
It carries the selected descriptor, output mode, source/session scope,
correlation ID, bounded positional/options input, and requested timeout. The
source dispatcher translates it into existing `UiAccess*` or `WinText*`
requests. It is never persisted and never contains backend handles.

### `AccessResult`

`AccessResult` replaces the presentation-only role of `T32BridgeResult`. It
contains:

- schema version, operation, source/session scope, snapshot revision, and
  correlation ID;
- presentation kind (`scalar`, `table`, `kv`, `list`, `raw`, or `document`), title,
  scalar/list/table/key-value cells;
- count and truncation metadata;
- an optional machine payload produced by the existing canonical
  `UiAccessSnapshot`/`WinTextSnapshot` serializer.

`raw` preserves TRACE32 text capture compatibility but is always escaped inside
JSON; it is not a bypass around the machine envelope. The result does not own
semantic nodes or windows. Common conversion helpers derive
human cells and the machine payload from the same snapshot/result so human and
JSON modes cannot silently disagree. `document` is used for a full canonical
snapshot; it is not a raw-output escape hatch.

### `AccessError`

`AccessError` contains `code`, `message`, optional `source_code`, optional
`hint`, and `retryable`. The common stable codes are:

`source_unavailable`, `interaction_required`, `permission_denied`,
`unsupported_action`, `target_not_found`, `stale_target`, `target_disabled`,
`target_busy`, `timeout`, and `invalid_argument`.

Adapters map native failures once at their boundary. Existing T32 codes such as
`T4030` and `T4070` remain visible as `source_code`, preserving diagnostics and
compatibility while giving UI, WM, and T32 the same machine code. Success exits
`0`; usage/schema failures exit `2`; runtime failures exit `1`. JSON failures
emit one versioned `AccessError` envelope to stdout and diagnostics only to
stderr.

### `AccessSafety`

`AccessSafety` contains `read_only`, `destructive`, `idempotent`,
`requires_confirmation`, `may_prompt`, and `timeout_ms`. The descriptor is
declarative; enforcement is mandatory at dispatch. `list`, `snapshot`,
`surface`, `find`, and `history` are read-only. `act` is capability-checked and
may require confirmation. Common code never grants confirmation and never
falls back to raw keyboard/pointer input.

## Shared operation mapping

| Operation | TRACE32 | `simple ui` | host WM / `simple play` |
|---|---|---|---|
| `list` | `windows` | `windows` | existing `wm-list` plus additive `windows` spelling |
| `snapshot` | `window show` / capture | `snapshot` | `wm-text-snapshot` |
| `surface` | `window describe` | `surface` | top-level window description only |
| `find` | captured/catalog semantic find | `find` | `wm-text-find`, top-level only |
| `act` | action/field bridge | `act` | `wm-text-act`, supported adapter actions only |
| `history` | `history` | `history` | correlated access history |

TRACE32 catalog listing is not misreported as live OS enumeration. The result
identifies source and capture state explicitly. Duplicate TRACE32 names and WM
titles are labels, never identities.

## Normalized window list

No `AccessWindow` model is added. A common projector reads each
`UiAccessSurface` and its root `UiAccessNode` properties and emits the required
list columns in deterministic `(source_id, session_id, surface_id)` order:
stable ID, title, owner/application, surface kind, state, geometry,
focus/visibility, parent identity, capabilities, revision/time, and staleness.
Missing values are JSON `null` and `-` in human output; they are never guessed.

The host WM adapter converts its private `WindowInfo` records into
`UiAccessSurface`/root `UiAccessNode` values before calling common projectors.
`src/lib/common/ui/win_text_access.spl` must stop importing
`std.nogc_sync_mut.play.types.WindowInfo`. The same ownership rule applies to
TRACE32 catalog/capture records and compositor records.

## Runtime flow

```text
argv
  -> source command catalog (shared descriptors for overlapping commands)
  -> common parse/validate/safety/output-mode helpers
  -> AccessRequest
  -> source dispatcher
       -> UI: local HTTP facade -> existing /api/test/ui/* -> live UISession
       -> WM: live play.wm adapter -> common surface/node values
       -> T32: existing catalog/remote/capture/action owners
  -> common query or pre-action validation
  -> source-owned execution when mutating
  -> refresh/observe once + correlated bounded history
  -> AccessResult or AccessError
  -> common human or JSON renderer
```

`simple ui` is a separate process and therefore never pretends to hold the
running application's `UISession`. Its live adapter calls the existing test API
mounted by GUI/web and TUI-web hosts, defaulting to loopback and the configured
port with one bounded request per read. `act` uses one POST plus the one
post-action surface/history observation required by the contract. The adapter
uses the existing HTTP/client facade; it adds no raw runtime calls or transport.

When `--ui-access-db` is explicitly selected and no live service is available,
the existing access store may reconstruct list/snapshot/surface/find/history as
captured read-only state. It reports capture time/staleness and rejects `act` as
`source_unavailable`; a database write is not an action transport. Native TUI
without a mounted test API is therefore read-only through this fallback. The
live TUI system fixture uses the existing TUI-web/test-API host.

Action dispatch always obtains a current source revision, re-resolves the
canonical target, checks advertised action, enabled/busy/defunct state, input
bounds, confirmation policy, and timeout, then invokes exactly one owner
adapter. A removed or generation-reused target fails before execution.

History uses the existing `UiAccessEvent` sequence and the existing maximum of
64. Correlation ID and normalized error/result code are encoded in event
payloads; no parallel history record is introduced. Each action records a
request and result even on failure.

## Module and MDSOC boundaries

```text
src/lib/common/ui/
  access_cli_grammar.spl   data grammar, validation, errors, rendering
  access_types.spl         unchanged semantic UI records
  access_query.spl         existing query/serialization owner
  win_text_access.spl      existing source envelope; no host backend import

examples/10_tooling/trace32_tools/t32_cli/  catalog/remote/capture/action adapter
src/app/ui/                deployed UI CLI and local test-API client adapter
src/app/ui.test_api/       existing live UISession service (unchanged contract)
src/app/play/ + play.wm    host WM CLI and platform adapter
```

This cross-cuts three applications, but a virtual capsule or feature transform
would add machinery without removing coupling. Use ordinary data composition:
common owns the leaf grammar and each sibling imports downward. No sibling may
import another sibling's bridge, catalog, renderer, or backend-private type.
No inheritance or runtime registration framework is needed.

## Startup and entry closures

- `src/app/ui/cli_entry.spl` parses access commands before renderer/backend
  modes and imports only the common grammar plus the UI access client adapter.
- `src/app/ui/access_cli.spl` maps shared operations to the existing local
  `/api/test/ui/*` routes and optionally reads the existing access store for
  stale-aware read-only fallback.
- The T32 CLI keeps its existing entrypoint and unique commands; overlapping
  descriptors/results/errors/rendering migrate to the common grammar.
- `src/app/play/main.spl` keeps existing spellings and changes planned WM
  branches to live adapter calls.
- Production wrappers continue to launch cached compiled artifacts.

Startup loads static descriptors only. It must not enumerate windows, capture
UI, open a database, contact TRACE32, spawn a subprocess, or initialize a GUI
renderer merely to print help. Entry-closure checks must prove UI access does
not pull T32 or host-WM implementation modules, T32 does not pull UI renderers,
and WM does not pull UI/T32 adapters. The UI access command closure may import
the existing HTTP/client and persisted-store facades, but not a UI renderer.

## Renderer and IR boundary

Protocol v1 access remains semantic and renderer-independent: it exposes
`UiAccessSnapshot`/WinText identities, never WebIR/DrawIR objects, backend
handles, or readback state. Any future Protocol v2 render inspection must reuse
stable component IDs and the existing `simple-draw-ir-v2` owners under the
canonical [Draw IR P5/P6 plan](../03_plan/ui/rendering/draw_ir_multibackend_plan.md),
including its web fold-in; this feature must not create a parallel IR.

## Hot paths, cache, and invalidation

- `list` refreshes once per source, then normalizes and sorts in memory; never
  refresh once per window.
- `snapshot` refreshes once; `surface` and `find` operate on that bounded current
  snapshot unless explicit freshness requires one source refresh.
- `act` re-resolves once, executes once, invalidates only its source/surface,
  then refreshes or observes once for history evidence.
- `history` reads the bounded existing ring/store and performs no refresh.
- No hot operation scans the filesystem, reparses source, sleeps/retries in a
  loop, or shells out per node/window.

Snapshot revision plus source/session generation invalidates identities.
Mutating actions invalidate the affected snapshot. Source disconnect or
permission changes invalidate the source cache and return a typed error rather
than an empty successful result.

## Performance and observability

On the selected 100-window/1,000-node warm fixture:

- list/snapshot p95 <= 100 ms;
- cached find and common pre-adapter action routing p95 <= 20 ms;
- access CLI overhead <= 20 MiB maximum RSS;
- history remains <= 64 events.

Perf evidence records cold/warm state, source/backend, fixture cardinality,
p50/p95, max RSS, semantic count/checksum, refresh count, and subprocess count.
Debug diagnostics may report parse, refresh, normalize/query, adapter, render,
and total durations to stderr; JSON stdout stays uncontaminated.

## Compatibility and migration

1. Introduce the common grammar and parity tests without changing command
   spellings or output semantics.
2. Alias `T32BridgeResult` to the shared superset `AccessResult` so existing
   bridge constructors keep working, and map text/T-codes to `AccessError` at
   the T32 CLI boundary. Expose overlapping T32 GUI commands as shared
   `AccessCommandDescriptor` records while retaining the source catalog for
   T32-only commands. Compatibility aliases contain no second behavior.
3. Preserve T32-only commands, T-codes, help aliases, and source-specific
   execution.
4. Add UI commands without changing existing GUI/TUI/render modes.
5. Make existing WM commands live and add only the symmetric aliases selected
   by requirements.
6. Additive JSON fields remain optional within protocol version 1; changed
   meaning/type requires a major version.

## Rejected alternatives

| Alternative | Reason rejected |
|---|---|
| New UI/WM CLI snapshot types | Duplicates `UiAccessSnapshot`/`WinTextSnapshot` and query/action rules |
| Put adapters behind one generic trait/registry | No runtime plugin need; plain source dispatch is smaller and keeps ownership visible |
| Reuse `T32BridgeResult` from the T32 CLI module directly | Creates an upward sibling dependency and keeps the grammar T32-owned |
| Move WM backend records into common | Leaks mutable platform implementation into the dependency-light entry closure |
| Infer actions or fall back to raw input | Violates capability and safety requirements |
| Canonicalize signed JSON bytes | No signing/hash requirement; deterministic arrays and semantic JSON are sufficient |
| MDSOC virtual capsule/feature weaving | Static shared data plus adapters already provides the needed separation |

## Requirement traceability

| Architecture evidence | Requirements |
|---|---|
| Shared grammar and operation mapping | REQ-UCLA-001..004, REQ-UCLA-024, AC-UCLA-08 |
| Live UI transport and read-only fallback | REQ-UCLA-025, AC-UCLA-09, NFR-UCLA-022 |
| Existing semantic models and normalized projector | REQ-UCLA-005..008, REQ-UCLA-012..015 |
| Re-resolve/safety/action/history flow | REQ-UCLA-009..011, NFR-UCLA-004, NFR-UCLA-006..010 |
| Result/error/output contract | REQ-UCLA-016..019, NFR-UCLA-012..014 |
| Evidence, gate, and review obligations | REQ-UCLA-020..023, NFR-UCLA-018..020 |
| Startup/entry closure and dependency rules | NFR-UCLA-015..017, NFR-UCLA-021 |
| Hot-path/cache/observability budgets | NFR-UCLA-001..005 |
| Compatibility migration | NFR-UCLA-011..014 |

## Implementation invariants

- There is exactly one definition of each shared grammar type.
- UI and WM do not define CLI-specific snapshot/query/action/history records.
- Common UI imports no host-WM or TRACE32 backend type.
- Every advertised action is checked against current state and executed only by
  its owner adapter.
- Machine output is one versioned UTF-8 payload; diagnostics use stderr.
- Empty, unavailable, stale, unsupported, and interaction-required states stay
  distinguishable.
- T32, UI, and WM parity evidence compares descriptors, normalized results,
  errors, output modes, and safety metadata for overlapping operations.
