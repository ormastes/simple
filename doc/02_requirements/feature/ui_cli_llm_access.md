<!-- codex-research -->
# UI CLI LLM Access — Feature Requirements

**Date:** 2026-07-11
**Status:** Selected requirements
**Selected options:** F1-A, F2-A, F3-A, F4-A, F5-A

## Scope

Extend the selected UI Access Protocol and WM Text Access contracts with live, T32-style CLI access. The CLI reuses `common.ui.access` and `common.ui.win_text_access`; it does not introduce a parallel UI model. Simple-owned GUI/TUI sessions expose the full semantic access loop, while host WM access covers top-level windows and only the actions already supported by its adapter.

## Functional Requirements

### CLI surface and compatibility

- REQ-UCLA-001: The deployed `simple ui` entry shall expose live `windows`, `snapshot`, `surface`, `find`, `act`, and `history` operations in addition to existing render/backend modes.
- REQ-UCLA-002: Existing `simple play wm-list` and `wm-text-snapshot|find|act` commands shall execute live adapters instead of returning planned-only output; any symmetric window-list spelling shall be additive, and existing spellings shall remain supported.
- REQ-UCLA-003: CLI help and the operator guide shall map T32 `windows`, window capture/describe, action, and history concepts to their Simple UI and WM equivalents, including intentional differences.

### Window listing and semantic inspection

- REQ-UCLA-004: UI and WM list operations shall emit the same normalized top-level window/surface schema and deterministic ordering.
- REQ-UCLA-005: Each record shall expose a source/session-scoped stable ID, title, owner/application, surface kind, state, geometry, focus/visibility, parent identity, capabilities, captured revision/time, and staleness when available; unavailable fields shall be explicit and shall never be fabricated.
- REQ-UCLA-006: UI snapshot and surface operations shall expose current GUI and TUI semantic trees through the existing `UiAccessSnapshot` model and canonical `surface_id#widget_id` identities.
- REQ-UCLA-007: Host WM operations shall expose top-level windows through the existing WinText envelope; internal controls remain unsupported unless a semantic adapter provides them.

### Find, act, and history

- REQ-UCLA-008: Find shall query a bounded current snapshot through the shared in-memory query owner and return canonical IDs suitable for later action.
- REQ-UCLA-009: Before acting, the system shall re-resolve the target against the current source/session revision, verify its advertised capability and enabled/busy/defunct state, then invoke the source-owned adapter.
- REQ-UCLA-010: Successful and failed actions shall append correlated request/result events to bounded history and refresh or observe the resulting UI state.
- REQ-UCLA-011: The CLI shall never silently replace a missing semantic action with lower-confidence raw pointer/keyboard input.

### Common-library ownership

- REQ-UCLA-012: `UiAccess*` and `WinText*` shall remain the only common access records; no CLI-specific parallel snapshot, query, action, or history model shall be introduced.
- REQ-UCLA-013: Normalization, selector/query behavior, deterministic ordering, serialization, error codes, action validation, and history rules shall have one common owner used by UI and WM frontends.
- REQ-UCLA-014: Live enumeration, capture, refresh, and action execution shall remain adapter-owned.
- REQ-UCLA-015: The common UI layer shall not import host-WM backend record types; the host adapter shall convert backend window records into common records unless design evidence proves a minimal neutral descriptor is shared by multiple adapters.

### Output and errors

- REQ-UCLA-016: Human-readable output shall be the default and `--json` shall emit exactly one versioned UTF-8 machine payload on standard output with deterministic array ordering.
- REQ-UCLA-017: List/snapshot output shall expose truncation or pagination metadata when bounds apply.
- REQ-UCLA-018: Usage/schema errors and runtime target/backend failures shall have stable nonzero exits and typed codes, including `source_unavailable`, `interaction_required`, `permission_denied`, `unsupported_action`, `target_not_found`, `stale_target`, `target_disabled`, `target_busy`, `timeout`, and `invalid_argument` where applicable.
- REQ-UCLA-019: Headless, unavailable-backend, stale-window, unsupported-rendering, and zero-window states shall be distinguishable and shall not crash or masquerade as successful populated results.

### Evidence and documentation

- REQ-UCLA-020: Focused unit/integration/system evidence shall cover live UI GUI/TUI discovery, live WM listing, stable identity and ordering, human/JSON output, find, safe UI actions, safe WM adapter actions, post-action history, and every required failure class.
- REQ-UCLA-021: A canonical `check-ui-cli-access` gate shall fail closed on common contract, CLI routing, UI/WM parity, schema, safety, action/history, or generated-manual regressions.
- REQ-UCLA-022: Architecture, GUI/TUI/CLI designs, detail design, system-test plan, executable SSpec, generated operator manual, agent task plan, and detailed LLM/operator guide shall remain traceable to these requirements.
- REQ-UCLA-023: Agent sidecar results shall be merged by the lane owner and the final architecture, implementation, evidence, generated manual, exclusions, and done claim shall receive explicit highest-capability review.
- REQ-UCLA-024: TRACE32 GUI access, Simple UI access, and WM access shall share one common architecture grammar for command descriptors, operation classes, structured results, stable errors, output modes, and safety metadata where semantics overlap; source-specific catalogs, captures, and action execution shall remain adapter-owned.
- REQ-UCLA-025: A separate `simple ui` CLI process shall reach a live GUI/TUI session through the existing `/api/test/ui/*` service using the configured local endpoint; an attached UI-access database may provide read-only list/snapshot/surface/find/history fallback, but shall never be presented as a live action transport.

## Acceptance Criteria

- AC-UCLA-01: A live GUI fixture and a live TUI fixture are listed, snapped, queried, safely acted upon, refreshed, and represented in correlated history through `simple ui`.
- AC-UCLA-02: A live host-WM fixture is listed through the existing play/WM CLI, produces the same normalized list fields/order rules as the UI list, and routes supported actions through its owner adapter.
- AC-UCLA-03: Repeated lists preserve scoped identities for unchanged windows; a removed/reused target fails as `stale_target` or `target_not_found` before action.
- AC-UCLA-04: Human and JSON modes agree semantically; JSON parses as one versioned payload and diagnostics do not contaminate its standard output.
- AC-UCLA-05: Unsupported, unavailable, interaction-required, disabled/busy, invalid, and timeout fixtures return distinct stable failures.
- AC-UCLA-06: Dependency and duplication evidence proves UI and WM frontends reuse common access/query/serialization/safety/history owners and that the common core no longer depends on the host-WM backend record.
- AC-UCLA-07: `check-ui-cli-access` passes once on the final implementation with real assertions and the generated manual reads as an operator workflow without opening the source spec.
- AC-UCLA-08: T32, UI, and WM commands are registered and rendered through the shared access grammar, and parity tests prove their overlapping list/capture-or-snapshot/find/act/history operations use the same descriptor/result/error rules without removing T32-specific commands.
- AC-UCLA-09: Live GUI and TUI-web fixtures are accessed from a separate CLI process over the existing test API; stopping that service produces `source_unavailable`, while database fallback remains readable and rejects `act` without mutating state.

## Out of Scope

- Replacing GUI/TUI renderers, the WM, or T32.
- Full UIA, AX, or AT-SPI descendant integration for arbitrary host applications.
- Pixel-perfect cross-backend equivalence beyond evidence already required by the selected UI protocol.
- Remote transport, authentication, packaging, or release.
