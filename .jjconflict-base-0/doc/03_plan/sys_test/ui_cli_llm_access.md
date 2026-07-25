<!-- codex-design -->
# UI CLI LLM Access — System Test Plan

## Scope

The focused system lane proves the live T32-style LLM access loop for Simple
GUI/TUI and host-WM surfaces, including one shared grammar, normalized listing,
semantic inspection, safe action routing, correlated history, stable errors,
deterministic human/JSON output, bounded hot paths, compatibility, and evidence.

The shared grammar names are fixed: `AccessCommandDescriptor`,
`AccessOperation`, `AccessRequest`, `AccessResult`, `AccessError`,
`AccessSafety`, and `AccessOutputMode`. T32, UI, and WM must map overlapping
descriptor/operation/result/error/safety/output semantics through these records;
source catalogs, capture, refresh, and action execution remain adapter-owned.

Excluded: arbitrary host-application descendant accessibility, remote transport,
authentication, packaging/release, renderer replacement, and pixel-perfect
cross-backend equivalence.

## Executable Evidence

- Spec: `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl`
- Final review spec: `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_final_review_spec.spl`
- Generated manual: `doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.md`
- Final review manual: `doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_final_review_spec.md`
- Focused gate: `bin/simple run scripts/check/check-ui-cli-access.spl`
- Production execution: native/compiled SSpec mode; interpreter loading alone is
  not execution evidence.

The Pure Simple gate owns deterministic live fixtures and emits one compact
report per `--scenario`. A missing or failing gate is a hard scenario failure;
`setup_ui_cli_access` and `_check_gate` never accept planned or fabricated
output.

Run the primary spec once and save its transcript, then hash that evidence and
obtain the bound review receipt before running the final review spec once. This
two-phase split avoids rerunning already-green acceptance scenarios.

## Environment and Fixtures

- Warm Simple GUI fixture and TUI-web fixture, each mounting the existing test
  API and exposing one safe actionable node to a separate CLI process.
- Host WM fixture with supported top-level focus/move action and no fabricated
  descendant controls.
- TRACE32 descriptor catalog for compatibility/parity checks; no hardware action
  is required for tests that only prove grammar registration.
- Error fixtures for headless, unavailable backend, zero windows, permission,
  interaction, stale/reused ID, disabled, busy, unsupported action, invalid
  argument, and timeout states.
- Performance fixture: 100 windows/surfaces and 1,000 semantic nodes.
- Warm baseline and maximum-RSS measurement available on the same host/backend.

## Scenario Catalog

| ID | Scenario | Primary oracle |
|---|---|---|
| S01 | shared-grammar | Seven exact grammar records and T32/UI/WM parity mappings |
| S02 | t32-compatibility | T32-specific commands preserved; overlapping mappings pass |
| S03 | live-tui-loop | Live list/snapshot/find/act/refresh/history plus TUI capture |
| S04 | live-gui-loop | Live list/surface/find/act/refresh/history plus GUI capture |
| S05 | live-wm-loop | Normalized WM list and owner-adapter top-level action |
| S06 | identity-ordering-staleness | Stable scoped IDs, deterministic ordering, stale rejection |
| S07 | output-modes | Human/JSON semantic equality and clean versioned UTF-8 payload |
| S08 | error-taxonomy | Every required stable error and no raw/fabricated fallback |
| S09 | environment-states | Empty/headless/unavailable/unsupported states remain distinct |
| S10 | action-safety | Re-resolution, capability/state/input/timeout/confirmation rules |
| S11 | common-ownership | Common owners, adapter boundary, dependency/duplication guards |
| S12 | bounded-hot-paths | Bounds and scan/reparse/subprocess/retry/cached-wrapper guards |
| S13 | performance | p50/p95/RSS/fixture/checksum evidence against selected targets |
| S14 | compatibility-help | Deployed help/commands plus additive schema compatibility |
| S15 | live-ui-transport | Existing test API, loopback/timeout/request bounds, and read-only DB fallback |
| S16 | manual-evidence | Typed TUI/GUI/protocol captures and generated-manual quality |
| S17 | final | Canonical fail-closed aggregate and highest-capability acceptance |

## Traceability Matrix

Every requirement has happy-path, boundary/compatibility, and failure/gate
coverage across at least three focused scenarios.

| Requirement | Description | Test scenarios | Cases | Coverage |
|---|---|---|---:|---|
| REQ-UCLA-001 | Deployed `simple ui` operations | S03, S04, S14 | 3 | Full |
| REQ-UCLA-002 | Live existing WM commands | S05, S14, S16 | 3 | Full |
| REQ-UCLA-003 | Help maps T32 concepts/differences | S02, S14, S15 | 3 | Full |
| REQ-UCLA-004 | Shared normalized schema/order | S01, S05, S06 | 3 | Full |
| REQ-UCLA-005 | Complete explicit record metadata | S05, S06, S07 | 3 | Full |
| REQ-UCLA-006 | GUI/TUI semantic trees and IDs | S03, S04, S06 | 3 | Full |
| REQ-UCLA-007 | WM top-level-only WinText envelope | S01, S05, S11 | 3 | Full |
| REQ-UCLA-008 | Bounded shared find and canonical IDs | S03, S04, S12 | 3 | Full |
| REQ-UCLA-009 | Re-resolve and validate action | S05, S06, S10 | 3 | Full |
| REQ-UCLA-010 | Correlated history and refresh | S03, S04, S10 | 3 | Full |
| REQ-UCLA-011 | No raw-input fallback | S08, S10, S16 | 3 | Full |
| REQ-UCLA-012 | No CLI-specific parallel model | S01, S11, S16 | 3 | Full |
| REQ-UCLA-013 | One common behavior owner | S01, S11, S12 | 3 | Full |
| REQ-UCLA-014 | Live work remains adapter-owned | S03, S05, S11 | 3 | Full |
| REQ-UCLA-015 | Common excludes host backend types | S01, S11, S16 | 3 | Full |
| REQ-UCLA-016 | Human default and one JSON payload | S07, S14, S16 | 3 | Full |
| REQ-UCLA-017 | Truncation/pagination metadata | S06, S07, S12 | 3 | Full |
| REQ-UCLA-018 | Stable nonzero typed errors | S07, S08, S09 | 3 | Full |
| REQ-UCLA-019 | Environmental states distinguished | S08, S09, S16 | 3 | Full |
| REQ-UCLA-020 | Focused live evidence | S03, S04, S05 | 3 | Full |
| REQ-UCLA-021 | Canonical fail-closed gate | S11, S16, S17 | 3 | Full |
| REQ-UCLA-022 | Traceable design/manual/guide set | S14, S16, S17 | 3 | Full |
| REQ-UCLA-023 | Merged lanes and highest review | S11, S16, S17 | 3 | Full |
| REQ-UCLA-024 | Shared T32/UI/WM architecture grammar | S01, S02, S17 | 3 | Full |
| REQ-UCLA-025 | Live test-API transport and read-only DB fallback | S03, S04, S15 | 3 | Full |
| NFR-UCLA-001 | Warm list/snapshot p95 <= 100 ms | S12, S13, S17 | 3 | Full |
| NFR-UCLA-002 | Cached find/routing p95 <= 20 ms | S10, S12, S13 | 3 | Full |
| NFR-UCLA-003 | RSS delta <= 20 MiB | S12, S13, S17 | 3 | Full |
| NFR-UCLA-004 | Recent history bounded at 64 | S03, S10, S12 | 3 | Full |
| NFR-UCLA-005 | No hot-path scans/reparse/fanout | S11, S12, S13 | 3 | Full |
| NFR-UCLA-006 | Read operations declared read-only | S01, S10, S17 | 3 | Full |
| NFR-UCLA-007 | Complete action safety pipeline | S05, S06, S10 | 3 | Full |
| NFR-UCLA-008 | Explicit confirmation eligibility | S08, S10, S17 | 3 | Full |
| NFR-UCLA-009 | No semantic downgrade/fabrication | S08, S09, S10 | 3 | Full |
| NFR-UCLA-010 | Distinguishable failures | S08, S09, S17 | 3 | Full |
| NFR-UCLA-011 | Existing surfaces compatible | S02, S14, S17 | 3 | Full |
| NFR-UCLA-012 | Additive JSON schema evolution | S01, S07, S14 | 3 | Full |
| NFR-UCLA-013 | Deterministic strict UTF-8 JSON | S06, S07, S17 | 3 | Full |
| NFR-UCLA-014 | Clean stdout and stable exits | S07, S08, S14 | 3 | Full |
| NFR-UCLA-015 | Facades only; no runtime shortcut | S11, S12, S17 | 3 | Full |
| NFR-UCLA-016 | Cached compiled production wrapper | S12, S14, S17 | 3 | Full |
| NFR-UCLA-017 | No repeated scans/rereads/sleeps | S11, S12, S13 | 3 | Full |
| NFR-UCLA-018 | Reproducible perf evidence fields | S07, S13, S17 | 3 | Full |
| NFR-UCLA-019 | Real assertions, steps, captures | S03, S04, S16 | 3 | Full |
| NFR-UCLA-020 | One converged final verification | S14, S16, S17 | 3 | Full |
| NFR-UCLA-021 | Data-only dependency-light grammar | S01, S11, S12 | 3 | Full |
| NFR-UCLA-022 | Bounded loopback test-API calls via existing facade | S03, S04, S15 | 3 | Full |

## Manual Rendering and Capture Policy

- S03 and S04 are primary visible operator workflows; their seven canonical
  steps remain expanded.
- S05, S07, S08, S10, S14, and S15 remain visible as focused operational/error flows.
- S01, S02, S06, S09, S11-S13, S16, and S17 are folded detail/gate evidence.
- `# @evidence-display: embed_tui` embeds compact TUI captures. GUI screenshots
  and protocol/perf reports remain linked.
- Typed capture metadata is scenario-local: `tui` for textual rendering, `gui`
  for screenshots, and `protocol` for descriptors, JSON, history, errors, and
  gate reports.
- TUI path: `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui/`.
- Protocol path: `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/`.
- GUI path: `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/` (Git LFS).

## Execution and Pass/Fail

0. Build and run the two-module imported `Action(text)` native regression with
   the newly bootstrapped pure-Simple compiler; require exact `run` output.
   This compiler invariant must pass before collecting any live UI evidence.
1. Run focused unit/integration evidence owned by `check-ui-cli-access`, then
   collect live evidence in order: TUI, GUI, WM, and transport.
2. Run this SSpec in native/compiled mode once after implementation converges.
3. Generate the mirrored manual with `0 stubs`; inspect primary workflows and
   typed evidence once.
4. Run the UI SSpec evidence audit, direct runtime guards, dependency checks,
   and `find doc/06_spec -name '*_spec.spl'` layout guard through the aggregate.
5. Run S13 once on the representative warm fixture, then S17 once for final
   highest-capability acceptance. Do not repeat passing gates.

PASS requires every scenario report to contain `status=pass`, every traceability
row to remain covered, every required error to be distinct, performance targets
to be measured and met, generated-manual stubs to be zero, executable specs
under `doc/06_spec` to be zero, and final review to say `accepted`. Any missing
gate/helper, planned-only adapter, fabricated output, placeholder assertion,
schema divergence, raw-input fallback, stale action, dirty JSON stdout, missing
capture, or unmeasured NFR is FAIL.

## Risks

- Host WM availability is environmental; fixtures must prove both live and
  unavailable paths without weakening either assertion.
- TRACE32 names are non-unique and Z-order changes; scoped IDs and canonical
  sorting, not titles/Z-order, are the identity oracle.
- Screenshot evidence can pass while interaction is broken; S03-S05 require
  semantic query/action/history protocol evidence in addition to capture.
- A common module importing renderer/WM/T32 owners would defeat the requested
  layering even if CLI output looks correct; S01/S11/S12 enforce dependency
  direction.

## WebIR/DrawIR Refactoring Boundary

- UI access remains semantic-only: grammar, snapshots, queries, actions, and
  history must not import WebIR, DrawIR, Engine2D, or font-renderer owners.
- Track `src/app/ui.browser/backend.spl` widget-to-DrawIR duplication for the
  renderer optimization lane; converge it on `widget_tree_to_draw_ir` there.
- Treat the direct 8x16 text path in `window_scene_draw_ir.spl` as legacy
  compatibility until Engine2D `draw_text`/font parity evidence replaces it.
- Neither renderer debt blocks this access feature unless it crosses the
  semantic boundary; do not add a parallel IR/backend handle here.
