<!-- codex-design -->
# Office CLI/TUI UI Access System-Test Plan

## Status and Requirement Source

Designed for explicitly selected option F1 and profile N1. The concurrent
requirements lane owns the final requirement files. The labels below mirror
that selected contract and the frozen user interface.

## Requirement Labels

| ID | Contract |
|---|---|
| REQ-OFFICE-CLI-UI-001..003,012 | Phase-3 build produces standalone `office calc [FILE] --tui`; optional `simple office` delegates to its cache; IDE checks remain separate; invalid arguments fail |
| REQ-OFFICE-CLI-UI-004..006 | Calc exposes `main` through windows/snapshot/surface/find/act/history with stable IDs, revisions, value actions, post-state, and correlated history |
| REQ-OFFICE-CLI-UI-007..008 | Real Calc entry produces A1=6, A2=8, B1=`=A1*A2`=>48, and C1=`=AVG(A1:A2)`=>7 |
| REQ-OFFICE-CLI-UI-009..011 | Retained TUI/protocol evidence, generated operator manual, and production isolation are verified by the evidence, isolation, and manual gates |
| NFR-OFFICE-CLI-UI-001 | `OFFICE_BINARY` is a Phase-3-built native product distinct from `SIMPLE_TEST_DRIVER`/UI client, with no full-CLI, raw-source, or seed launch fallback |
| NFR-OFFICE-CLI-UI-002..005 | Deployed startup/query/action/RSS/history limits hold on the measurement fixture |
| NFR-OFFICE-CLI-UI-006..010 | Deterministic evidence, restoration, hygiene, verification, and manual quality hold |

## Scope

Included:

- standalone Office artifact launch plus separate IDE diagnostic routing;
- real Calc TUI/controller and canonical UI access service;
- stable semantic IDs and value-bearing actions;
- multiplication and `AVG` through the live sheet;
- independent post-action snapshot and history;
- deterministic ANSI/text capture;
- N1 performance/provenance/isolation gates.

Excluded:

- redesigning other Office app surfaces;
- cross-platform PTY qualification beyond the primary N1 host;
- GUI pixel parity;
- general Excel compatibility beyond the selected witness;
- SGTTI in the production closure.

## Environment

- `OFFICE_BINARY` names the Phase-3-built standalone product under test.
- `SIMPLE_TEST_DRIVER` names the existing tool that executes SSpec/check
  orchestration; it is not the Office product or an application dependency.
- `SIMPLE_UI_CLIENT` names a cached `simple.access/v1` client artifact when the
  test driver does not provide that client directly.
- `SIMPLE_LIB=src` is allowed for test module resolution, not production
  source-entry fallback.
- Loopback UI access service and an available primary-host PTY are required.
- The gate uses a fixed 124x37 terminal and an isolated fixture/artifact root.
- Stale evidence, persisted-store act, raw-source dispatch, using the test driver
  as the Office process, and seed/full-CLI product fallback fail.

## Manual Flow and Capture Policy

The inline SSpec setup scenario `has one fresh deployed Office evidence run`
invokes `--scenario all` once for one unique run ID. Every displayed or folded
scenario expands that setup with `@prev(...)` and consumes the same fresh run
directory through `setup_office_cli_tui_ui_access` and `check_office_gate`; none
launches a second gate or reads the shared legacy evidence root.

Primary visible scenario:

1. Full deployed Calc discovery/action/history/formula flow — `exec`, `tui`,
   `protocol`, and `artifact`.

Folded scenarios:

- seed and stale-evidence rejection, legacy/invalid CLI behavior, and
  stale/missing/unsupported semantic actions;
- startup/query/action/RSS/history bounds, deterministic capture, provenance,
  restoration, architecture hygiene, and manual-quality gates.

Evidence display is `embed_tui`. Protocol, gate, and performance receipts
remain links. Executable SSpec stays folded beneath manual steps.

## Scenario Matrix

| Executable scenario (one shared gate run) | Visibility | Requirement | Happy/edge/error | Evidence |
|---|---|---|---|---|
| live semantic formula workflow | show | REQ-001..010 | happy/compatibility | exec+tui+protocol+artifact |
| fail-closed commands and actions | folded | REQ-011..012; NFR-001,007,008 | edge/error/isolation | exec+protocol |
| bounded deterministic N1 evidence | folded | NFR-002..006,009,010 | NFR/artifact | exec+protocol+artifact |

The deployed gate internally exercises CLI compatibility, discovery, formulas,
rejections, history eviction, performance, provenance, and PTY cleanup. The
SSpec scenarios organize that one run for the operator manual; they are not
separate gate selectors.

## Frozen Manual Steps

- Launch Calc through the standalone Office artifact
- List active Office windows
- Capture the Calc semantic snapshot
- Inspect the main Calc surface
- Find the active cell and formula input
- Enter source values through semantic actions
- Enter multiplication through the formula input
- Enter AVG through the formula input
- Review the independent post-action snapshot
- Review correlated access history
- Capture the rendered Calc TUI

## Assertions

The system gate must prove:

- command ownership/help is present and the app gate names its runtime;
- IDE TUI/GUI feature reports exit zero and name the correct mode;
- Office help contains `calc [FILE] --tui`;
- `main`, `main#cell_A1`, `main#formula_input`, and
  `main#confirm_edit` are present and the retained frame is 124x37;
- the found target, acted target, and history target are identical;
- stale revision and missing/unsupported actions fail without state mutation;
- B1 visibly and semantically equals `48`;
- C1 visibly and semantically equals `7`, while its raw formula is
  `=AVG(A1:A2)`;
- TUI capture and all protocol files share the current run ID;
- terminal mode is restored and the child/service is stopped.

## N1 Pass Criteria

```text
warm_calc_ready_ms <= 2000
windows_snapshot_p95_ms <= 100
find_p95_ms <= 25
action_observed_p95_ms <= 250
access_rss_delta_mib <= 20
history_limit = 64
capture = 124x37
```

## Execution Order

1. Implementation owner completes production command/controller/protocol work
   and the check gate.
2. Run the focused spec once:

   `OFFICE_BINARY="$PWD/bin/office" SIMPLE_TEST_DRIVER="$PWD/bin/simple" SIMPLE_UI_CLIENT="$PWD/bin/simple" SIMPLE_LIB=src bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --mode=interpreter`

3. If the spec executes rather than failing to compile or resolve symbols,
   generate its manual:

   `bin/simple spipe-docgen test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --output doc/06_spec --no-index`

4. Review the generated manual for `0 stubs`, visible primary flow, folded
   executable source, and current evidence links.
5. Run the UI evidence audit once after adding this spec/manual pair.
6. Confirm `find doc/06_spec -name '*_spec.spl' | wc -l` is `0`.

Do not generate or hand-edit the `doc/06_spec` manual while the executable spec
or gate cannot run.

## Traceability

| Requirement | Executable spec | Scenarios | Generated manual |
|---|---|---|---|
| REQ-001..010 | `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl` | live semantic formula workflow | `doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md` after fresh docgen |
| REQ-011..012 | same | fail-closed commands and actions | same |
| NFR-001,007,008 | same | fail-closed commands and actions | same |
| NFR-002..006,009,010 | same | bounded deterministic N1 evidence | same |

## Failure Triage

- Missing `OFFICE_BINARY`: build the narrow Office entry with the existing
  Phase-3 compiler; do not bootstrap the full CLI.
- Missing `SIMPLE_TEST_DRIVER`/`SIMPLE_UI_CLIENT`: provide the existing test
  orchestration/client artifacts without substituting them for Office.
- Gate nonzero: inspect the named scenario and `gate.out` receipt.
- Source unavailable: confirm Calc started the established loopback service.
- Missing target: inspect `protocol/snapshot-before.json` and stable IDs.
- Formula mismatch: inspect actions, post-snapshot, and raw formula.
- Capture mismatch: reject stale run IDs before changing assertions.
- Performance miss: retain measurements and record/fix a concrete regression;
  do not increase thresholds silently.
