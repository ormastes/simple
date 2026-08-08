<!-- codex-design -->
# Office CLI/TUI UI Access System-Test Plan

## Status and Requirement Source

Designed for explicitly selected option F1 and profile N1. The concurrent
requirements lane owns the final requirement files. The labels below mirror
that selected contract and the frozen user interface.

## Requirement Labels

| ID | Contract |
|---|---|
| REQ-OFFICE-CLI-UI-001..003,012 | Deployed IDE/Office CLI owns its options, exposes `office calc [FILE] --tui`, preserves compatibility, and fails invalid arguments |
| REQ-OFFICE-CLI-UI-004..006 | Calc exposes `main` through windows/snapshot/surface/find/act/history with stable IDs, revisions, value actions, post-state, and correlated history |
| REQ-OFFICE-CLI-UI-007..008 | Real Calc entry produces A1=6, A2=8, B1=`=A1*A2`=>48, and C1=`=AVG(A1:A2)`=>7 |
| REQ-OFFICE-CLI-UI-009..011 | Retained TUI/protocol evidence, generated operator manual, and production isolation are verified by the evidence, isolation, and manual gates |
| NFR-OFFICE-CLI-UI-001 | Deterministic 124x37 TUI, protocol, exec, and log artifacts are current and reviewable |
| NFR-OFFICE-CLI-UI-002 | N1 latency/RSS/history limits, terminal cleanup, self-hosted provenance, and SGTTI isolation hold |

## Scope

Included:

- deployed `simple office` and `simple ide` dispatch;
- real Calc TUI/controller and canonical UI access service;
- stable semantic IDs and value-bearing actions;
- multiplication and `AVG` through the live sheet;
- independent post-action snapshot and history;
- XLSX save/reopen;
- deterministic ANSI/text capture;
- N1 performance/provenance/isolation gates.

Excluded:

- redesigning other Office app surfaces;
- cross-platform PTY qualification beyond the primary N1 host;
- GUI pixel parity;
- general Excel compatibility beyond the selected witness;
- SGTTI in the production closure.

## Environment

- `SIMPLE_BINARY` must name the verified pure-Simple self-hosted binary.
- `SIMPLE_LIB=src` is allowed for test module resolution, not production
  source-entry fallback.
- Loopback UI access service and an available primary-host PTY are required.
- The gate uses a fixed 124x37 terminal and an isolated fixture/artifact root.
- Rust seed, stale evidence, persisted-store act, and source fallback fail.

## Manual Flow and Capture Policy

Primary visible scenarios:

1. CLI contract and IDE feature checks — `exec`.
2. Full Calc discovery/action/history flow — `tui` plus `protocol`.
3. Multiplication and AVG live results — `tui`, `protocol`, and `artifact`.

Folded scenarios:

- legacy/invalid CLI behavior;
- semantic action/history details;
- stale/missing/unsupported rejection;
- invalid formula;
- evidence freshness;
- performance/provenance/SGTTI isolation.

Evidence display is `embed_tui`. Protocol, XLSX, logs, and performance receipts
remain links. Executable SSpec stays folded beneath manual steps.

## Scenario Matrix

| Gate scenario | Visibility | Requirement | Happy/edge/error | Evidence |
|---|---|---|---|---|
| `cli-help` | show | REQ-001 | happy | exec |
| `cli-ide` | folded | REQ-001 | edge/compat | exec |
| `cli-invalid` | folded | REQ-001 | error | exec |
| `ui-discovery` | show | REQ-002 | happy | protocol+tui |
| `ui-action-history` | folded | REQ-002 | edge/state | protocol |
| `ui-rejection` | folded | REQ-002 | error | protocol |
| `formula-multiply` | show | REQ-003 | happy | tui+protocol |
| `formula-avg` | show | REQ-003 | compatibility edge | tui+protocol+XLSX |
| `formula-invalid` | folded | REQ-003 | error | protocol+tui |
| `evidence` | folded | NFR-001 | artifact/freshness | all |
| `performance` | folded | NFR-002 | N1 targets | perf+log |
| `isolation` | folded | NFR-002 | provenance/cleanup | exec+log |

REQ-001, REQ-002, and REQ-003 each have happy, edge, and error coverage.
NFRs use aggregate evidence gates rather than synthetic placeholder scenarios.

## Frozen Manual Steps

- Launch Calc through the deployed Office command
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
- Save and reopen the XLSX artifact

## Assertions

The system gate must prove:

- command path/provenance names the deployed self-hosted runtime;
- IDE TUI/GUI feature reports exit zero and name the correct mode;
- Office help contains `calc [FILE] --tui`;
- `main`, `main#cell_A1`, `main#formula_input`, and
  `main#confirm_edit` are present and the retained frame is 124x37;
- the found target, acted target, and history target are identical;
- stale revision and missing/unsupported actions fail without state mutation;
- B1 visibly and semantically equals `48`;
- C1 visibly and semantically equals `7`, while its raw formula is
  `=AVG(A1:A2)`;
- saved/reopened XLSX preserves both results;
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

   `SIMPLE_BINARY="$PWD/bin/simple" SIMPLE_LIB=src bin/simple test test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl --mode=interpreter`

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
| REQ-001 | `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl` | cli-help, cli-ide, cli-invalid | `doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md` |
| REQ-002 | same | ui-discovery, ui-action-history, ui-rejection | same |
| REQ-003 | same | formula-multiply, formula-avg, formula-invalid | same |
| NFR-001 | same | evidence | same |
| NFR-002 | same | performance, isolation | same |

## Failure Triage

- Missing `SIMPLE_BINARY`: deploy/identify the verified self-hosted binary.
- Gate nonzero: inspect the named scenario and `log/calc-service.log`.
- Source unavailable: confirm Calc started the established loopback service.
- Missing target: inspect `protocol/snapshot-before.json` and stable IDs.
- Formula mismatch: inspect actions, post-snapshot, raw formula, and XLSX reopen.
- Capture mismatch: reject stale run IDs before changing assertions.
- Performance miss: retain measurements and record/fix a concrete regression;
  do not increase thresholds silently.
