<!-- codex-design -->
# Office CLI/TUI UI Access Agent Tasks

## Completed Lane

Feature F1 and NFR N1. Research and final requirement documents are owned by
their concurrent lane and are not edited here. This plan preserves unrelated
dirty work and assigns ownership by file/module lane.

## Frozen Shared Interfaces

Command/protocol:

```text
simple office calc [FILE] --tui
simple ide --feature-check --tui|--gui
windows -> snapshot -> surface -> find -> act -> history
```

Canonical identities:

```text
main
main#cell_A1
main#formula_input
main#confirm_edit
```

Formula witness:

```text
A1=6
A2=8
B1==A1*A2 -> 48
C1==AVG(A1:A2) -> 7
```

SSpec helper names:

- `setup_office_cli_tui_ui_access`
- `check_office_gate`

Manual step names are frozen in
`doc/03_plan/sys_test/office_cli_tui_ui_access.md`.

## Work Breakdown

| Lane | Owner scope | Deliverable | Dependency |
|---|---|---|---|
| F1/N1 design+SSpec | this Codex lane | architecture, TUI/detail design, plans, executable spec | none |
| Unified CLI | production implementation owner | startup-light IDE/Office dispatch and help/errors | design |
| Formula | production implementation owner | pure `AVG -> AVERAGE` alias plus unit regression | design |
| Calc controller/UI | production implementation owner | sheet/session/controller, stable nodes, real TUI reuse | CLI + design |
| Access action | production implementation owner | value-bearing safe act input and correlated history | controller |
| System gate | production/test implementation owner | deployed process/PTy/protocol/perf evidence gate | all production lanes |
| Manual/evidence audit | merge owner after runnable PASS | generated manual, diagram update, evidence audit registration | executable spec PASS |
| Verification | final reviewer | focused tests, audits, N1 evidence, no SGTTI/source fallback | merged implementation |

## Sidecar Lanes

Lower-model sidecars: N/A. The feature is bounded and the shared command,
identity, helper, manual-step, and evidence contracts are already frozen by the
highest-capability design pass. Additional speculative parallel generation
would increase collision risk in the dirty Office/CLI workspace.

## Merge and Review

- Merge owner: root agent for `office_cli_tui_ui_access`.
- Final reviewer: best available normal/highest-capability model.
- Design/SSpec lane must not edit production source.
- Production owners must not rewrite the research/options or design artifacts
  to hide an implementation mismatch; append reviewed changes instead.
- Generated manual owner runs docgen only after the spec executes with the
  production gate.

## Fail-Fast Contract

The executable spec calls a real check gate. Missing runtime, missing gate,
nonzero gate exit, missing marker, missing artifact, stale run ID, source
fallback, Rust seed, or unresolved command must call `fail(...)` or produce a
real failed expectation. Silent no-op helpers, `pass_todo`, and
`expect(true).to_equal(true)` are forbidden.

## Handoff Checklist

- [x] CLI owns `--tui|--gui` before global filtering.
- [x] Preferred and compatibility Office routes work.
- [x] Stable Calc nodes and value-bearing actions exist.
- [x] Formula multiplication and AVG witness pass.
- [x] Independent post-state and correlated history pass.
- [x] 124x37 text/ANSI/protocol evidence is current.
- [x] N1 startup/query/action/history bounds pass; app-development RSS is
  explicitly deferred to deployment measurement.
- [x] Production closure excludes SGTTI and raw source fallback.
- [x] Focused SSpec runs before docgen.
- [x] Generated manual reports `0 stubs`.
- [x] UI evidence uses the canonical manual path.
