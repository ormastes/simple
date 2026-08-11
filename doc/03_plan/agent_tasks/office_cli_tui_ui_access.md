<!-- codex-design -->
# Office CLI/TUI UI Access Agent Tasks

## Corrective Lane (2026-08-08)

Feature F1 and NFR N1 are not complete. An independent audit found a split
small/full Calc TUI, a five-cell live UI tree, and an SSpec that read stale
evidence instead of executing its gate. This plan preserves unrelated dirty
work and assigns the corrective ownership needed for genuine acceptance.

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

SSpec helper names (implemented and shared by every scenario):

- `setup_office_cli_tui_ui_access`
- `check_office_gate`

`setup_office_cli_tui_ui_access` invokes the unique-run `all` gate at most once
per SSpec process. The visible primary scenario and folded error/NFR scenarios
consume only that returned run root.

Manual step names are frozen in
`doc/03_plan/sys_test/office_cli_tui_ui_access.md`.

## Work Breakdown

| Lane | Owner scope | Deliverable | Dependency |
|---|---|---|---|
| F1/N1 design+SSpec | this Codex lane | architecture, TUI/detail design, plans, executable spec | none |
| Unified CLI | production implementation owner | startup-light IDE/Office dispatch and help/errors | design |
| Formula | production implementation owner | pure `AVG -> AVERAGE` alias plus unit regression | design |
| Calc controller/UI | production implementation owner | loaded-sheet/session/controller, one normal TUI model, full 20x30 live tree | CLI + design |
| Access action | production implementation owner | value-bearing safe act input and correlated history | controller |
| System gate | production/test implementation owner | deployed self-hosted process/PTy/protocol/perf gate with unique run ID | all production lanes |
| Manual/evidence audit | merge owner after runnable PASS | generated manual, diagram update, evidence audit registration | executable spec PASS |
| Verification | final reviewer | focused tests, audits, N1 evidence, no SGTTI/source fallback | merged implementation |

## Sidecar Lanes

- `office_spipe_docs_audit`: manual-first SSpec, plans, guide, skill, and stale
  generated-manual audit/correction.
- `office_spipe_gate_audit`: deployed PTY/protocol/provenance/N1 gate audit and
  fail-closed evidence hardening.
- `office_spipe_impl_audit`: production CLI/Calc/session closure audit and
  opt-in access-transport ownership split.

All sidecars worked against frozen command, canonical-ID, helper, and manual
step names. `/root` remains merge owner and performs the final
highest-capability requirement-by-requirement review.

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

- [ ] CLI owns `--tui|--gui` without raw-source dispatch.
- [ ] Preferred and compatibility routes use one Calc model.
- [ ] All 20x30 cells are live semantic targets.
- [ ] Formula multiplication and AVG pass through deployed UI actions.
- [ ] Independent post-state and correlated history pass live.
- [ ] Current actual PTY ANSI/text/protocol evidence is retained.
- [ ] N1 startup/query/action/RSS/history bounds pass on a deployed runtime.
- [ ] Production closure excludes SGTTI and raw-source fallback.
- [ ] Focused SSpec invokes the gate before docgen.
- [ ] Generated manual reports `0 stubs` and requirement-specific evidence.
- [ ] UI evidence uses the canonical manual path.
