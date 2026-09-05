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
office calc [FILE] --tui
simple office ... -> optional cached-artifact delegate
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
per SSpec process. The inline `has one fresh deployed Office evidence run`
scenario exposes it to docgen, and the visible primary plus folded error/NFR
scenarios expand it through `@prev(...)` and consume only that returned root.

Manual step names are frozen in
`doc/03_plan/sys_test/office_cli_tui_ui_access.md`.

## Work Breakdown

| Lane | Owner scope | Deliverable | Dependency |
|---|---|---|---|
| F1/N1 design+SSpec | this Codex lane | architecture, TUI/detail design, plans, executable spec | none |
| Standalone artifact | production implementation owner | Phase-3 build of `src/app/office_cli/main.spl`, direct launch, help/errors, narrow closure | design |
| Optional compatibility | production implementation owner | `simple office` delegates to cached Office artifact without source execution | standalone artifact |
| Formula | production implementation owner | pure `AVG -> AVERAGE` alias plus unit regression | design |
| Calc controller/UI | production implementation owner | loaded-sheet/session/controller, one normal TUI model, full 20x30 live tree | CLI + design |
| Access action | production implementation owner | value-bearing safe act input and correlated history | controller |
| System gate | production/test implementation owner | separate `OFFICE_BINARY` product, `SIMPLE_TEST_DRIVER`, cached UI client, PTY/protocol/perf gate with unique run ID | all production lanes |
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

The executable spec calls a real check gate. Missing Office artifact, test
driver, UI client, or gate,
nonzero gate exit, missing marker, missing artifact, stale run ID, source
fallback, Rust seed, or unresolved command must call `fail(...)` or produce a
real failed expectation. Silent no-op helpers, `pass_todo`, and
`expect(true).to_equal(true)` are forbidden.

## Handoff Checklist

- [x] Phase-3 build produces a standalone Office artifact without a full CLI bootstrap. — verified scripts/check/build-office-standalone-target.shs:5 `never invokes bootstrap` (requires `SIMPLE_TARGET_PHASE3`, :46) building src/app/office_cli/main.spl:25 `fn main`
- [ ] `office` owns Calc arguments; optional `simple office` only delegates to its cache.
  - status 2026-09-05: standalone half done (`src/app/office_cli/main.spl:25` routes `calc` to `run_calc_cli`); `simple office calc --tui` still runs `run_calc_session_host` / `run_calc_access_server` in-process (`src/app/office/mod.spl:880-883`), no cached-artifact delegation.
- [ ] Preferred and compatibility routes use one Calc model.
  - status 2026-09-05: standalone route uses `CalcTuiState` (`calc_tui_host.spl:11 calc_tui_new`); `simple office` route uses `calc_session_host.spl`, which does not reference `calc_tui` — still two models.
- [x] All 20x30 cells are live semantic targets. — verified src/app/office/sheets/sheets_app.spl:41 `visible_rows: 30` / :42 `visible_cols: 20`; src/app/office/sheets/access_controller.spl:700 `calc_cell_view_items` (full visible grid); gate asserts `main#cell_T30` at scripts/check/check-office-cli-tui-ui-access.spl:516-520
- [ ] Formula multiplication and AVG pass through deployed UI actions.
- [ ] Independent post-state and correlated history pass live.
- [ ] Current actual PTY ANSI/text/protocol evidence is retained.
- [ ] N1 startup/query/action/RSS/history bounds pass on `OFFICE_BINARY`.
- [ ] Production closure excludes compiler, unified CLI, SGTTI, and raw-source fallback.
- [x] Focused SSpec invokes the gate before docgen. — verified test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl:196 `setup_office_cli_tui_ui_access` (`process_run(gate_binary, ["--scenario", "all", "--run-id", run_id])`, fails closed on missing `OFFICE_GATE_BINARY`) and :234 `check_office_gate`
- [x] Generated manual reports `0 stubs` and requirement-specific evidence. — verified `src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl` -> `checkbox: Generated manual reports \`0 stubs\` and requirement-specific evidence` PASS (12 examples, 9 failures), after regenerating `doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md` with docgen `0 stubs` and per-scenario `_Requirements: \`REQ-OFFICE-CLI-UI-001\` ... \`REQ-OFFICE-CLI-UI-010\`_
- [ ] UI evidence uses the canonical manual path.

Gate script (pure Simple, not `.shs`): `scripts/check/check-office-cli-tui-ui-access.spl`
(`OFFICE_BINARY` :56, RSS bound :31/:274, startup bound :339, history correlation :424-480,
PTY capture `tui/calc-after.ansi` :228). The runtime-outcome boxes above ("pass live",
"pass on `OFFICE_BINARY`", evidence retained) stay open until a gate run is recorded.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
