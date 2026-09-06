# Office plan-acceptance spec reads an evidence root the gate never writes

- date: 2026-09-06
- status: OPEN
- area: app/office, test/03_system/plan_acceptance

## Symptom

`test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl` computes its
evidence root as

    OFFICE_UI_BASE = "build/test-artifacts/03_system/plan_acceptance/office_cli_tui_ui_access/runs/"
    root           = OFFICE_UI_BASE + "handoff-plan-remains-" + SIMPLE_TEST_RUN_ID

and then reads `root + "/suite.txt"`, `root + "/protocol/*.json"`,
`root + "/tui/calc-after.{ansi,txt}"`, `root + "/perf/startup.txt"`.

The gate it invokes, `scripts/check/check-office-cli-tui-ui-access.spl`, writes
its receipts under a different base entirely
(`check-office-cli-tui-ui-access.spl:26,73-74`):

    EVIDENCE_BASE = "build/test-artifacts/03_system/app/office/feature/office_cli_tui_ui_access"
    _run_root(run_id) = EVIDENCE_BASE + "/runs/" + run_id

The gate takes only `--scenario` and `--run-id`; it has no way to be told a
different base. So even with `OFFICE_GATE_BINARY`, `OFFICE_BINARY` and
`SIMPLE_UI_CLIENT` all correctly configured and the gate exiting 0, the eight
receipt-reading scenarios read a directory that does not exist.

## Why it has not been noticed

All nine open scenarios currently fail earlier, in `setup_office_handoff_gate`,
because `OFFICE_GATE_BINARY` is unset in every default environment and no
compiled gate binary exists in the tree. The path mismatch is the *second*
blocker behind that one.

## Fix options (not applied — unverifiable while the gate cannot run)

1. Point the spec's `OFFICE_UI_BASE` at the gate's `EVIDENCE_BASE`. Locator
   plumbing only; changes no oracle.
2. Add an optional `--evidence-base` argument to the gate and have the spec pass
   its own base. Keeps the two suites' evidence trees disjoint.

Option 1 is smaller; option 2 is what the plan's "never read a shared or prior
evidence directory" wording argues for. Either must be validated by an actual
gate run, which needs an admitted Phase-3 compiler (`SIMPLE_TARGET_PHASE3`,
`scripts/check/build-office-standalone-target.shs:46`). No `build/**/stage3/**`
compiler exists in this tree, and producing one is a bootstrap.
