# Caret Workbench UI Research — TLDR

Evidence table (plan §1.1), blockers (§1.2), competitive research (§2) and references (§16).

- Re-verified 2026-11-14 against `origin/release/1.0.0` @ `e3b68584142`.
- Confirmed: byte-sliced `_put_str`, `MANAGED_PROVIDER = "process"`, pane/manager identity gap, `--tui` ignoring `--profile`, `Ctrl+B` smux prefix.
- Changed: smux owner bug is rated P2; smux gained `runtime_binding_*_v3` files.
- Could not verify: extension v2 absence, keybinding reservations, trace P0/P1 wording, Slop qualification.
- Proposed plan, not a release-readiness certificate.

```text
 plan 52caab0725c --> re-check @ e3b68584142
   confirmed | changed | could not verify
```

Full doc: [caret_workbench_ui_research_2026-11-14.md](caret_workbench_ui_research_2026-11-14.md)
Design: [../../../05_design/app/llm_caret/caret_workbench_ui.md](../../../05_design/app/llm_caret/caret_workbench_ui.md)
Requirements: [../../../02_requirements/app/llm_caret/caret_workbench_ui.md](../../../02_requirements/app/llm_caret/caret_workbench_ui.md)
Plan: [../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md](../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)
