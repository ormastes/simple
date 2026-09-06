# DevHub terminal/UI system-test plan

## Requirements

- REQ-DEVHUB-TERM-001: `bin/devhub` must select a runtime that can execute the
  DevHub source entrypoint rather than merely answer an identity probe;
  terminal help, version, and error exits must come from DevHub itself; and the
  global `--tui` surface prefix must preserve successful command dispatch.

## Offline process matrix

The executable specification at
`test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl` runs only local
help, version, invalid-command, GUI-document, launch-option, and invalid-port
cases. It does not read backend credentials or access Jira, GitHub, Bitbucket,
Confluence, MinIO, or mail services.

## Acceptance

All nine cases must be discovered by the SSpec runner and pass in
interpreter mode. The terminal must also be exercised directly with
`bin/devhub --help`, `bin/devhub --tui --help`, and `bin/devhub --version`.

## Modern SSpec and evidence policy

The primary TUI scenario is visible in the generated manual. Each scenario
uses explicit `step("...")` flow labels and canonical matchers. The TUI help
transcript is captured at
`build/test-artifacts/03_system/app/devhub/feature/devhub_terminal_ui/help_tui.txt`
and embedded by the mirrored manual; executable source remains folded detail.
The actual Electron window screenshot is retained at
`doc/06_spec/image/03_system/app/devhub/feature/devhub_terminal_ui/devhub_gui.png`.

## Traceability

| Requirement | Executable spec | Generated manual | Scenarios | Coverage |
|---|---|---|---:|---|
| REQ-DEVHUB-TERM-001 | `test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl` | `doc/06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md` | 9 | help, TUI, version, error, GUI document, clickable actions, shell options, port guard, quiet/verbose diagnostics |
