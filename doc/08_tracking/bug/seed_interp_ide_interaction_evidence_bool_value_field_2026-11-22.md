# Phase 1 seed interpreter: `text?` call fails with "undefined field 'value' on bool" in IDE evidence spec (2026-11-22)

Status: OPEN (compiler defect; Phase 1 seed `ac2e90625c2a`). No source workaround applied.

## Symptom

`test/03_system/app/ide/feature/ide_interaction_evidence_spec.spl` (run or test, Phase 1):

```
semantic: .../ide_interaction_evidence_spec.spl:76:13: undefined field 'value':
cannot access field on value of type 'bool'
```

Line 76 is `val component = launcher_action_to_component("open_sheets")`
(`src/app/office/launcher.spl:32`, returns `text?`).

## Reduction so far

- The same call in a fresh spec/`main` with the same import list passes
  (`comp=sheets`, 2/2 examples).
- Renaming the local to `launcher_component` does not help.
- Truncating the scenario after line 75 and calling it as `val lc = ...` still fails at that
  line, so the failure depends on the state built by the preceding statements
  (`ide_interaction_evidence`, `build_launcher_ui`, `ui_access_snapshot_from_state`,
  `ui_access_find_nodes`), not on the call alone.

## Unblock condition

Reduce to a minimal repro against the seed interpreter, fix in
`src/compiler_rust` (or the pure-Simple interpreter), and re-run the spec with the next
compiler generation. The spec itself is correct and stays RED.
