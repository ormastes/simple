# UI SSPEC Evidence Audit Design

## Overview

`ui_sspec_evidence_audit_spec.spl` is a lightweight system audit that reads the
repository as evidence. It does not replace the UI behavior specs; it verifies
that the UI behavior specs and generated manuals remain wired into the SPipe
manual/evidence lane.

## Evidence Model

- Executable specs live under `test/03_system/app/**/feature/*_spec.spl`.
- Generated manuals live under the mirrored `doc/06_spec/03_system/app/**`
  path.
- UI evidence is proven by source markers such as `ui_access_snapshot`,
  `/api/test/draw-ir`, `SgttiTestDriver`, `# @evidence-display`, and
  `**TUI Captures:**`.

## Failure Modes

- A missing manual returns `missing`.
- A generated stub or truncated manual returns `short`.
- A manual without source traceability returns `untraced`.
- A spec missing its expected UI evidence marker returns `absent`.

The spec uses only `std.spec` plus runtime file/process externs, keeping the
audit independent of UI implementation modules.
