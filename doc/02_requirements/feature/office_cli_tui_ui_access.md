# Office CLI and Calc TUI UI Access Requirements

Selected feature option: **F1 — Calc-First Shared UI Controller**.

## Goal

Provide deployed, discoverable IDE/Office CLI entry points and a real Calc TUI
that human debuggers and LLM operators can inspect and edit through the existing
`simple.access/v1` UI protocol.

## Functional Requirements

### REQ-OFFICE-CLI-UI-001 — Deployed command ownership

The deployed CLI shall route `simple ide` and `simple office` to startup-light
command-owner entry points before global option filtering consumes
command-specific mode flags. It shall not execute raw `.spl` source or fall back
to the Rust seed in the production command path.

### REQ-OFFICE-CLI-UI-002 — IDE feature-check routing

`simple ide --feature-check --tui` and
`simple ide --feature-check --gui` shall reach the existing IDE feature-check
implementation and return deterministic mode-appropriate output.

### REQ-OFFICE-CLI-UI-003 — Calc launch grammar

The preferred command shall be:

```text
simple office calc [FILE] --tui
```

When `FILE` is omitted, Calc shall create a new in-memory workbook suitable for
editing. Existing `sheets` and `edit-sheet FILE --tui` routes shall remain
compatible.

### REQ-OFFICE-CLI-UI-004 — Canonical semantic surface

A launched Calc TUI shall expose one canonical `main` surface through the
existing `simple ui windows`, `snapshot`, `surface`, `find`, `act`, and
`history` operations. No Office-specific parallel protocol is permitted.

### REQ-OFFICE-CLI-UI-005 — Stable editable nodes

The Calc surface shall expose stable cell nodes such as `main#cell_A1`, an
editable `main#formula_input`, and `main#confirm_edit`. Selection, focus,
formula value, visible calculated value, and supported actions shall be
represented semantically rather than inferred from terminal coordinates.

### REQ-OFFICE-CLI-UI-006 — Value-bearing actions

The canonical UI action grammar shall support a value-bearing action such as
`type_text --value TEXT`. The Calc controller shall apply the action to the real
sheet model, rebuild its semantic tree, and record correlated request/result
history.

### REQ-OFFICE-CLI-UI-007 — Real multiplication

Entering `A1=6`, `A2=8`, and `B1= A1*A2` through the Calc UI shall use the real
formula evaluator and expose the calculated value `48` in the TUI and an
independent post-action semantic snapshot.

### REQ-OFFICE-CLI-UI-008 — AVG compatibility function

The formula evaluator shall recognize `AVG(...)` as a pure compatibility alias
of `AVERAGE(...)`. Entering `C1=AVG(A1:A2)` with `A1=6` and `A2=8` shall expose
the calculated value `7`.

### REQ-OFFICE-CLI-UI-009 — Real TUI evidence

The authoritative system scenario shall launch the deployed Calc command in a
terminal-compatible environment, retain its ANSI/text screen capture, drive
the semantic discovery/action/history flow, and assert the independently
observed formula results.

### REQ-OFFICE-CLI-UI-010 — Operator manual

The executable SSpec shall generate a readable mirrored manual with imperative
steps, requirement traceability, typed TUI/protocol/artifact captures, folded
edge/error scenarios, troubleshooting guidance, and zero docgen stubs.

### REQ-OFFICE-CLI-UI-011 — Production isolation

The normal IDE/Office/Calc production closure shall not import SGTTI or
test-only capture modules. Debug access shall use the existing opt-in access
service/store boundary.

### REQ-OFFICE-CLI-UI-012 — Compatibility and diagnostics

Unknown app/mode/action combinations shall return deterministic diagnostics and
non-zero status. Existing documented Office aliases shall retain their behavior.

## Exclusions

- Full semantic editing for every Office application in this feature.
- Microsoft Excel automation or proprietary rendering parity.
- GUI pixel-parity work beyond the requested Calc TUI evidence.
- A new Office-only UI automation protocol.
- Release, version bump, commit, tag, or push.
