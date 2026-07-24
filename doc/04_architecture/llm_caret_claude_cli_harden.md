# LLM Caret Claude CLI Harden - Architecture

Date: 2026-07-05

## Decision

Treat `src/app/llm_caret` as one MDSOC+ app-layer provider caret. Claude CLI
feature migration lands through explicit provider modules and trace tables,
not by importing the full Claude CLI UI, remote bridge, or OAuth subsystem.

## Boundaries

- App provider caret: `src/app/llm_caret`.
- External comparison source: `tmp/claude/claude-code-main/src`.
- Verification: shell checker plus SSpec system gate.

## Invariants

- Provider source files must stay mapped to Claude source evidence or an
  explicit Simple-only extension role.
- File and LOC mapping coverage must remain at least 80%.
- Function, struct, and extern symbol trace coverage must remain complete.
- The default gate must be offline and deterministic.

## TUI Runtime Boundary (2026-07-24)

The shipped interactive loop is split across two app-layer capsules:

- `tui_io.spl` owns the `CaretIo` capability bundle and its production
  adapters to the canonical terminal and stdin owners.
- `chat_tui.spl` owns rendering, input reduction, session transitions, and
  lifecycle ordering. Tests inject a `CaretIo`; they do not copy this logic or
  declare private runtime externs.

Raw mode is acquired before alternate-screen or cursor mutation. Every modeled
exit restores cursor visibility, alternate-screen state, and raw mode in that
order. A raw-entry failure is returned as a typed loop result and becomes a
nonzero CLI exit. Frame rendering takes one terminal-size snapshot so a resize
cannot mix dimensions from two queries.

Hard panics and asynchronous signals remain below the app-layer capability
boundary: full restoration for those paths requires a runtime-owned
atexit/signal guard and must not be claimed from component tests.

## Claude-Full Feature-Gate Evidence Capsule (2026-07-24)

`claude_full/feature_gate_registry.spl` is an inward-only parts-bin capsule.
It imports pure leaf gate owners and projects their heterogeneous values into
`ClaudeFeatureGateRecord` plus condition probes. Exact production and focused
or aggregate system-test paths make feature-to-test ownership reviewable
without adding a second runtime dispatcher.

Dependency direction is system evidence → inward registry → leaf owner. The
`owner_spec` value is an inert repo-relative text path; production source does
not import `test/**`, and leaf owners do not depend back on the registry.

The capsule is intentionally not imported by `src/app/llm_caret/main.spl`,
the shipped command registry, or TUI dispatch. Root metadata is recorded only
where it is needed for reconciliation. In particular, `/compact` remains
enabled and visible in static root metadata while its leaf owner may disable
the descriptor from an environment-derived Boolean.

This bounded 33-record registry is supporting evidence for
`REQ-LLM-CARET-HIDDEN-008`. It does not prove shipped command admission,
current-upstream exhaustiveness, or discovery of future distributed gates.
Those claims remain owned by root/component/live-PTY evidence and by a restored
provenance-pinned upstream inventory respectively.
