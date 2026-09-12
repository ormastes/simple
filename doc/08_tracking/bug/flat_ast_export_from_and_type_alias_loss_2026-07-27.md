# Flat AST loses export-from provenance and type aliases
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Observed

During the full Stage 4 CLI closure, `export X from module` retains only `X`;
the provider module is absent from `Module.exports`. Flat parsing also does not
dispatch `type Name = Target`, and module assembly hardcodes
`type_aliases: {}`.

This caused unresolved EasyFix facade types and `T32BridgeResult`.

## Current compatibility repair

Affected build-critical sources use supported `export use module.{...}` and
import alias syntax. This preserves their existing public names and targets.

## Required compiler fix

- Represent export provider modules in flat declarations and `Module.exports`.
- Add a flat type-alias declaration, parser dispatch, and module assembly.
- Resolve alias RHS ownership for type lowering and static member lookup.
- Add parser/HIR tests for generic and non-generic aliases and export-from.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
