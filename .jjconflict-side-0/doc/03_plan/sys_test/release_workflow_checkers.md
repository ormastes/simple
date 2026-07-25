# Release Workflow Checker Test Plan

## Scope

Restore the four checker entrypoints already called by release workflows
without restoring deleted implementation dependencies.

| Requirement | Executable evidence | Pass condition |
|---|---|---|
| REL-CHECK-001 | `release_checker_contract_test.shs`, `release_checker_contract_spec.spl` | named runtime/archive roles enforce distinct size budgets, stripped release executables, and missing-file policy |
| REL-CHECK-002 | same pair | directory and tar payloads require notices; font tampering, multiple roots, unsafe paths, and escaping links fail |
| REL-CHECK-003 | same pair | smoke/full select canonical SimpleOS scenarios without a second QEMU implementation |
| REL-CHECK-004 | same pair | MCP metadata matches package identity; tagged payload checksum passes; the named native binary is staged |

Manual: `doc/06_spec/01_unit/scripts/release_checker_contract_spec.md`.
The focused shell test uses tiny local fixtures, a fake Simple CLI, and an
offline MCP release archive; live QEMU and GitHub release lookup remain workflow
evidence.
