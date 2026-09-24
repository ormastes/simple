# MDSOC++ IDE/Tooling Large-Program Pilot

## Purpose

This manual verifies the first concrete MDSOC++ large-program composition. It
uses the existing IDE/tooling responsibilities as independently owned capsules:
document snapshots, workspace model, language analysis and diagnostics, test
execution, editor shell, and an optional AI service.

## Operator Flow

1. Seal the local IDE graph without AI and confirm every required facet binds.
2. Confirm the absent optional AI facet does not make the graph incomplete.
3. Add AI with network authority and confirm its analysis and shell bindings.
4. Complete an analysis request through the existing tooling provider adapter.
5. Remove network authority and confirm admission fails at the AI capsule.
6. Reduce the measured memory budget by one byte and confirm fail-closed sealing.
7. Publish generation 11 with an additive document-state migration from 1.0 to 1.1.
8. Submit an inadmissible generation 11 and confirm generation 10 remains published.
9. Remove migration evidence or skip a generation and confirm rollback.

## Expected Composition

| Capsule | Provides | Requires |
|---|---|---|
| Document store | document snapshot | none |
| Workspace model | workspace model | document snapshot |
| Language analysis | analysis, diagnostics | document snapshot, workspace model |
| Test service | test execution | workspace model |
| Editor shell | editor surface | document, diagnostics, tests, optional AI |
| AI service (optional) | AI assistance | document snapshot, analysis |

Without AI, five capsules produce seven bindings. With admitted AI, six
capsules produce ten bindings. Startup follows provider-before-consumer order;
shutdown is its exact reverse.

## Failure Semantics

- Missing network authority returns `CapabilityDenied` for the AI slot.
- Insufficient aggregate memory returns `MemoryBudgetExceeded`.
- A document schema change without an exact migration edge returns
  `MigrationMissing` or `MigrationIncompatible`.
- A rejected candidate never replaces the active generation. Its upgrade
  receipt records candidate status, published generation, restored generation,
  both composition digests, and `rolled_back=true`.

## Executable Evidence

Run:

```text
bin/simple test test/03_system/app/mdsocpp/ide_tooling_large_program_pilot_spec.spl
```

The executable source is
`test/03_system/app/mdsocpp/ide_tooling_large_program_pilot_spec.spl`.
