# Low Dependency UI dynSMF NFR Requirements

Date: 2026-06-05

## Selection

Selected NFRs: NFR-A plus NFR-B.

Startup/RSS budgets from NFR-C are deferred until after the first thin slice.

## Requirements

NFR-001: Static dependency gate is deterministic

The dependency gate must parse `use` statements, resolve module prefixes
deterministically, and report stable violation paths.

NFR-002: Dependency gate ignores external code

Dependency scans must ignore vendored/external paths defined by repository
policy, including compiler/runtime vendor trees.

NFR-003: Runtime dynSMF evidence is inspectable

dynSMF session operations must emit evidence rows for load, skip, unload, stale
lookup, and reload actions. Evidence must include library id, policy source,
status, handle, generation, and reason where applicable.

NFR-004: Interpreter tests avoid process-global env mutation

dynSMF policy must be constructible in tests without mutating process-global
environment variables.

NFR-005: Existing dynlib behavior remains compatible

The selected dynSMF session layer must preserve existing registry close/refcount
behavior and existing dynlib facade behavior.

NFR-006: Generated spec layout stays clean

Executable `.spl` specs must remain under `test/`; generated/manual docs belong
under `doc/06_spec`. The command
`find doc/06_spec -name '*_spec.spl' | wc -l` must print `0`.

