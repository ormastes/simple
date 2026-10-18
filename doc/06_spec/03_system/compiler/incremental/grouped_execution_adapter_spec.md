# Grouped execution authority adapter

REQ-IM-007. Executable: `test/03_system/compiler/incremental/grouped_execution_adapter_spec.spl`.
Status: authored, runtime/docgen UNRUN. Existing native
`test/fixtures/bootstrap_builder/grouped_manager_main.spl` remains an independent
consumer and is not claimed as executed.

## Admission and ownership

Create two independent SCC actions and one dependent action using the actual
coordinator, service and bridge. Verify two ready bindings and typed absent
dispatch slots. Reject an undeclared worker, duplicate action claim, occupied
worker and dependency-blocked claim. The original input retains absent dispatches.

## Recovery preserves peer work

Claim A and B, complete B, then submit a parent-verified reap DTO fixture for A.
Require exactly the next generation while B remains completed in both owners.
Reject A's original result and a third attempt. Admit the second attempt's
failure with no CAS publication, release its memory reservation and keep its
dependent action blocked. Reject duplicate final delivery.

## Receipt negatives

Vary group, action, worker, generation, lease, snapshot, cache and proof digest
independently. Every rejected recovery must retain the current service generation
and coordinator reservation. Same-generation recovery must also fail.

## Publication boundary and configuration

Reject package archive results from an intermediate parse action without
changing its lease or publication list. Reject incomplete binding coverage,
duplicate worker slots and a zero retry budget during admission.

## Evidence limits

All tests use production transition functions. Reap values are explicit DTO
fixtures, not evidence of a live process death. The production runner must obtain
them from its existing broker collector or verified journal replay. Full OS
retirement, process identity, journal crash tests and compilation remain unrun.
