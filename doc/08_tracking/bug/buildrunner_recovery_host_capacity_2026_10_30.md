# BuildRunner accepted overbooked recovery journals

Status: source fix and regression cases authored; runtime verification UNRUN.
Inspected base: `b622509b4daf41d6d8902fed695760975276258d`.

`task_runner_dispatch` enforces each host's declared slot limit. In contrast,
`task_runner_decode_v1` validated persisted host names and rebuilt active
reservation counts without checking that limit. A journal containing two
RUNNING rows for a one-slot host was therefore accepted, producing negative
free slots. REAPED and UNRESOLVED rows also become RUNNING during recovery.
The BuildRunner CLI trusts this decoded state before recovering child ownership.

The repair validates rebuilt active counts against every host's slots before
returning recovered state. It reuses the existing common scheduler/index;
there is no new invoker, container, journal schema or process-acceptance path.
Exactly-at-limit and independent-host recovery remain accepted. Pending or
terminal host labels do not reserve slots.

Tests were authored before the production edit:

- Unit: `test/01_unit/lib/common/task_runner/recovery_capacity_spec.spl`
  (four examples: overbooking, recovery-normalized leases, exact capacity,
  independent hosts).
- Integration: `test/02_integration/app/buildrunner/recovery_capacity_spec.spl`
  (two examples through the production BuildRunner adapter).
- Acceptance: `test/03_system/app/buildrunner/feature/recovery_capacity_spec.spl`
  (one file-backed CLI example: exit 2 before receipt-directory creation or
  process-port calls, with the original journal unchanged).

No compatible qualified Linux full CLI/test runner was available. These are
seven authored examples, not seven executed tests; behavioral RED/GREEN,
native child custody, required core/MCP checks and generated-manual validation
remain unverified. No bootstrap retry or push was performed. The earlier six
bootstrap repair cycles remain exhausted. Removing the new guard should make
the two invalid unit examples and invalid integration example fail; acceptance
should detect the pre-fix receipt-directory creation even when later ownership
recovery independently returns exit 2.

This bounded recovery repair does not complete the lockless-map/AsyncRef
adoption plan or remove monomorphization from that plan.
