# Delete/update conflict retention requires a durable oracle

Status: OPEN source gap; no runtime failure is claimed.

REQ-013 requires delete/update and incompatible scalar races to remain explicit conflicts. `db_reduce_operations_local` currently emits `SCVDB_TOMBSTONE_UPDATE` for updates against a tombstoned row, but does not emit a corresponding `DbConflictRecord`. `db_apply_local_transition` returns a conflict result without publishing when `plan.conflict_records` is empty. Scalar field races instead append durable catalog evidence.

The caller can observe a typed rejection and the tombstone remains unchanged. That alone does not establish durable conflict catalog retention across restart. The REQ-013 combined delete/update-and-scalar boundary system scenario remains fail-fast until its complete durable oracle exists; the new different-field and undeclared-schema scenarios do not close this gap.

A repair must define authenticated row-level conflict evidence and its supported reviewer decisions, retain original mutation/provenance without partial semantic acceptance, and cover both delete-before-update and update-before-delete with explicit preconditions. It must preserve tombstone/no-resurrection guarantees, replay/counter behavior, and paged/reference consistency. A caller-supplied conflict flag or synthesized scalar-field record must not stand in for the original operation. Add actual filesystem restart and signed reviewer tests before claiming completion.