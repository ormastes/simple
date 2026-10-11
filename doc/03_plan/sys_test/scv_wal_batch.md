# SCV batch acceptance evidence

Spec: test/02_integration/app/scv_metadata_batch_spec.spl. Eight authored cases.
REQ-008: exact unsaved two-row replay, failed append publication, checkpoint
failure counters, rejection of a torn suffix. REQ-014: all-row preflight and
one serialized-owner batch path. REQ-024: empty batch, payload/cardinality
bounds and multiline/key rejection.

Required execution: qualified full pure-Simple CLI/TestRunner on the recorded
source and runtime provider. Run the spec once; record actual registered and
executed cases, pass/fail/skip counts and producer/runtime hashes. Interpret
and both native backends for aggregate owner semantics where supported.
Measure realistic equal workloads: row-at-a-time vs insert_batch, cold/warm
wall time, RSS, WAL reads/writes/syncs and database receiver copies.

Pending fault matrix: concurrent handles, owner death/requeue, checkpoint
crash boundaries, strict corrupt-prefix replay, reopen counter monotonicity,
schema-v2 idempotent migration, durability across power loss and missing CAS.
These required items are not implied by the eight batch scenarios.
