# Lifecycle cache teardown

Executable owner: `test/01_unit/compiler/loader/lifecycle_cache_teardown_spec.spl`.

The scenario inserts one orphaned SMF reference into a fresh lifecycle manager,
checks a tracked count and dictionary length of one, destroys the lifecycle with
an empty executable mapper, and checks both counts become zero. This exercises
the canonical force-clear path even when no module can trigger normal unloading.
It makes no claim about mapped native resources.

Evidence and producer/import limitations:
`doc/08_tracking/bug/phase1_lifecycle_cache_teardown_owner_2026-10-11.md`.
Only the exact source-body projection passed (1/1 bootstrap diagnostic).
The normal imported current-source regression and admitted production gates
remain unverified.
