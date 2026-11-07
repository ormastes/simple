# Host preparation replay correctness

This is a corrective slice of the user-authorized HOST-02/ORCH-02 local host execution lane; no additional product options are introduced.

- HOST-REPLAY-01: An exact live admitted preparation may be retried without another reservation, journal event, or capacity charge.
- HOST-REPLAY-02: Expired, consumed, released, uncertain or continuity-unproven preparation must never be returned as newly prepared. Stale boot/provider fences must reject. Rejection must preserve journal revision and existing capacity accounting.

Implementation: `src/lib/nogc_sync_mut/orchestration/host_capacity_owner_v1.spl`.
Verification: `test/03_system/app/orchestrator/feature/host_prepare_replay_spec.spl` and its real-journal native fixture. Execution status is recorded separately; authored coverage is not passing evidence.
