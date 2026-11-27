# Host preparation replay lifecycle

Status: **NOT_RUN**. This is an authored manual, not generated execution evidence.

Executable specification: `test/03_system/app/orchestrator/feature/host_prepare_replay_spec.spl`.
Real journal fixture: `test/fixtures/orchestration/host_prepare_replay_native_probe.spl`.

- HOST-REPLAY-01: A live admitted preparation replays without advancing the journal sequence.
- HOST-REPLAY-02: Exact-deadline expiry, lost continuity, stale boot/provider fences, aborted preparation, committed execution, and recovered unknown execution reject preparation replay.

Every rejection independently reads the durable journal through the original capability and checks retained state, envelope, outcome digest, and sequence. Expired and discontinuous reservations remain charged; execution and unknown execution remain charged; aborted capacity remains released.

One unadmitted native diagnostic build timed out at 240 seconds after 99 MIR modules passed; no executable was produced. Runtime, SSpec, provider, transport and system qualification remain NOT_RUN. Reviewed resource and daemon dependencies are present. Evidence: `doc/05_design/host_prepare_replay_verification.sdn`.
