<!-- codex-research -->
# NFR: Scheduler + Process Isolation

- NFR-SPI-001: Scheduler selection must avoid global queue contention as SMP support grows.
- NFR-SPI-002: Existing scheduler unit behavior must remain compatible unless explicitly superseded.
- NFR-SPI-003: Deadline scheduling must fail closed unless admission control accepts a valid runtime/period/deadline tuple.
- NFR-SPI-004: RT/deadline task validation must reject GC/allocation/unbounded-blocking effects.
- NFR-SPI-005: Process isolation metadata must be initialized at every task creation path.
