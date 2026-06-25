<!-- codex-research -->
# NFR Requirements — Dashboard Crash Containment Framework

Date: 2026-04-03
Selection basis: explicit user direction in prompt

## Non-Functional Requirements

- NFR-RES-001: Default hosted interactive workloads shall cap memory at `8192 MB`.
- NFR-RES-002: Heavy compiler workloads may use up to `16384 MB`; heavy test/index workloads may use up to `12288 MB`.
- NFR-CPU-001: Default hosted interactive workloads shall use `floor(available_parallelism / 2)` with a floor of `1`.
- NFR-CPU-002: Heavy compiler workloads may use all available parallelism; batch indexers may use a capped high-water mark above half but below full machine saturation by default.
- NFR-REL-001: Crash containment shall be process-scoped for hosted apps and supervised-task scoped for system services.
- NFR-REL-002: The framework shall avoid in-process “resume as normal” semantics after invariant violation in kernel-resident or bare-metal domains.
- NFR-OBS-001: Crash classification shall preserve at least exit-code-based reason text for panic, trap, abort, signal, timeout, and resource-limit failure.
- NFR-OPS-001: Build, test, and system validation for this feature shall run in containers rather than directly on the host server.
