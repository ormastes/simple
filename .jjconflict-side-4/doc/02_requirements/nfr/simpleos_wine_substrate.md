<!-- codex-design -->

# NFR Requirements: SimpleOS Wine Substrate

Date: 2026-05-06

## NFR-001: Staged Safety

No Wine or PE execution may run arbitrary guest code until process isolation, VM permissions, and fault handling are verified.

## NFR-002: Observability

Every substrate layer must expose structured trace markers for capability state, process/thread lifecycle, VM mappings, faults, IPC waits, renderer events, and PE loader decisions.

## NFR-003: Compatibility Without Hiding Native Design

SimpleOS must keep async-first and capability-based internals. POSIX/Wine shapes must be adapters over native services, and host waits plus file/network I/O must reuse `nogc_async_mut` / `nogc_async_mut_noalloc` primitives instead of introducing a second async runtime.

## NFR-004: Testability

Each requirement must have a unit/spec gate plus at least one integration or QEMU evidence gate before moving to the next stage.

## NFR-005: Performance Budgets

- Renderer damage-to-present p95: under 16 ms on the QEMU desktop smoke scene.
- VM map/protect/unmap operation p95: under 1 ms for small ranges after initialization.
- Process launch from filesystem to first userspace instruction: under 250 ms in QEMU smoke.
- PE parser for a small `hello.exe`: under 10 ms after file bytes are available.

## NFR-006: No Fake Compatibility

No resident fallback, no no-op pthreads, no no-op dynamic loading, and no success result for unsupported PE features. Unsupported work must return structured errors.
