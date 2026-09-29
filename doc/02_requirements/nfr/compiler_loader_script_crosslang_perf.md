# Compiler, loader, script, and cross-language performance NFRs

Selection: retained NFR contract (bounded Build9 tranche).

- NFR-001: Retained rows record raw wall samples, p50/p95, maximum RSS, executable/compiler identity, requested/actual mode, fallback, exit status, and checksum.
- NFR-002: No row is admitted from a Rust bootstrap seed, stale wrapper, or fallback execution.
- NFR-003: Native packed-byte rows reject maximum process RSS above four times the requested payload and retain the measured limit/reason.
- NFR-004: Every benchmark subprocess is bounded by the configured timeout; failures do not become timing values.
- NFR-005: Loader cache claims remain limited to executable repeated-miss/caller/reset counters until a canonical filesystem-probe counter exists; no syscall reduction is claimed here.
- NFR-006: The tranche preserves the existing resolver, packed-byte, and runtime ownership boundaries and introduces no parallel implementation path.
- NFR-007: Retained byte RSS admission is Linux-only and fail-closed: GNU `/usr/bin/time` and `timeout` must be present; GNU time's `%M` receipt over the bounded command must include a known allocating child, with no PID polling or unbounded fallback. Unsupported hosts are unavailable.
- NFR-008: Byte fixture timing uses the fixture's integer `elapsed_ms` receipt for the 1 MiB `<1000 ms` and 32 MiB `<30000 ms` targets; host wall p50/p95 remains a separate retained-report measure.
