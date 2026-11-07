# Linux native uname field decoding

Source: `test/01_unit/lib/nogc_sync_mut/sffi/linux_uname_v1_spec.spl`.

Status: **AUTHORED / UNEXECUTED / AWAITING_VERIFICATION**. This is a source
manual, not runtime-generated evidence or a passing test report.

1. Normalizes supported kernel architecture names without environment defaults.
2. Refuses foreign kernel names and unknown or malformed architecture values.

These two cases test the pure decoder only. The separately authored
`test/fixtures/orchestration/linux_container_native_identity_probe.spl` invokes
the actual Linux uname owner and remains unexecuted. No environment/shell or
compile-target architecture value substitutes for native observation.

See `doc/05_design/linux_simple_container_adapter_v2.md` for ABI provenance,
scope/continuity rules, trusted deadline boundary, and remaining verification.
