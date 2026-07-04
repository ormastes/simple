<!-- codex-research -->

# HTML/CSS Binary Caching NFR

- NFR-HCBC-001: Cache metadata helpers shall stay inside the shared web render API and shall not add new native, network, TLS, package, compression, or GUI toolkit dependencies to renderer startup.
- NFR-HCBC-002: Cache classification shall be deterministic and testable in unit tests.
- NFR-HCBC-003: GTK comparison shall be reproducible from one script under `scripts/`, with generated artifacts placed under `build/` and reports under `doc/09_report/`.
- NFR-HCBC-004: First-milestone checks shall include parser/type checking for changed shared API and targeted unit coverage for cache key, static/dynamic classification, and IPC HTML reuse.
- NFR-HCBC-005: Performance reports shall clearly distinguish measured values from unavailable host capabilities.
- NFR-HCBC-006: Persistent cache support shall be optional and shall not be imported by default web backend construction.
- NFR-HCBC-007: Hot static cache hits shall be separately measured from full software pixel rendering in the GTK comparison report.
- NFR-HCBC-008: Compact static-shell plan bytes shall be measured separately from full generated HTML bytes.
- NFR-HCBC-009: Prepared SWBC reuse timing shall be reported separately from disk-backed HTML cache timing.
- NFR-HCBC-010: Layout payload bytes shall be measured separately from encoded SWBC plan bytes and full generated HTML bytes.
- NFR-HCBC-011: Retained command payload bytes and command reuse counts shall be reported in the GTK comparison output.
