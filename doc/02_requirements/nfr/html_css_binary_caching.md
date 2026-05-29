<!-- codex-research -->

# HTML/CSS Binary Caching NFR

- NFR-HCBC-001: Cache metadata helpers shall stay inside the shared web render API and shall not add new native, network, TLS, package, compression, or GUI toolkit dependencies to renderer startup.
- NFR-HCBC-002: Cache classification shall be deterministic and testable in unit tests.
- NFR-HCBC-003: GTK comparison shall be reproducible from one script under `scripts/`, with generated artifacts placed under `build/` and reports under `doc/09_report/`.
- NFR-HCBC-004: First-milestone checks shall include parser/type checking for changed shared API and targeted unit coverage for cache key, static/dynamic classification, and IPC HTML reuse.
- NFR-HCBC-005: Performance reports shall clearly distinguish measured values from unavailable host capabilities.
