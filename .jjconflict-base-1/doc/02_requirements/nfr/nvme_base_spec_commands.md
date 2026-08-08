# NVMe Base-Spec Command NFRs

- NFR-001: The system test must fail on a missing runtime, nonzero subprocess result, missing PASS marker, or any firmware FAIL marker.
- NFR-002: Evidence must run through the selected self-hosted Simple runtime, never the Rust seed.
- NFR-003: The executable SSpec must use real assertions and have a matching manual under `doc/06_spec`.

