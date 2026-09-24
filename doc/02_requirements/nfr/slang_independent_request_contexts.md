# Slang independent request-context NFRs

Date: 2026-09-08. Status: selected S3 ownership contract.

- NFR-001: Default request admission is conservative and independently configurable.
- NFR-002: Request count, snapshot bytes, and total process RSS are distinct gauges.
- NFR-003: No raw pointer crosses the int64 SFFI boundary.
- NFR-004: Every terminal/error path is idempotent and leak-free under ASan.
- NFR-005: Handle validation and request-table lookup are bounded constant time.
- NFR-006: Cache lookup remains bounded by eight entries until an indexed page store exists.
- NFR-007: Live evidence records per-context RSS and isolated/interleaved output parity.
