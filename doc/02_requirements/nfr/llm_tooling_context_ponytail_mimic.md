# NFR Requirements: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

Selected option: Option A, Small Local Tooling NFRs.

## Final Targets

- NFR-001: Public context output shall not contain the internal absence marker.
- NFR-002: The first slice shall avoid new raw runtime shortcuts and use the
  existing CLI/file helper seam.
- NFR-003: The scoped implementation shall compile with the release Simple
  binary.
- NFR-004: Unit coverage shall include markdown, text, JSON, stats, and missing
  file output.
- NFR-005: `doc/06_spec` shall contain only generated/manual markdown docs, not
  executable `.spl` specs.
- NFR-006: Local index/query helpers shall stay pure Simple over existing file
  helper seams and avoid daemon state or new raw runtime shortcuts.
- NFR-007: SQL-backed context helpers shall use the existing Simple SQLite
  facade and owner interpreter extern module instead of adding app-level raw
  runtime shortcuts.
- NFR-008: SQL-backed context output shall preserve the public absence policy:
  explicit statuses and content text, never the internal absence marker.
