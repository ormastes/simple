# SFFI v2 Hardening — Non-Functional Requirements

**Status:** Selected and final for P0/P1

- **REQ-SFFI-V2-NFR-001 — Hot path:** A generated scalar or opaque-handle
  typed call shall perform no per-call hashing, signature verification, library
  search, symbol-name/map lookup, generic decoding, or wrapper allocation.
- **REQ-SFFI-V2-NFR-002 — Diagnostics:** Canonical SFFI failures shall have
  stable codes and include provider, symbol, lane, and safe hash prefixes while
  avoiding raw pointer disclosure by default.
- **REQ-SFFI-V2-NFR-003 — Parity:** Supported execution lanes shall agree on
  value/error category for every shared fixture; a lane-specific workaround is
  not conformance.
- **REQ-SFFI-V2-NFR-004 — Admission safety:** Provider metadata parsing shall
  be bounded and overflow-safe, and provider publication shall be atomic only
  after the complete required closure validates.
- **REQ-SFFI-V2-NFR-005 — Coverage:** New contract encoders, return validators,
  and lift logic shall reach at least 80% branch coverage with positive,
  negative, malformed, and sabotage controls.
- **REQ-SFFI-V2-NFR-006 — Native-first selection:** Before adding a foreign
  provider, implementation shall inventory `src/lib/**` and `src/os/**` for a
  pure-Simple counterpart and retain canonical no-GC sync extern ownership.

P4 signature/provenance latency, revocation, reproducibility, and trust-store
targets remain planned until the P4 requirement decision is separately frozen.

