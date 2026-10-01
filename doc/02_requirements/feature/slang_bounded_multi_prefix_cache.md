# Slang bounded serial multi-prefix cache requirements

Date: 2026-09-08. Status: selected S2 precursor from the user-approved SPipe +
Slang implementation contract, refined by Astra architecture review.

- REQ-001: Retain up to a configured positive entry count and total byte limit.
- REQ-002: Zero capacity disables retention without disabling generation.
- REQ-003: Select the longest complete exact-token prefix; mismatches cold-start.
- REQ-004: Use deterministic LRU eviction and refresh recency on hit/admission.
- REQ-005: Include serialized state and token identity in retained-byte accounting.
- REQ-006: Reject an oversized candidate before allocation and keep generation valid.
- REQ-007: Recompute one matched boundary token and preserve request isolation.
- REQ-008: Expose admissions, evictions, rejected candidate bytes, restore failures, resident
  entries, and resident bytes without breaking an S1-only backend library.
- REQ-009: Teardown releases every entry and resets gauges and counters.
- REQ-010: Remain serial and snapshot-based; do not advertise paged KV,
  concurrent contexts, persistence, spill, or distributed transport.
