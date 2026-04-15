# Handle Pointers Specification

Handle pointers provide safe, reusable references to i64 values via a slot table with generation counters. Freed slots are reused, but stale handles are detected via generation mismatch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #820-825 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/handle_pointers_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Handle pointers provide safe, reusable references to i64 values via a slot
table with generation counters. Freed slots are reused, but stale handles
are detected via generation mismatch.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Handle | Index + generation pair for safe reference |
| Generation | Version counter incremented on free |
| Pool | Pre-allocated slot table with free list |
| Slot reuse | Freed indices are recycled |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/handle_pointers/result.json` |

## Scenarios

- creates handle for value
- dereferences handle
- validates live handle
- detects freed handle
- old handle invalid after slot reuse
- reuses freed slot index
- manages multiple concurrent handles
- returns -1 for freed handle
- second free returns false
