# Borrowing Specification

Reference Capabilities and Borrowing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Management |
| Status | In Progress |
| Source | `test/feature/usage/borrowing_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Reference Capabilities and Borrowing Specification

**Feature:** Borrowing and reference capabilities system
Tests for the borrowing system including mutable (mut T), isolated (iso T),
and immutable reference capabilities. Verifies proper ownership transfer,
mutable access restrictions, and isolation guarantees.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/borrowing/result.json` |

## Scenarios

- allows multiple immutable borrows
- prevents simultaneous immutable and mutable borrows
- ensures exclusive access to isolated values
- transfers ownership correctly through function calls
