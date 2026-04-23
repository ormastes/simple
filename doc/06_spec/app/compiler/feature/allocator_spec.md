# Allocator Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/allocator_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/allocator/result.json` |

## Scenarios

- [slow] creates allocator with base and size
- [slow] allocates memory and returns address
- [slow] allocates multiple blocks sequentially
- [slow] aligns allocations to 8 bytes
- [slow] allocates with custom alignment
- [slow] adds padding for alignment
- [slow] returns 0 when out of memory
- [slow] tracks remaining space correctly
- [slow] resets allocator to empty state
- [slow] allows reuse after reset
- [slow] creates single large free block
- [slow] allocates from first suitable block
- [slow] splits large blocks
- [slow] uses entire block if no room to split
- [slow] marks block as free
- [slow] coalesces with next free block
- [slow] coalesces with previous free block
- [slow] resizes in place if possible
- [slow] allocates new block if growing
- [slow] handles alternating alloc/free pattern
- [slow] creates pool with linked free list
- [slow] allocates from front of free list
- [slow] updates free list pointer
- [slow] returns 0 when pool exhausted
- [slow] returns block to front of free list
- [slow] allows reuse of deallocated blocks
- [slow] tracks allocated count
- [slow] creates 8 size classes
- [slow] divides heap evenly among pools
- [slow] finds correct pool for small allocation
- [slow] finds correct pool for exact match
- [slow] returns 255 for too-large allocation
- [slow] allocates from different size classes
- [slow] handles pool exhaustion gracefully
- [slow] bump allocator is fastest for temporary allocations
- [slow] free list allocator handles general workload
- [slow] fixed block allocator is fastest for uniform objects
- [slow] multi-pool allocator balances speed and flexibility
