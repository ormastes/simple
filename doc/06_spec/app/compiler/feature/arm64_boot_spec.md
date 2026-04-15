# Arm64 Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/arm64_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/arm64_boot/result.json` |

## Scenarios

- [slow] generates valid exception vector table
- [slow] checks vector table alignment
- [slow] sets up exception levels correctly
- [slow] maintains stack pointer alignment
- [slow] boots on virt machine
- [slow] handles exceptions correctly
