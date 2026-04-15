# Compressed Logging Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/compressed_logging_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/compressed_logging/result.json` |

## Scenarios

- [slow] QEMU produces binary protocol output
- [slow] binary output contains valid frame structure
- [slow] decoder resolves handles to Hello message
- [slow] decoder resolves all messages
- [slow] compressed binary data is smaller than text strings
