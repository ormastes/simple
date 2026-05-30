# Ipc Protocol Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/unit/app/ui/ipc_protocol_spec.spl` |
| Updated | 2026-05-28 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SPipe scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/unit/app/ui/ipc_protocol/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/app/ui/ipc_protocol/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/app/ui/ipc_protocol/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/app/ui/ipc_protocol/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/app/ui/ipc_protocol/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/app/ui/ipc_protocol/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/app/ui/ipc_protocol/stdout.log` |

## Scenarios

- parses keypress events
- parses action events
- parses resize events
- parses quit events
- returns nil for unknown messages
- parses fetch results with headers
- builds a render message
- builds a dialog message
- builds a notification message
- builds a GET fetch request without body fields
- builds a POST fetch request with body and content type
- extracts string fields
- returns empty for missing fields
- escapes special characters
- escapes quotes
