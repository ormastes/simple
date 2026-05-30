# Ipc Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/unit/app/ui/ipc_spec.spl` |
| Updated | 2026-05-28 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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
| `result.json` | JSON artifact | `build/test-artifacts/unit/app/ui/ipc/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/app/ui/ipc/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/app/ui/ipc/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/app/ui/ipc/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/app/ui/ipc/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/app/ui/ipc/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/app/ui/ipc/stdout.log` |

## Scenarios

- extracts type field from JSON
- extracts key field from JSON
- returns empty string for missing field
- handles JSON with spaces around colon
- returns empty string for empty input
- parses keypress message into UIEvent.KeyPress
- parses quit message into UIEvent.Quit
- returns nil for empty string
- returns nil for unrecognized message type
- parses action message
- parses resize message
- wraps html in JSON with type render
- includes html content in output
- produces valid JSON structure
- escapes double quotes
- escapes backslashes
- escapes newlines
- passes plain text unchanged
- handles empty string
