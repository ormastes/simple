# File Watcher Specification

Tests the file watcher for automatic rebuilds including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCHER-001 |
| Category | Tools \| Development |
| Status | Implemented |
| Source | `test/feature/usage/file_watcher_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the file watcher for automatic rebuilds including:
- Initial build on start
- Rebuild on file change
- SMF output generation

## Watcher Behavior

1. On start: perform initial build
2. Watch source file for changes
3. On change: rebuild module
4. Output SMF to .simple/build/ directory

## Syntax

```bash
simple watch src/main.spl
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/file_watcher/result.json` |

## Scenarios

- performs initial build on start
- rebuilds on file change
- outputs SMF to build directory
