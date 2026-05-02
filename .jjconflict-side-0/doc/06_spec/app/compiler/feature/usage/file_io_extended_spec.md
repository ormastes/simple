# Extended File I/O Specification

Extended File I/O operations including line-based reading, append operations,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #700-715 |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/feature/usage/file_io_extended_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Extended File I/O operations including line-based reading, append operations,
binary I/O, file moving, recursive directory operations, and path utilities.

Self-contained: all I/O functions defined inline via extern fn declarations.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/file_io_extended/result.json` |

## Scenarios

- reads multiple lines correctly
- reads empty file as empty list
- appends to existing file
- creates file if not exists
- preserves binary data exactly
- moves file to new location
- creates nested directories
- returns all files recursively
- gets absolute path
- removes directory and contents
- extracts filename without extension
- handles multiple dots
- handles no extension
- computes relative path
- handles same path
- joins two paths
- read_lines fails for non-existent file
- read_bytes fails for non-existent file
- move_file fails for non-existent source
- walk_dir fails for non-existent directory
