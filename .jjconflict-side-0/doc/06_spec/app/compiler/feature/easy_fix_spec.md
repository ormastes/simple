# Easy Fix Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/easy_fix_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/easy_fix/result.json` |

## Scenarios

- has Safe level
- has Likely level
- has Uncertain level
- Safe != Likely
- Safe != Uncertain
- Likely != Uncertain
- creates a replacement with all fields
- creates a zero-length insertion
- creates a deletion (empty new_text)
- formats for display
- creates an empty fix
- adds replacements
- adds multiple replacements
- reports safe confidence
- reports non-safe for Likely
- reports non-safe for Uncertain
- formats confidence as string
- replaces text at the beginning
- replaces text at the end
- replaces text in the middle
- inserts text (zero-length span)
- deletes text (empty new_text)
- applies two fixes in same file
- applies three fixes preserving order
- detects overlapping spans
- applies fixes to different files
- returns error for missing file
- Safe filter returns only safe fixes
- Likely filter returns safe and likely
- Uncertain filter returns all
- returns empty list when no fixes match
- filters by prefix
- returns empty when no match
- matches exact prefix
- starts with zero counts
- formats dry-run report
- formats applied report
- creates lint with easy_fix
- creates lint without easy_fix
- reports has_easy_fix true when present
- reports has_easy_fix false when absent
- includes fix info in formatted output
- handles empty fix list
- handles fix with no replacements
- replaces entire file content
- inserts at beginning of file
- appends at end of file
- handles replacement longer than original
- handles replacement shorter than original
- applies adjacent non-overlapping fixes
