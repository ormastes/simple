# Theme Sync Diff Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #THEME-SYNC-002 |
| Category | Tooling / Theme Sync |
| Status | Implemented |
| Type | Unit Spec |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/lib/ui/theme_sync/theme_sync_diff_test.spl` |
| Coverage Target | `src/lib/common/ui/theme_sync_diff.spl` |
| Generator | Manual mirrored SSPEC doc |

## Overview

Verifies that theme-sync diff logic detects token drift between local and
remote Stitch design systems and renders a readable drift report.

## Scenarios

Generated from executable SPipe scenarios in the source test. The source covers
no-drift comparisons, metadata drift, typography drift, shape drift, named color
drift, color override drift, spacing drift, and colorized report output.
