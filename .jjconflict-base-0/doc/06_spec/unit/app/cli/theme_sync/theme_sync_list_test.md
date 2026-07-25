# Theme Sync CLI List Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #THEME-SYNC-003 |
| Category | Tooling / Theme Sync CLI |
| Status | Implemented |
| Type | Unit Spec |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/cli/theme_sync/theme_sync_list_test.spl` |
| Coverage Target | `src/app/cli/theme_sync.spl` |
| Generator | Manual mirrored SSPEC doc |

## Overview

Verifies pure helper behavior used by the theme-sync CLI: flag parsing,
`sync_mode.sdn` value extraction, and local theme availability.

## Scenarios

Generated from executable SPipe scenarios in the source test. The source covers
flag value extraction, boolean flag detection, SDN field reads, sync mode
format parsing, and valid local theme names.
