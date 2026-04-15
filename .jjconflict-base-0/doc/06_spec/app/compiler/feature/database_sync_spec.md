# Database Sync Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/database_sync_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/database_sync/result.json` |

## Scenarios

- creates database file after atomic write
- does not leave temp files after successful write
- preserves old file if write fails
- makes file readable immediately after save
- cleans up stale .tmp files on startup
- adds less than 5% latency to save
- acquires lock for database access
- releases lock explicitly
- blocks second process from acquiring lock
- prevents deadlock with timeout
- serializes concurrent reads
- serializes concurrent writes
- prevents lost updates under concurrent access
- cleans up stale lock files on startup
- removes lock file if process crashes
- has negligible overhead under no contention
- acceptable latency under light contention
- loads TodoDb using unified API
- saves TodoDb using unified API
- loads FeatureDb using unified API
- loads TaskDb using unified API
- gets record by ID
- inserts new record
- deletes record
- lists all records
- counts records
- applies lock during load
- applies lock during save
- maintains old API for TodoDb
- loads files saved with old format
- has single sync logic for all types
- reduces duplication
- handles concurrent read/write safely
- prevents data corruption under stress
- survives process crash gracefully
- maintains performance under all phases
