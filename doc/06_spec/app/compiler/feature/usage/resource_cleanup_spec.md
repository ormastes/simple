# Resource Cleanup Framework

Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegistry for leak detection with unique IDs and leak reporting, LeakTracked mixin for automatic registration, and defer/with statements for scope-based cleanup. Some tests are skipped in interpreter mode as defer and with are compiler-only features.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RES-001 |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/feature/usage/resource_cleanup_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the unified resource cleanup framework including the Resource trait
(close, is_open, resource_name), ResourceRegistry for leak detection with
unique IDs and leak reporting, LeakTracked mixin for automatic registration,
and defer/with statements for scope-based cleanup. Some tests are skipped
in interpreter mode as defer and with are compiler-only features.

## Syntax

```simple
val res = MockResource.open("test")
defer mockresource_close(res)
with open_resource("file.txt") as f:
f.read()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/resource_cleanup/result.json` |

## Scenarios

- close() releases the resource
- close() is idempotent
- is_open() returns correct state
- resource_name() provides descriptive name
- registers resources with unique IDs
- unregisters resources
- check_leaks() returns unclosed resources
- leak_report() generates human-readable output
- clear() removes all entries
- auto-registers on _start_tracking()
- auto-unregisters on _stop_tracking()
- is_tracked() returns correct state
- tracking_id() returns Some while tracked
- demonstrates defer pattern
- demonstrates leak detection in tests
