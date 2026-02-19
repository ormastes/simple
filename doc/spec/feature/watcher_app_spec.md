# watcher_app_spec

**Category:** Tooling | **Status:** Active

_Source: `test/feature/watcher/watcher_app_spec.spl`_

---

System test for file watcher application integration.

Tests the file watcher's integration with the application lifecycle,
including monitoring source files, triggering rebuilds, and error handling.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 5 |

## Test Structure

### File Watcher

#### when monitoring source files

- ✅ detects basic changes
- ✅ handles multiple file operations
#### when rebuilding on changes

- ✅ recalculates simple math
- ✅ maintains state correctly
#### when handling errors

- ✅ recovers from errors gracefully

