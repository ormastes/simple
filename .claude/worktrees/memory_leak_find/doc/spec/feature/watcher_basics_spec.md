# File Watcher Change Detection and Rebuild Cycle

**Feature ID:** #TOOL-007 | **Category:** Tooling | **Status:** Active

_Source: `test/feature/watcher/watcher_basics_spec.spl`_

---

## Overview

The file watcher monitors source files for modifications and automatically
triggers a rebuild when changes are detected. This spec exercises the core
watch-rebuild cycle: basic change detection on arithmetic expressions, handling
of multiple file operations (e.g., list mutations), correctness of recalculated
values after a simulated change, preservation of mutable state across loop-based
rebuilds, and graceful recovery when an error occurs during the cycle.

## Syntax

```simple
# Basic change detection -- values recomputed on rebuild
val sum = x + y
expect(sum).to_equal(3)

# Multiple file operations trigger watcher
var data = [1, 2, 3]
data.push(4)
expect(data.len()).to_equal(4)

# State preserved correctly across rebuild iterations
var counter = 0
for i in [1, 2, 3]:
    counter = counter + i
expect(counter).to_equal(6)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Change detection | Watcher identifies modified source files and initiates rebuild |
| Automatic rebuild | Compilation is re-triggered without manual intervention |
| State management | Mutable variables are correctly reset or preserved across rebuilds |
| Error recovery | The watcher continues operating after a build error instead of crashing |

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

