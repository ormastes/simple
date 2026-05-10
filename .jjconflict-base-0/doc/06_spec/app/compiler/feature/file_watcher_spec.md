# File Watcher Specification

**Feature ID:** #WATCHER-001 | **Category:** Tools | Development | **Status:** Implemented

_Source: `test/feature/usage/file_watcher_spec.spl`_

---

## Watcher Behavior

1. On start: perform initial build
2. Watch source file for changes
3. On change: rebuild module
4. Output SMF to .simple/build/ directory

## Syntax

```bash
simple watch src/main.spl
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 3 |

## Test Structure

### File Watcher

- ✅ performs initial build on start
- ✅ rebuilds on file change
- ✅ outputs SMF to build directory

