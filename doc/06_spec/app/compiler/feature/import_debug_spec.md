# Bug Database Import Debug Test

**Feature ID:** #STDLIB-001 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/import_debug_spec.spl`_

---

## Overview

Minimal test verifying that the BugDatabase module can be imported and instantiated using
describe/it blocks. Tests that create_bug_database can be called without a direct import
of the function (relying on wildcard import resolution) and that the resulting database
contains the expected "bugs" table.

## Syntax

```simple
var db = create_bug_database("/tmp/describe_test.sdn")
check(db.db.tables.contains_key("bugs"))
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Test create_bug_database

- ✅ calls create_bug_database without importing it

