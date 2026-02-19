# Minimal Helper Import Test

**Feature ID:** #STDLIB-002 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/minimal_spec.spl`_

---

## Overview

Minimal test verifying that helper functions can be imported from test utility modules.
Tests that the test_file_exists helper from the minimal_helper module can be called
successfully within a describe/it block structure, validating basic cross-module import
resolution in the test framework.

## Syntax

```simple
use test.lib.minimal_helper.{test_file_exists}
val result = test_file_exists("/tmp/test")
check(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Test helper import

- ✅ calls helper

