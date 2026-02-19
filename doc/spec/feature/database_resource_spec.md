# MCP Database Resource Specification

**Feature ID:** #MCP-DB-001 | **Category:** MCP / Database Integration | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/app/database_resource_spec.spl`_

---

## Overview

Tests for MCP database resources that provide JSON API access to:
- Bug Database (`bugdb://`)
- Feature Database (`featuredb://`)
- Test Database (`testdb://`)

All resources use the shared `lib.database` atomic operations.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 27 |

## Test Structure

### Bug Database MCP Resource
_Tests for bugdb:// MCP resource._

#### read operations

- ✅ returns empty list for new database
- ✅ returns stats for empty database
- ✅ returns error for non-existent bug
#### write operations

- ✅ adds bug via JSON
- ✅ retrieves added bug
- ✅ updates bug status
- ✅ fails to add bug without id
#### query operations

- ✅ gets open bugs only
- ✅ gets critical bugs only
- ✅ calculates correct stats
### Feature Database MCP Resource
_Tests for featuredb:// MCP resource._

#### read operations

- ✅ returns empty list for new database
- ✅ returns stats for empty database
#### write operations

- ✅ adds feature via JSON
- ✅ retrieves added feature
- ✅ updates feature status
#### query operations

- ✅ gets features by category
- ✅ gets features by status
### Test Database MCP Resource
_Tests for testdb:// MCP resource._

#### read operations

- ✅ returns empty list for new database
- ✅ returns stats for empty database
#### test run lifecycle

- ✅ starts a test run
- ✅ ends a test run
- ✅ records test result
#### analysis operations

- ✅ returns empty flaky tests for new database
- ✅ returns empty slow tests for new database
### Database MCP Integration
_Cross-database integration tests._

#### atomic operations

- ✅ database operations are atomic
#### JSON format

- ✅ escapes special characters in JSON
- ✅ handles empty strings

