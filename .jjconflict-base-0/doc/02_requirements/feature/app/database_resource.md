# MCP Database Resource Specification
*Source:* `test/feature/app/database_resource_spec.spl`

## Overview



**Difficulty:** 3/5

## Overview

Tests for MCP database resources that provide JSON API access to:
- Bug Database (`bugdb://`)
- Feature Database (`featuredb://`)
- Test Database (`testdb://`)

All resources use the shared `lib.database` atomic operations.

## Behavior

### Bug Database MCP Resource

### When read operations

- returns empty list for new database
- returns stats for empty database
- returns error for non-existent bug

### When write operations

- adds bug via JSON
- retrieves added bug
- updates bug status
- fails to add bug without id

### When query operations

- gets open bugs only
- gets critical bugs only
- calculates correct stats

### Feature Database MCP Resource

### When read operations

- returns empty list for new database
- returns stats for empty database

### When write operations

- adds feature via JSON
- retrieves added feature
- updates feature status

### When query operations

- gets features by category
- gets features by status

### Test Database MCP Resource

### When read operations

- returns empty list for new database
- returns stats for empty database

### When test run lifecycle

- starts a test run
- ends a test run
- records test result

### When analysis operations

- returns empty flaky tests for new database
- returns empty slow tests for new database

### Database MCP Integration

### When atomic operations

- database operations are atomic

### When JSON format

- escapes special characters in JSON
- handles empty strings


