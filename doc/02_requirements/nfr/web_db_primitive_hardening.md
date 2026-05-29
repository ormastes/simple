<!-- codex-research -->
# NFR - Web DB Primitive Hardening

## NFR-001: Reliability
Shutdown and closed-channel behavior must be deterministic and covered by tests.

## NFR-002: Data Safety
Database persistence must use existing atomic production APIs and temporary test files under `/tmp`.

## NFR-003: Maintainability
No new production `pass_todo` or undocumented `pass_do_nothing` may be introduced in touched files.

## NFR-004: Compatibility
Existing public module paths and constructors remain stable.

## NFR-005: Regression Coverage
Run targeted HTTP/web, database, primitive, and required core/MCP smoke checks after implementation.
