# ADR-001: Logger Name Matches Session Name

**Date:** 2026-03-07
**Status:** Accepted

## Context

The project has multiple logger implementations across different subsystems:

| Logger | Location | Name/ID field |
|--------|----------|---------------|
| `BootLogger` | `src/compiler/80.driver/driver_types.spl` | None |
| `BuildLogger` | `src/compiler/80.driver/build_log.spl` | `session_id` (UUID) |
| Bare-metal logger | `src/lib/nogc_async_mut_noalloc/log/logger.spl` | None |
| `McpLogger` | `src/compiler_rust/lib/std/src/mcp/core/logger.spl` | None (only `file_path`) |

`BuildLogger` records compilation sessions with a `session_id` (random UUID), but the other loggers have no name or identifier. When correlating log output across subsystems — especially during debugging — there is no way to associate log entries with the session that produced them.

## Decision

All loggers must use the same name as the session they belong to.

When a compilation or execution session is started, the session identifier (e.g., `BuildLogger.session_id`) becomes the canonical name for all loggers active during that session. Logger output must include this session name so that log entries can be correlated across subsystems.

Concretely:

1. Loggers that participate in a session must accept a `name: text` field matching the session identifier.
2. Log output format includes the name prefix: `[session_name][LEVEL] message`.
3. If no session context exists (e.g., bare-metal standalone), the logger name defaults to the module name.

## Rationale

- **Traceability:** A single session ID in all log lines enables grep-based filtering across subsystems.
- **Simplicity:** Reusing the session name avoids introducing a separate logger naming scheme.
- **Debugging:** When multiple sessions run concurrently (e.g., parallel builds, MCP server handling multiple requests), the session name disambiguates log output.

## Alternatives Considered

| Option | Pros | Cons |
|--------|------|------|
| Separate logger names (e.g., "compiler", "mcp") | Descriptive per-subsystem | Cannot correlate across subsystems for the same session |
| No logger names | Zero overhead | Impossible to filter in concurrent scenarios |
| **Session name as logger name** | Unified, correlatable, simple | Requires threading session context to all loggers |

## Consequences

**Positive:**
- All log output from a single session can be filtered with one identifier
- Consistent naming convention across all logger implementations

**Negative / Trade-offs:**
- Loggers that previously had no name field need a `name: text` parameter added
- Session context must be passed to subsystem loggers (slightly more plumbing)

**Risks:**
- Bare-metal logger uses `i32` handles for performance; adding a text name may not be appropriate there. Mitigation: use a numeric session handle in bare-metal contexts, with text name only in hosted loggers.
