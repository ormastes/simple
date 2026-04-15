# UI Access Protocol — NFRs

**Date:** 2026-04-15
**Status:** Selected requirements
**Options Source:** `doc/02_requirements/nfr/ui_access_protocol_options.md`

## Performance

- NFR-UAP-001: Access snapshots shall be derived from in-memory session and
  surface state; the hot path shall not shell out, scan the filesystem, or make
  external process calls.
- NFR-UAP-002: Recent-event history shall remain bounded in memory.
- NFR-UAP-003: `ui_access_find` shall filter the in-memory snapshot rather than
  rebuilding state through repeated scans.

## Compatibility

- NFR-UAP-004: The new protocol shall be additive and shall not break existing
  `/api/test/*`, widget tools, or screen-read flows.
- NFR-UAP-005: Consumers that ignore the new UI access tools/routes shall
  continue to work without code changes.

## Reliability

- NFR-UAP-006: If no `UISession` is available, additive test routes shall return
  an empty or state-derived access response rather than crashing.
- NFR-UAP-007: Missing surfaces or invalid canonical IDs shall return explicit
  error responses.

## Observability

- NFR-UAP-008: The protocol shall expose recent event history suitable for human
  or LLM debugging.
- NFR-UAP-009: Canonical IDs and surface IDs shall be readable enough to support
  direct debugging without hidden opaque tokens.

## Testability

- NFR-UAP-010: The shared access module shall have unit coverage for canonical
  IDs, snapshot building, finding, and event history.
- NFR-UAP-011: The tool registry shall have automated coverage for the new UI
  access schema surface.
