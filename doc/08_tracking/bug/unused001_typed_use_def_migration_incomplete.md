# UNUSED001 typed use-def migration is incomplete

**Status:** OPEN (unverified 2026-09-12)

## Status

Open. Query lint's compatibility producer is now linear in source and identifier volume,
but it remains a textual approximation.

## Current safe boundary

The producer counts whole identifier tokens once per function and excludes each
declaration line when deciding whether that declaration is referenced. This preserves
legacy handling of comments, strings, shadowed names, and declaration order while
removing per-declaration whole-function rescans.

## Completion condition

Typed HIR use-def facts distinguish lexical bindings, shadowing, captures, patterns,
generated uses, and unreachable uses; exact spans flow into the diagnostic record; the
text producer becomes fallback-only; comparative fixtures prove warning compatibility or
document deliberate precision changes; warm latency and allocation evidence covers files
with many declarations.

Unknown or incomplete binding facts must suppress a typed claim, not infer unused state.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
