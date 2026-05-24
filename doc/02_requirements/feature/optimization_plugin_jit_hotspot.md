<!-- codex-research -->
# Optimization Plugin JIT Hotspot Requirements

REQ-OPJH-001: Simple Optimization Plugin shall include JIT hotspot optimization as a first-class provider kind, not only compiler or interpreter optimization.

REQ-OPJH-002: JIT hotspot providers shall use the same metadata contract as compiler providers: name, version, kind, load mode, lookup kind, hot path flag, required facts, produced facts, and safety class.

REQ-OPJH-003: Built-in JIT hotspot providers shall be representable in source without dynamic loading.

REQ-OPJH-004: A JIT hotspot provider shall run only when required runtime facts are available.

REQ-OPJH-005: The guide, architecture doc, and spec shall document JIT hotspot provider behavior, fallback, and safety rules.

REQ-OPJH-006: Tests shall cover provider metadata and missing-fact rejection for JIT hotspot providers.

REQ-OPJH-007: Tiered JIT profiling shall expose optimizer-facing hotspot facts from function call counts and tier thresholds.

REQ-OPJH-008: Hotspot planning shall be testable without invoking native JIT compilation or runtime externs.

REQ-OPJH-009: Hotspot plans shall support explicit invalidation while preserving fallback execution.

REQ-OPJH-010: JIT hotspot planning shall have a representative benchmark covering cold, ready, and invalidated plans before documentation makes performance claims.
