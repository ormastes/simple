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

REQ-OPJH-011: Tiered JIT tier-1 promotion shall consume eligible hotspot plans before native compilation while preserving original-source compilation when the provider is disabled or facts are missing.

REQ-OPJH-012: JIT hotspot specialization providers shall only replace compile source when the plan is eligible, specialized source exists, and a semantic proof is declared.

REQ-OPJH-013: JIT hotspot planning for reassigned `var` storage shall require explicit SSA transform, escape/no-escape, and borrow-reassignment-safe facts before accepting specialization.

REQ-OPJH-014: Hotspot rebuild planning shall distinguish Cranelift tier-1 medium-cost rebuilds from LLVM tier-2 high-cost rebuilds and shall not schedule LLVM rebuilds before the tier-2 threshold or when the backend is unavailable.

REQ-OPJH-015: The MIR optimizer shall expose analyzer-derived JIT var facts from repeated local definitions, escape evidence, and borrow-reassignment safety rather than requiring all `var` hotspot facts to be supplied manually.

REQ-OPJH-016: The MIR optimizer shall provide a conservative SSA var transform for straight-line reassignment hot paths, and shall explicitly reject CFG cases that require phi-node insertion until phi construction is implemented.

REQ-OPJH-017: SSA var transform rejection shall report simple branch-merge phi requirements with the affected local IDs so a later phi-insertion pass can consume concrete placement data.

REQ-OPJH-018: SSA var analysis shall expose a concrete phi insertion plan for simple branch merges, including join block, original local, planned branch value locals, and phi destination local.

REQ-OPJH-019: SSA var analysis shall be able to materialize simple branch-merge phi plans into MIR using a pseudo-phi intrinsic until backend-native phi lowering is implemented.

REQ-OPJH-020: The interpreter shall consume the `__simple_ssa_phi` pseudo-intrinsic with a deterministic fallback so materialized SSA MIR remains executable outside native backends.
