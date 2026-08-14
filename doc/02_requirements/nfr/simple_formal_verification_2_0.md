<!-- codex-design -->
# Simple Formal Verification 2.0 — Non-Functional Requirements

**Status:** Selected baseline
**Date:** 2026-08-12
**Recovered:** 2026-08-14

- **NFR-FV2-001 Reproducibility:** A clean build with pinned sources and tools reproduces semantic hashes, certificates, and receipts.
- **NFR-FV2-002 Sound failure:** Unsupported, stale, contradictory, timed-out, missing-tool, and unknown states fail closed.
- **NFR-FV2-003 Bounded trust:** Every trusted dependency and environmental assumption is named, classified, versioned, and attributable to an artifact.
- **NFR-FV2-004 Incrementality:** Development verification operates on SymbolId/SCC dependency closure and semantic cache keys; formatting-only edits do not invalidate proofs.
- **NFR-FV2-005 Determinism:** Expansion, weaving, VIR, Lean IR, solver routing, and receipt construction are deterministic under `verified`.
- **NFR-FV2-006 Performance:** No proof machinery remains at runtime except deliberately enabled bounded monitors. Warm incremental checks report timing/cache metrics and avoid full-tree scans or per-obligation process startup where batching is possible.
- **NFR-FV2-007 Diagnostics:** Counterexamples map to source spans, SymbolIds, values, effects, OS events, or RTL signals as applicable.
- **NFR-FV2-008 Evolvability:** Frozen public evidence schemas are versioned; incompatible changes require migration tests and cache invalidation.
- **NFR-FV2-009 Independence:** High-assurance release replay uses a fresh Lean environment and at least one independent checker where supported; RISC-V uses an oracle not generated from the implementation under test.
- **NFR-FV2-010 Scalability:** Proof scheduling is DAG-based and parallelizable across independent SCCs, pass certificates, OS subsystems, ISA families, and mutation jobs.

These targets remain acceptance requirements, not measurements already achieved. Current-main MIR evidence work is fail closed but does not yet establish reproducibility, incremental performance, independent replay, or end-artifact assurance for the complete FV2 chain.
