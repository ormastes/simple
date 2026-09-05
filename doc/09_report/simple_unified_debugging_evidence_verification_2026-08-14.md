<!-- codex-verify -->
# Simple Unified Debugging and Evidence — Verification Status

**Date:** 2026-08-14  
**Overall status:** FAIL — implementation is useful but the approved scope is
not yet production-ready. A Rust bootstrap seed is not Stage 4 evidence.

## Requirement evidence

| Requirement | Status | Authoritative evidence / remaining gate |
|---|---|---|
| REQ-001 | Partial | Central `DebugServiceV1` and opaque IDs are exercised by DAP, MCP, mcpgdb, interpreter, T32, OpenOCD and DbgEng adapters. Some legacy registries remain private-resource owners; full retirement is not proven. |
| REQ-002 | Proven | `debug_wire_dispatch_v1_spec.spl` and the unified System contract exercise additive-minor acceptance and major/malformed rejection. |
| REQ-003 | Partial | Migration adapters exist and DAP remains outward-facing. The documented retirement gate has not removed every legacy lifecycle owner. |
| REQ-004 | Proven | Root-operation contract and registered domain allowlist have executable coverage. |
| REQ-005 | Partial | Typed graphs exist for host/runtime/browser/device adapters; the complete desktop/mobile/server topology matrix is absent. |
| REQ-006 | Proven | Support, verification and perturbation are independent contract dimensions with focused tests. |
| REQ-007 | Partial | Event contract exists; real cross-domain propagation from runtime/browser/RPC/SQL/device is not proven. |
| REQ-008 | Partial | Bundle writer retains and rehashes raw artifacts and emits normalized layout/manifest/receipts. Native capture integrations remain incomplete. |
| REQ-009 | Partial | Core and major adapters receipt actions. An exhaustive action-path audit is still required, especially replay and unavailable external targets. |
| REQ-010 | Partial | TTL, rolling rate, retention, environment, privilege, redaction and mutation checks have focused coverage; adapter-wide enforcement is incomplete. |
| REQ-011 | Partial | Unified lifecycle/apply/list/remove/expiry works; all probe kinds are not yet mapped to native mechanisms. |
| REQ-012 | Partial | AOP validation rejects mutation and enforces typed/scoped/rate/TTL contracts; compiler application-path proof is absent. |
| REQ-013 | Partial | Doctor reports support/verification/perturbation/privilege/version/reason and profiles fail closed. Full live adapter reachability matrix is absent. |
| REQ-014 | Partial | Doctor, evidence inspect, durable live-GDB probe apply/list/remove, and digest-bound semantic reproduce/replay execute. Other replay formats and live adapter reproduction remain unavailable. |
| REQ-015 | Partial | PureDatabase SQL, CDP blocked-host, OpenOCD/T32 and interpreter service slices exist. Interpreter target execution is not LiveVerified; browser host is unavailable. |
| REQ-016 | Partial | Offline exact-build/source provenance can produce fixture-verified JS→Simple and Wasm→Simple `BoundaryFrameV1` rows and blocks mismatches. No real browser source breakpoint, source-map/DWARF consumer, or complete logical stack evidence exists. |
| REQ-017 | Partial | PureDatabase slice proves sanitized SQL, digest, plan, timing, rows, causality, exact service session/build binding, policy-first inspection and outcome receipts. Engine-native waits/locks remain incomplete. |
| REQ-018 | Partial | Existing T32/OpenOCD/JTAG mechanisms are adapted policy-first; the embedded dump slice retains and indexes raw native OpenOCD/T32/JTAG/product artifacts with fixture evidence. Physical acquisition, RTOS decoding and semantic breakpoint binding remain incomplete. |
| REQ-019 | Proven (process) | Canonical SPipe skill and mirrors contain D0–D12, faithful System→Integration fallback rules, cleanup and knowledge closure. |
| REQ-020 | Partial | Bug DB has structured provider token fields, closed-cohort averaging and knowledge gate. Full fresh suite evidence and every historical debug closure are not proven. |

## NFR evidence

| NFR | Status | Remaining gate |
|---|---|---|
| NFR-001 | Partial | Fail-closed/redaction tests exist; all adapter payloads need audit. |
| NFR-002 | Proven | Orthogonal capability dimensions and visible blocked rows are tested. |
| NFR-003 | Partial | Bundle digest/raw-copy checks exist; adapter version, immutable storage and capture metadata are not complete everywhere. |
| NFR-004 | Proven | Real crash and deadline-overrun Integration scenarios retain other sessions and receipt cleanup. |
| NFR-005 | Partial | `debug_service_v1_perf_spec.spl` defines executable p95 gates for warm lookup and passive authorization. No authoritative warm-start, ingestion or doctor row has run against an admitted Stage 4 binary. |
| NFR-006 | Partial | Central sessions, receipts, probes, action stamps and evidence metadata now have configured bounds plus rejection/eviction/drop counters. Subprocess/artifact byte bounds and ≤2% CPU/≤3% RSS evidence remain incomplete. |
| NFR-007 | Partial | Canonical artifact/replay-input ordering, content-derived bundle IDs, and deterministic semantic replay are covered by focused tests. Cross-runtime replay determinism remains unproven. |
| NFR-008 | Partial | Wire compatibility and migration bridges exist; full DAP compatibility through central service is incomplete. |
| NFR-009 | Partial | Doctor/CDP blocked-host behavior is truthful; cross-host adapter matrix is incomplete. |
| NFR-010 | Missing | Live executable coverage for REQ-015–018 is incomplete. |
| NFR-011 | Partial | Close and explicit expiry are tested; autonomous disconnect cleanup across all adapters is incomplete. |
| NFR-012 | Partial | Contracts have one owner; remaining legacy lifecycle ownership needs retirement enforcement. |
| NFR-013 | Partial | Schema/cohort/unavailable/2× logic exists; full fresh machine-check evidence remains incomplete. |

## Bootstrap 4 acceptance

No exact-source, admitted pure-Simple Stage 4 full CLI exists. The corrected
folded-module-constant Integration scenario produced a real executable but did
not reproduce the original Stage 3 failure and emitted no expected stdout.
Therefore neither the current compiler candidate nor the debug-tool suite has
Stage 4 trust. Preserve caches/logs and resume from the next phase-localized
observation; do not substitute the Rust seed or rerun the capped reproducer.

## Release decision

Do not release. Completion requires at minimum: admitted Stage 4 essential-tool
smoke; live interpreter execution; a real browser JS/Wasm/Simple breakpoint and
logical stack; service-bound SQL evidence; custom embedded dump evidence; and
the NFR-005/NFR-006 performance/resource gates.
