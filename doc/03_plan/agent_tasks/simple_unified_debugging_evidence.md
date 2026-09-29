<!-- codex-design -->
# Agent Task Plan — Simple Unified Debugging and Evidence

**Status:** Contract names frozen; implementation not started by this plan
**Merge owner:** A0 contract/service lead
**Final reviewer:** best available normal/highest-capability architecture and verification reviewer independent of implementation

## Interface lock

Frozen names: `DebugServiceV1`, `DebugWireV1`, `DebugSessionId`,
`DebugTargetGraphV1`, `DebugCapabilityV1`, `DebugEventV1`, `DebugReceiptV1`,
`DebugPolicyV1`. Existing `DebugTarget`, `ProfileTarget`, and `DebugBackend` are
adapters. A0 records the hash of the approved schema set before fan-out. Only A0
edits shared schemas; proposed changes return as review notes.

Before sidecars start, A0 also freezes the system-test step/helper names and
fail-fast placeholders from the system-test plan.

## Lanes

| Lane | Ownership | Dependencies | Sidecar |
|---|---|---|---|
| A0 | contracts, registry, interface-lock hash, merge | none | N/A; primary owner |
| A1 | build/source identity, bundles, receipts, redaction | A0 | Codex Spark/Claude Haiku exploration allowed |
| A2 | adapter host, doctor, CLI, DAP/MCP and legacy bridges | A0 | Claude Sonnet review allowed |
| A3 | interpreter, SMF/JIT, native metadata | A0–A1 | lower-model inventory only |
| A4 | CDP, JS source maps, Wasm DWARF, Simple browser scripts | A0–A1 | lower-model fixture survey allowed |
| A5 | server ObserveContext/OTel/eBPF | A0–A1 | lower-model inventory allowed |
| A6 | SQLite first, then other SQL adapters | A0–A1 | lower-model engine matrix allowed |
| A7 | desktop/UI/GPU evidence | A0–A2 | lower-model platform inventory allowed |
| A8 | Android lifecycle/tombstone/ANR/Perfetto | A0–A2 | lower-model fixture inventory allowed |
| A9 | Apple lifecycle/crash/dSYM/watchdog | A0–A2 | lower-model fixture inventory allowed |
| A10 | embedded agent, dumps, JTAG/T32/OpenOCD | A0–A2 | lower-model hardware inventory allowed |
| A11 | policy, privilege, privacy, adversarial review | A0–A1 | N/A; independent reviewer |
| A12 | Modern SSpec, evidence showcase, docs/skills/knowledge/cost gate | all relevant lanes | lower-model doc audit, highest-model acceptance |

## Wave gates

1. Contract: schema tests and interface-lock review.
2. Evidence: exact-build offline bundle and redaction/integrity evidence.
3. Core: isolation, doctor, DAP/MCP/CLI and migration parity.
4. Native: interpreter then SMF/JIT/native debug evidence.
5. Vertical: SQLite, Chrome, embedded; blocked-host rows remain failures when
   required and honest skips only when optional.
6. Cross-domain/release: causality, replay, live matrices, performance/privacy
   budgets and independent verification PASS.

Each lane returns scope, owned files, interface-lock hash, dependencies,
changes, tests, live evidence, privacy impact, blocked rows, risks and rollback.
No lane marks a parser fixture as live support or edits another lane's files.
