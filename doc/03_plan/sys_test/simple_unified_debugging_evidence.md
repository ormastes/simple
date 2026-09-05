<!-- codex-design -->
# System Test Plan — Simple Unified Debugging and Evidence

**Status:** Planned; executable specs are an implementation deliverable
**Target spec:** `test/03_system/app/debug/simple_unified_debugging_evidence_spec.spl`
**Manual mirror:** `doc/06_spec/03_system/app/debug/simple_unified_debugging_evidence_spec.md`

## Shared scenario vocabulary

Primary manual steps: `step("Start one centrally owned debug session")`,
`step("Discover the real target graph")`, `step("Choose the cheapest decisive observation")`,
`step("Capture receipted evidence")`, `step("Inspect and reproduce offline")`,
`step("Clean up and record reusable knowledge")`.

Setup/checker helpers: `given_debug_fixture`, `given_policy_profile`,
`check_session_owner`, `check_capability_matrix`, `check_receipt`,
`check_bundle_integrity`, `check_redaction`, `check_cleanup`, and
`check_knowledge_cost_gate`. Until implemented, each oracle is fail-fast with
`assert(false)`; no placeholder pass is permitted.

## Scenarios and traceability

| Scenario | Coverage |
|---|---|
| One service owns an adapter while CLI and DAP use the same session ID | REQ-001, REQ-003, REQ-004; NFR-004, NFR-008, NFR-012 |
| Wire negotiation accepts additive minor and rejects major mismatch | REQ-002; NFR-008 |
| Target discovery produces typed real edges and omits fabricated nodes | REQ-005, REQ-007; NFR-002 |
| Doctor reports live, fixture, unverified, blocked and unavailable honestly | REQ-006, REQ-013; NFR-002, NFR-009 |
| Observe is permitted while Control is denied without changing execution | REQ-009, REQ-010; NFR-001, NFR-011 |
| Probe apply/list/TTL cleanup share IDs and complete receipts | REQ-011, REQ-014; NFR-006, NFR-011 |
| Mutating AOP aspect is rejected in mission-critical mode | REQ-012; NFR-001 |
| Bundle retains raw artifact, normalized index, digests and exact build | REQ-008; NFR-003, NFR-007 |
| Adapter crash is isolated and session is labeled/cleaned | REQ-002, REQ-009; NFR-004, NFR-011 |
| Interpreter semantic breakpoint yields structured frames and evidence | REQ-015; NFR-010 |
| SQLite trace/plan/lock evidence is correlated and bind values redacted | REQ-015, REQ-017; NFR-001 |
| Chrome worker auto-attach crosses JS/Wasm/Simple with a real source breakpoint | REQ-015, REQ-016; NFR-010 |
| Embedded retained dump precedes halt and OpenOCD/T32 blocked rows are truthful | REQ-015, REQ-018; NFR-009, NFR-010 |
| D0–D12 investigation preserves original failure and cleans temporary tools | REQ-019; NFR-011 |
| Resolved bug records token fields; >2× ratio requires knowledge link | REQ-020; NFR-013 |
| Warm startup, lookup, event throughput, bounds and overhead meet budgets | NFR-005, NFR-006 |

## Evidence levels

Use deterministic fixtures for wire, policy, redaction and parsers; integration
processes for isolation and SQLite; a real Chrome runtime for source breakpoint
and worker claims; and real or declared blocked physical targets for embedded.
Fixture parsing never satisfies a live claim. TUI scenarios capture text/ANSI;
protocol and bundle scenarios capture typed SDN and artifact digests.

Run each acceptance criterion once per verification session. Generate the manual
with `spipe-docgen`, require zero stubs, scan with `sspec-maintain`, and require
no executable `.spl` beneath `doc/06_spec`.
