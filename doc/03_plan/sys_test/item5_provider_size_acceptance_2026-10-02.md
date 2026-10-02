# Item 5 concrete runtime acceptance and TDD plan

Status: planned, not executed. Requirements remain the user-selected 2026-09-02
contract; no budgets or supported hosts are removed.

Each executable SSpec scenario uses step descriptions, REQ/NFR tags, real
production calls and built-in matchers. Source substring checks are auxiliary
architecture checks. Missing native artifacts or receipts block acceptance.
Existing synthetic BS7 receipts verify their checker only.

| Case | Requirement | Setup, action and observable assertion |
|---|---|---|
| I5-01 | REQ-001, NFR-005 | Start no-import hello with loader/init counters; register all optional descriptors; assert zero mappings, initializations, archive reads and provider effects before demand. |
| I5-02 | REQ-002, REQ-015 | Install sealed precompiled provider; demand a capability; assert exactly one admitted load/init, expected output and no source parse; repeat demand and assert reuse. |
| I5-03 | REQ-002, REQ-012 | Mutate missing artifact, digest, ABI, target, architecture, dependency and policy independently; assert exact typed error and zero initialization/effects. |
| I5-04 | REQ-002 | Supply coherent image/receipt digests but mismatched pinned member identity/extent/checksum; reject archive authority before publication. Include archive-size bounds. |
| I5-05 | REQ-002 | Concurrent first demand with bounded synchronization; assert one initializer, identical admitted identity, no partial receipt, stable cached refusal on failed initialization. |
| I5-06 | REQ-004, REQ-005 | Exercise pure and foreign selection and rollback; effectful fixture records one write per request. Shadow comparisons execute only admitted pure bounded operations. |
| I5-07 | REQ-006, REQ-011, NFR-006 | Run actual parity/failure/mutation/resource fixtures for each retained provider family and supported target; assert same results/errors and no unrelated provider dependency. |
| I5-08 | REQ-003, REQ-007, REQ-013 | Link NoGC no-allocation hello; inspect map, sections, constructors, exports and dynamic dependencies; assert no collector/compiler/backend/optional roots and a reason for every retained root. |
| I5-09 | REQ-008, REQ-009, REQ-010 | Compare release-small, ordinary release and debug; prove omitted unwind/RTTI/exceptions unnecessary; demand an exception-requiring foreign provider and assert base size/roots unchanged and functionality retained. |
| I5-10 | REQ-011, REQ-012 | Hold live provider pin then request close; assert refusal; release pin and close; assert later invocation rejected. Do not require OS unmapping immediately after close. |
| I5-11 | REQ-014, NFR-001..003 | Replay exact captured link and strip inputs for Simple/C same-output hello; verify artifact hashes and size limits, with admitted non-ELF allowance. Retain unstripped/stripped bytes and inspection products. |
| I5-12 | NFR-004, NFR-007 | Collect matched same-host Python/Simple startup and peak RSS: at least 30 development or 100 release samples, p50/p95, binary/toolchain/source hashes. Reject stale or synthetic cohorts. |
| I5-13 | REQ-003, REQ-015 | Invoke packaged CLI optional command; observe compiled-artifact demand boundary, then exercise unavailable provider; assert no raw-source fallback and no eager Office/UI/GPU roots in minimal command. |
| I5-14 | item 5 layering | Inspect and exercise kernel/driver versus extension ownership; retain existing owner-result/provider interfaces, no unsolicited ECS/MDSOC+ kernel conversion. |

## Bounded sequence

1. Discover admitted runtime and record its immutable identity. Add a behavioral
   regression for the pinned-member authority seam, observe RED, implement the
   minimal validation in its owner, then observe GREEN once.
2. Extend actual loading/target/policy and lifetime coverage around the existing
   src/os/smf/provider_loader.spl; do not create a competing loader.
3. Implement exact link closure, provider packaging and CLI cutover with separate
   isolated ownership. RuntimeFeatureClosureV1 must be proven in current source,
   not inferred from a historical document.
4. Build real size/startup cohorts and cross-host qualification evidence. Run
   required core/MCP/LSP checks once after relevant changes and update manuals
   from executable specs. At most three fix/verification cycles per feature.

Acceptance ledger records source/head/target, fixture hashes, command, exit,
assertion result, evidence path and remaining blockers per case. No helper PASS,
source-token match or metadata-only receipt certifies native execution.
