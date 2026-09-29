# SPipe Knowledge Compiler MCP and hostile-input contract

> Frames 1 MiB (`frame_too_large`), headers 32 KiB (`limit_exceeded`), JSON depth

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe Knowledge Compiler MCP and hostile-input contract

Frames 1 MiB (`frame_too_large`), headers 32 KiB (`limit_exceeded`), JSON depth

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirement map
- Views/tools: REQ-SPKC-006..009, 026; NFR-SPKC-004, 011, 019..020.
- Negotiation/compatibility: REQ-SPKC-010, 027, 030; NFR-SPKC-003, 016, 019.
- Containment/auth/privacy: NFR-SPKC-005..007, 021..022.

## Fixed limits and typed failures
Frames 1 MiB (`frame_too_large`), headers 32 KiB (`limit_exceeded`), JSON depth
64 (`invalid_request`), method 128 bytes, URI 8 KiB, query 4 KiB, decoded string
256 KiB, aggregate args 512 KiB, list 100, search candidates 1,000, trace depth
8/nodes 2,000, response 1 MiB, manual 200 lines/about 6,000 tokens, and 16
in-flight requests. Limit-plus-one must fail before dispatch or cache mutation.

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl --output doc/06_spec --no-index`

## Scenarios

### SPipe MCP protocol and hostile-input boundaries

#### should negotiate and browse through legacy and stateless transports

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-006..009
```

</details>

<details>
<summary>Advanced: should reject every configured limit-plus-one input before effects</summary>

#### should reject every configured limit-plus-one input before effects

- Browse virtual knowledge views
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-007, REQ-SPKC-008, REQ-SPKC-009
step("Browse virtual knowledge views")
fail("DESIGN-SCAFFOLD: assert frame_too_large/limit_exceeded/invalid_request at every fixed boundary")
```

</details>


</details>

<details>
<summary>Advanced: should isolate principals snapshots cursors caches and prompt content</summary>

#### should isolate principals snapshots cursors caches and prompt content

- Search and trace artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPKC-008, REQ-SPKC-009, REQ-SPKC-010
step("Search and trace artifacts")
fail("DESIGN-SCAFFOLD: assert unauthorized/stale_cursor and zero cross-scope cache or prompt leakage")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SPKC-010`
- `REQ-SPKC-006..009`
- `REQ-SPKC-010..009`
- `REQ-SPKC-008`
- `REQ-SPKC-007`
- `REQ-SPKC-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e131c91deee76ee8a7dae6f3d10c729161325f4772db6545cbc3a1dbca22c7f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e131c91deee76ee8a7dae6f3d10c729161325f4772db6545cbc3a1dbca22c7f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e131c91deee76ee8a7dae6f3d10c729161325f4772db6545cbc3a1dbca22c7f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **73/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md (current)
findings: 10 blockers: 2
  narrative=100 structure=75 oracle=50
  traceability=60 evidence=75 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=73; blocker cap makes effective=49
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should negotiate and browse through legacy and stateless transports' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should negotiate and browse through legacy and stateless transports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every configured limit-plus-one input before effects' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should isolate principals snapshots cursors caches and prompt content' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should isolate principals snapshots cursors caches and prompt content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
