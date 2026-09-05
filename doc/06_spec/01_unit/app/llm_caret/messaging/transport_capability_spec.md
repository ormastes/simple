# Transport Capability Specification

> Tests covering LLM Caret transport capability truth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Capability Specification

## Scenarios

### LLM Caret transport capability truth

#### publishes a versioned snapshot for every requested transport

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes a versioned snapshot for every requested transport
   - Expected: descriptor.capabilities.version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("publishes a versioned snapshot for every requested transport")
for name in supported_chat_adapters():
    val descriptor = chat_adapter_descriptor(name)
    expect(descriptor.tier).to_be_greater_than(-1)
    expect(descriptor.capabilities.version).to_equal(1)
```

</details>

<details>
<summary>Advanced: uses primitive shadow rooms for missing LINE and Kakao private rooms</summary>

#### uses primitive shadow rooms for missing LINE and Kakao private rooms

- uses primitive shadow rooms for missing LINE and Kakao private rooms
   - Expected: decision.accepted is true
   - Expected: decision.execution equals `primitive_shadow_room`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses primitive shadow rooms for missing LINE and Kakao private rooms")
for name in ["line", "kakao"]:
    val decision = plan_transport_operation(chat_adapter_descriptor(name).capabilities,
        TransportOperation.OpenPrivate)
    expect(decision.accepted).to_equal(true)
    expect(decision.execution).to_equal("primitive_shadow_room")
```

</details>


</details>

#### never promotes local Slack cursors to native human read evidence

- never promotes local Slack cursors to native human read evidence
   - Expected: caps.mark_read equals `CapabilityLevel.PrimitiveSidecar`
   - Expected: caps.human_read_receipt equals `CapabilityLevel.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never promotes local Slack cursors to native human read evidence")
val caps = chat_adapter_descriptor("slack").capabilities
expect(caps.mark_read).to_equal(CapabilityLevel.PrimitiveSidecar)
expect(caps.human_read_receipt).to_equal(CapabilityLevel.Unsupported)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret transport capability truth.
- LLM Caret transport capability truth

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d39806214798c612d3f1687c7a4bd04a857ed882f1eea2986ef664605ee94aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d39806214798c612d3f1687c7a4bd04a857ed882f1eea2986ef664605ee94aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d39806214798c612d3f1687c7a4bd04a857ed882f1eea2986ef664605ee94aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/transport_capability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/messaging/transport_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/transport_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes a versioned snapshot for every requested transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses primitive shadow rooms for missing LINE and Kakao private rooms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/transport_capability_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never promotes local Slack cursors to native human read evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
