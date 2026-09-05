# config_spec

> Messaging configuration uses typed SDN and secret references.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# config_spec

Messaging configuration uses typed SDN and secret references.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Messaging configuration uses typed SDN and secret references.

## Scenarios

### LLM Caret messaging SDN configuration

<details>
<summary>Advanced: decodes server, agent, room, and transport maps</summary>

#### decodes server, agent, room, and transport maps

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes server, agent, room, and transport maps


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes server, agent, room, and transport maps")
val config = decode_messaging_config("""
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-006`
- `REQ-LLM-MSG-013`
- `REQ-LLM-MSG-016`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cda3f3a36751e3006a7177e62609d9c20fae870bfb7052d2a95c8f982df75c8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cda3f3a36751e3006a7177e62609d9c20fae870bfb7052d2a95c8f982df75c8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cda3f3a36751e3006a7177e62609d9c20fae870bfb7052d2a95c8f982df75c8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/config_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/config_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/config_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/config_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes server, agent, room, and transport maps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/config_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects raw transport tokens and unsafe listeners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
