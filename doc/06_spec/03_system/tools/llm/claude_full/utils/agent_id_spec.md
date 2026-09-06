# Claude Full agent ID utils

> Pure Simple coverage for deterministic agent and request IDs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full agent ID utils

Pure Simple coverage for deterministic agent and request IDs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for deterministic agent and request IDs.

## Scenarios

### Claude full agent ID utils

#### formats and parses agent ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats and parses agent ids
- Check agent id round trip
   - Expected: id equals `researcher@my-project`
   - Expected: parsed.valid is true
   - Expected: parsed.agentName equals `researcher`
   - Expected: parsed.teamName equals `my-project`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats and parses agent ids")
step("Check agent id round trip")
val id = formatAgentId("researcher", "my-project")
val parsed = parseAgentId(id)
expect(id).to_equal("researcher@my-project")
expect(parsed.valid).to_equal(true)
expect(parsed.agentName).to_equal("researcher")
expect(parsed.teamName).to_equal("my-project")
```

</details>

#### rejects agent ids without a separator

- rejects agent ids without a separator
- Check invalid agent id
   - Expected: parseAgentId("researcher").valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects agent ids without a separator")
step("Check invalid agent id")
expect(parseAgentId("researcher").valid).to_equal(false)
```

</details>

#### generates and parses request ids

- generates and parses request ids
- Check request id round trip
   - Expected: id equals `shutdown-1702500000000@researcher@my-project`
   - Expected: parsed.valid is true
   - Expected: parsed.requestType equals `shutdown`
   - Expected: parsed.timestamp equals `1702500000000`
   - Expected: parsed.agentId equals `researcher@my-project`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates and parses request ids")
step("Check request id round trip")
val id = generateRequestId("shutdown", 1702500000000, "researcher@my-project")
val parsed = parseRequestId(id)
expect(id).to_equal("shutdown-1702500000000@researcher@my-project")
expect(parsed.valid).to_equal(true)
expect(parsed.requestType).to_equal("shutdown")
expect(parsed.timestamp).to_equal(1702500000000)
expect(parsed.agentId).to_equal("researcher@my-project")
```

</details>

#### parses dashed request types with the last dash

- parses dashed request types with the last dash
- Check dashed request type
   - Expected: parsed.valid is true
   - Expected: parsed.requestType equals `plan-approval`
   - Expected: parsed.timestamp equals `123`
   - Expected: parsed.agentId equals `lead@team`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses dashed request types with the last dash")
step("Check dashed request type")
val parsed = parseRequestId("plan-approval-123@lead@team")
expect(parsed.valid).to_equal(true)
expect(parsed.requestType).to_equal("plan-approval")
expect(parsed.timestamp).to_equal(123)
expect(parsed.agentId).to_equal("lead@team")
```

</details>

#### rejects malformed request ids

- rejects malformed request ids
- Check invalid request ids
   - Expected: parseRequestId("shutdown-123").valid is false
   - Expected: parseRequestId("shutdown@agent@team").valid is false
   - Expected: parseRequestId("shutdown-nope@agent@team").valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects malformed request ids")
step("Check invalid request ids")
expect(parseRequestId("shutdown-123").valid).to_equal(false)
expect(parseRequestId("shutdown@agent@team").valid).to_equal(false)
expect(parseRequestId("shutdown-nope@agent@team").valid).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aed2942642fce58049397e16a268bf4336c062d3f831ffe8c3efae63c985a28d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aed2942642fce58049397e16a268bf4336c062d3f831ffe8c3efae63c985a28d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aed2942642fce58049397e16a268bf4336c062d3f831ffe8c3efae63c985a28d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/agent_id_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/agent_id_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/agent_id_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats and parses agent ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects agent ids without a separator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/agent_id_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates and parses request ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
