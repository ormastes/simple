# Claude Full control message compat

> Pure Simple coverage for requestId to request_id compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full control message compat

Pure Simple coverage for requestId to request_id compatibility.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/control_message_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for requestId to request_id compatibility.

## Scenarios

### Claude full control message compat

#### normalizes top-level camelCase request ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes top-level camelCase request ids
- Check top-level requestId
   - Expected: normalized.request_id equals `req-1`
   - Expected: normalized.requestId equals ``
   - Expected: normalized.hasRequestId is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes top-level camelCase request ids")
step("Check top-level requestId")
val normalized = normalizeControlMessageKeys(controlMessage("", "req-1", true, emptyControlMessageResponse(), false))
expect(normalized.request_id).to_equal("req-1")
expect(normalized.requestId).to_equal("")
expect(normalized.hasRequestId).to_equal(false)
```

</details>

#### keeps snake case when both forms are present

- keeps snake case when both forms are present
- Check snake case precedence
   - Expected: normalized.request_id equals `snake`
   - Expected: normalized.requestId equals `camel`
   - Expected: normalized.hasRequestId is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps snake case when both forms are present")
step("Check snake case precedence")
val normalized = normalizeControlMessageKeys(controlMessage("snake", "camel", true, emptyControlMessageResponse(), false))
expect(normalized.request_id).to_equal("snake")
expect(normalized.requestId).to_equal("camel")
expect(normalized.hasRequestId).to_equal(true)
```

</details>

#### normalizes nested response request ids

- normalizes nested response request ids
- Check response requestId
   - Expected: normalized.response.request_id equals `resp-1`
   - Expected: normalized.response.requestId equals ``
   - Expected: normalized.response.hasRequestId is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes nested response request ids")
step("Check response requestId")
val response = controlMessageResponse("", "resp-1", true)
val normalized = normalizeControlMessageKeys(controlMessage("", "", false, response, true))
expect(normalized.response.request_id).to_equal("resp-1")
expect(normalized.response.requestId).to_equal("")
expect(normalized.response.hasRequestId).to_equal(false)
```

</details>

#### keeps nested response snake case when both forms are present

- keeps nested response snake case when both forms are present
- Check response snake case precedence
   - Expected: normalized.response.request_id equals `snake-resp`
   - Expected: normalized.response.requestId equals `camel-resp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps nested response snake case when both forms are present")
step("Check response snake case precedence")
val response = controlMessageResponse("snake-resp", "camel-resp", true)
val normalized = normalizeControlMessageKeys(controlMessage("", "", false, response, true))
expect(normalized.response.request_id).to_equal("snake-resp")
expect(normalized.response.requestId).to_equal("camel-resp")
```

</details>

#### leaves messages without camel case keys unchanged

- leaves messages without camel case keys unchanged
- Check no-op path
   - Expected: normalized.request_id equals `req-2`
   - Expected: normalized.hasResponse is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves messages without camel case keys unchanged")
step("Check no-op path")
val normalized = normalizeControlMessageKeys(controlMessage("req-2", "", false, emptyControlMessageResponse(), false))
expect(normalized.request_id).to_equal("req-2")
expect(normalized.hasResponse).to_equal(false)
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

- Canonical SPipe generation for source `c0f0ea52033f23642deb366a98f3eea06c52e8afd7dda411c1e4401613121637`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0f0ea52033f23642deb366a98f3eea06c52e8afd7dda411c1e4401613121637`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0f0ea52033f23642deb366a98f3eea06c52e8afd7dda411c1e4401613121637`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/control_message_compat_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/control_message_compat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/control_message_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/control_message_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/control_message_compat_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes top-level camelCase request ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/control_message_compat_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps snake case when both forms are present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/control_message_compat_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes nested response request ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
