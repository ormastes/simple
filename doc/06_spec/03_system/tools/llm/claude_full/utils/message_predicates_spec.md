# Claude Full Message Predicates

> Pure Simple coverage for message predicate parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Message Predicates

Pure Simple coverage for message predicate parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/message_predicates_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for message predicate parity.

## Scenarios

### Claude full message predicates

#### accepts visible user messages as human turns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts visible user messages as human turns
- Check human user message
   - Expected: isHumanTurn(message) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts visible user messages as human turns")
step("Check human user message")
val message = PredicateMessage(typeName: "user", isMeta: false, hasToolUseResult: false)
expect(isHumanTurn(message)).to_equal(true)
```

</details>

#### rejects assistant messages

- rejects assistant messages
- Check non-user message
   - Expected: isHumanTurn(message) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects assistant messages")
step("Check non-user message")
val message = PredicateMessage(typeName: "assistant", isMeta: false, hasToolUseResult: false)
expect(isHumanTurn(message)).to_equal(false)
```

</details>

#### rejects meta user messages

- rejects meta user messages
- Check meta user message
   - Expected: isHumanTurn(message) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects meta user messages")
step("Check meta user message")
val message = PredicateMessage(typeName: "user", isMeta: true, hasToolUseResult: false)
expect(isHumanTurn(message)).to_equal(false)
```

</details>

#### rejects user tool result messages

- rejects user tool result messages
- Check tool result user message
   - Expected: isHumanTurn(message) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects user tool result messages")
step("Check tool result user message")
val message = PredicateMessage(typeName: "user", isMeta: false, hasToolUseResult: true)
expect(isHumanTurn(message)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a02d5271941fa94352d74c8672d2d8f0ad46cc2259fa4ce4e4cecf3bfaa67b52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a02d5271941fa94352d74c8672d2d8f0ad46cc2259fa4ce4e4cecf3bfaa67b52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a02d5271941fa94352d74c8672d2d8f0ad46cc2259fa4ce4e4cecf3bfaa67b52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/message_predicates_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/message_predicates_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/message_predicates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/message_predicates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/message_predicates_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts visible user messages as human turns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/message_predicates_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects assistant messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/message_predicates_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects meta user messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
