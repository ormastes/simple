# Claude Full direct member message

> Pure Simple coverage for direct team member message parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full direct member message

Pure Simple coverage for direct team member message parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/direct_member_message_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for direct team member message parsing.

## Scenarios

### Claude full direct member message

#### parses recipient and trimmed message

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses recipient and trimmed message
- Check direct message parse
   - Expected: parsed.recipient_name equals `alice`
   - Expected: parsed.message equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses recipient and trimmed message")
step("Check direct message parse")
val parsed = parse_direct_member_message("@alice   hello world  ")
expect(parsed.recipient_name).to_equal("alice")
expect(parsed.message).to_equal("hello world")
```

</details>

#### allows hyphens underscores and digits in recipient names

- allows hyphens underscores and digits in recipient names
- Check recipient charset
   - Expected: parsed.recipient_name equals `team-lead_2`
   - Expected: parsed.message equals `status update`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows hyphens underscores and digits in recipient names")
step("Check recipient charset")
val parsed = parse_direct_member_message("@team-lead_2\tstatus update")
expect(parsed.recipient_name).to_equal("team-lead_2")
expect(parsed.message).to_equal("status update")
```

</details>

#### accepts multiline payloads

- accepts multiline payloads
- Check multiline payload
   - Expected: parsed.message equals `hello there`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts multiline payloads")
step("Check multiline payload")
val parsed = parse_direct_member_message("@alice\nhello there")
expect(parsed.message).to_equal("hello there")
```

</details>

#### accepts regex whitespace separators

- accepts regex whitespace separators
- Check JS whitespace parity
   - Expected: parse_direct_member_message("@alice\u000Chello").message equals `hello`
   - Expected: parse_direct_member_message("@alice" + char_from_code(11) + "hello").message equals `hello`
   - Expected: parse_direct_member_message("@alice " + char_from_code(11) + " hello").message equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts regex whitespace separators")
step("Check JS whitespace parity")
expect(parse_direct_member_message("@alice\u000Chello").message).to_equal("hello")
expect(parse_direct_member_message("@alice" + char_from_code(11) + "hello").message).to_equal("hello")
expect(parse_direct_member_message("@alice " + char_from_code(11) + " hello").message).to_equal("hello")
```

</details>

#### rejects input without direct mention prefix

- rejects input without direct mention prefix
- Check missing prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects input without direct mention prefix")
step("Check missing prefix")
expect(parse_direct_member_message("agent hello")).to_be_nil()
```

</details>

#### rejects malformed or empty messages

- rejects malformed or empty messages
- Check invalid forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects malformed or empty messages")
step("Check invalid forms")
expect(parse_direct_member_message("@ hello")).to_be_nil()
expect(parse_direct_member_message("@agent.name hello")).to_be_nil()
expect(parse_direct_member_message("@alice   ")).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d74351d883ea0d93b78f2c72e6cf6f134ea4fa67ed947c6562ed1e002bd4b636`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d74351d883ea0d93b78f2c72e6cf6f134ea4fa67ed947c6562ed1e002bd4b636`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d74351d883ea0d93b78f2c72e6cf6f134ea4fa67ed947c6562ed1e002bd4b636`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/direct_member_message_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/direct_member_message_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/direct_member_message_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/direct_member_message_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/direct_member_message_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses recipient and trimmed message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/direct_member_message_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows hyphens underscores and digits in recipient names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/direct_member_message_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts multiline payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
