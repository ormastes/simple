# LLM Caret Claude CLI Stream Contract

> This deterministic offline contract invokes the production

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Stream Contract

This deterministic offline contract invokes the production

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

This deterministic offline contract invokes the production
`claude_cli_stream` function through the maintained Claude CLI fixture. It
proves ordered stream-envelope handling, redaction of a structured provider
error, and fail-closed rejection of malformed or duplicate-terminal NDJSON.

It does not invoke `bin/caret`, a cached Caret artifact, an installed Claude
binary, authentication, or a network provider. The cached CLI and PTY specs
own those process and terminal acceptance boundaries.

## Scenarios

### LLM Caret Claude CLI stream contract

### REQ-LLM-CARET-CLI-HARDEN-006: production Claude stream handling

#### should preserve a complete ordered provider stream
#### should redact a structured provider error from the stream

- should redact a structured provider error from the stream
- Prepare offline Claude CLI fixture
- Stream the provider response
- Check ordered events and redaction
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should redact a structured provider error from the stream")
step("Prepare offline Claude CLI fixture")
expect(file_exists(MOCK_CLAUDE)).to_be(true)

step("Stream the provider response")
val events = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-provider-error",
    "sonnet", "", "", 1
)

step("Check ordered events and redaction")
expect(events.len()).to_equal(1)
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("provider overloaded")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should reject malformed and duplicate-terminal provider streams

- should reject malformed and duplicate-terminal provider streams
- Prepare offline Claude CLI fixture
- Stream the provider response
- Check ordered events and redaction
   - Expected: malformed.len() equals `1`
   - Expected: malformed[0].event_type equals `error`
   - Expected: malformed[0].stop_reason equals `invalid`
   - Expected: duplicate_terminal.len() equals `1`
   - Expected: duplicate_terminal[0].event_type equals `error`
   - Expected: duplicate_terminal[0].stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed and duplicate-terminal provider streams")
step("Prepare offline Claude CLI fixture")
expect(file_exists(MOCK_CLAUDE)).to_be(true)

step("Stream the provider response")
val malformed = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-malformed-then-result",
    "sonnet", "", "", 1
)
val duplicate_terminal = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-duplicate-terminal",
    "sonnet", "", "", 1
)

step("Check ordered events and redaction")
expect(malformed.len()).to_equal(1)
expect(malformed[0].event_type).to_equal("error")
expect(malformed[0].stop_reason).to_equal("invalid")
expect(malformed[0].content).to_contain("invalid JSON")
expect(duplicate_terminal.len()).to_equal(1)
expect(duplicate_terminal[0].event_type).to_equal("error")
expect(duplicate_terminal[0].stop_reason).to_equal("invalid")
expect(duplicate_terminal[0].content).to_contain("after a terminal")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-CLI-HARDEN-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e00f766d39c6b34c3d240fb60e0fe06af782872244c593958c24a80c204c270b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e00f766d39c6b34c3d240fb60e0fe06af782872244c593958c24a80c204c270b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e00f766d39c6b34c3d240fb60e0fe06af782872244c593958c24a80c204c270b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=75 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should preserve a complete ordered provider stream' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a complete ordered provider stream' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should redact a structured provider error from the stream' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should redact a structured provider error from the stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed and duplicate-terminal provider streams' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed and duplicate-terminal provider streams' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
