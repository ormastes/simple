# LLM Caret Claude CLI Stream Contract

> Verifies the llm caret claude cli stream behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Stream Contract

Verifies the llm caret claude cli stream behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret claude cli stream behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret Claude CLI stream contract

### REQ-LLM-CARET-CLI-HARDEN-006: production Claude stream handling

#### should preserve a complete ordered provider stream

- Verify: should preserve a complete ordered provider stream
- Prepare offline Claude CLI fixture
- Stream the provider response
- Check ordered events and redaction
   - Expected: events.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: events[0].event_type equals `system`
   - Expected: events[0].session_id equals `stream-session`
   - Expected: events[1].event_type equals `assistant`
   - Expected: events[1].content equals `streamed fixture`
   - Expected: events[2].event_type equals `result`
   - Expected: events[2].content equals `stream complete`
   - Expected: events[2].output_tokens equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should preserve a complete ordered provider stream")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare offline Claude CLI fixture")
expect(file_exists(MOCK_CLAUDE)).to_be(true)

step("Stream the provider response")
val events = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream", "sonnet", "Be concise", "", 1
)

step("Check ordered events and redaction")
expect(events.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(events[0].event_type).to_equal("system")
expect(events[0].session_id).to_equal("stream-session")
expect(events[1].event_type).to_equal("assistant")
expect(events[1].content).to_equal("streamed fixture")
expect(events[2].event_type).to_equal("result")
expect(events[2].content).to_equal("stream complete")
expect(events[2].output_tokens).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should redact a structured provider error from the stream

- Verify: should redact a structured provider error from the stream
- Prepare offline Claude CLI fixture
- Stream the provider response
- Check ordered events and redaction
   - Expected: events.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should redact a structured provider error from the stream")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare offline Claude CLI fixture")
expect(file_exists(MOCK_CLAUDE)).to_be(true)

step("Stream the provider response")
val events = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-provider-error",
    "sonnet", "", "", 1
)

step("Check ordered events and redaction")
expect(events.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("provider overloaded")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should reject malformed and duplicate-terminal provider streams

- Verify: should reject malformed and duplicate-terminal provider streams
- Prepare offline Claude CLI fixture
- Stream the provider response
- Check ordered events and redaction
   - Expected: malformed.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: malformed[0].event_type equals `error`
   - Expected: malformed[0].stop_reason equals `invalid`
   - Expected: duplicate_terminal.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: duplicate_terminal[0].event_type equals `error`
   - Expected: duplicate_terminal[0].stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should reject malformed and duplicate-terminal provider streams")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(malformed.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(malformed[0].event_type).to_equal("error")
expect(malformed[0].stop_reason).to_equal("invalid")
expect(malformed[0].content).to_contain("invalid JSON")
expect(duplicate_terminal.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06e1117a2c6045465a4d9d4c748394d488d9a59bcb0c1076c90451ac2308e3fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06e1117a2c6045465a4d9d4c748394d488d9a59bcb0c1076c90451ac2308e3fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06e1117a2c6045465a4d9d4c748394d488d9a59bcb0c1076c90451ac2308e3fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a complete ordered provider stream' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should redact a structured provider error from the stream' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_stream_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed and duplicate-terminal provider streams' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
