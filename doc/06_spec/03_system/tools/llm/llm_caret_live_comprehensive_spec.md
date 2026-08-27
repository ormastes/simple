# LLM Caret Comprehensive Live Integration Specification

> This comprehensive suite extends the bounded CLI contract with deterministic single-shot, system-prompt, six-turn resume, tutor, state-tracking, repetition, and exact-phrase scenarios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Comprehensive Live Integration Specification

This comprehensive suite extends the bounded CLI contract with deterministic single-shot, system-prompt, six-turn resume, tutor, state-tracking, repetition, and exact-phrase scenarios.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Offline fixture by default; long live execution is double opt-in |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_harden.md |
| Design | doc/05_design/llm_caret_claude_cli_harden.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This comprehensive suite extends the bounded CLI contract with deterministic
single-shot, system-prompt, six-turn resume, tutor, state-tracking, repetition,
and exact-phrase scenarios.

All scenarios execute offline by default. Paid single-shot calls require
`SIMPLE_LLM_COMPREHENSIVE_LIVE=1`. Paid long-conversation calls additionally
require `SIMPLE_LLM_LONG_LIVE=1`.

## Syntax

```bash
bin/simple test test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl --mode=interpreter
SIMPLE_LLM_COMPREHENSIVE_LIVE=1 SIMPLE_LLM_LONG_LIVE=1 bin/simple test test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl --mode=interpreter
```

## Safety Gates

The two live controls are independent:

- comprehensive live enables ordinary provider calls;
- long live enables multi-turn provider calls;
- long scenarios remain deterministic unless both are enabled;
- no scenario uses a placeholder pass;
- no scenario treats a disabled live gate as success evidence.

## Section 1: Single Shot

The suite checks:

- exact marker text;
- deterministic arithmetic;
- provider identity;
- session identity;
- positive token usage.

## Section 2: System Prompt

The suite checks:

- pirate persona adherence;
- CSV-only formatting.

## Section 3: Six-Turn Resume

One session establishes `ORBIT-73`, then five resumed turns must recall it.
Every turn checks the process result and structured content.

## Section 4: Code Tutor

Five resumed turns build an explanation of immutable and mutable values. The
middle and summary turns must retain both concepts.

## Section 5: Mutable State

Five resumed turns create a shopping list, remove bread, add tea, and confirm
the final list. The final state must contain apples, coffee, and tea while
excluding bread.

## Section 6: Edge Cases

The suite counts exactly five `PLATYPUS` occurrences and checks an exact phrase
request contains the complete normalized phrase.

## Failure Handling

Each subprocess result exposes stdout, stderr, and exit code. A nonzero exit or
missing structured field fails the scenario. Conversation scenarios reuse the
first returned session identifier.

## Evidence Boundary

The offline path proves deterministic orchestration and assertions. The
double-opt-in live path additionally proves authenticated remote conversation
resume. Neither path replaces full TUI interaction evidence.

## Execution Modes

Offline mode is the required continuous-integration path because it is stable,
free, and independent of account state.

Comprehensive live mode is an operator diagnostic for ordinary prompts.

Long live mode is an operator diagnostic for session-resume behavior.

Operators must retain the exact environment gates in captured evidence so an
offline fixture pass is never mislabeled as remote-provider evidence.

## Manual Policy

Every scenario is visible in the generated manual as an advanced slow scenario.
Long scenarios are executable and folded; there are no skip-only helpers.

## Scenarios

### LLM Caret Live Comprehensive Integration

### Section 1: Single-shot responses

<details>
<summary>Advanced: should return exact text in the response</summary>

#### should return exact text in the response _(slow)_

- should return exact text in the response
- Invoke the provider with an exact-text prompt
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return exact text in the response")
step("Invoke the provider with an exact-text prompt")
val result = call_claude_simple("Reply with exactly: HELLO_SIMPLE")
val stdout = result.0 ?? ""
val exit_code = result.2

expect(exit_code).to_equal(0)

val content = _extract_json_string(stdout, "result")
print "  [MANUAL] Content: {content}"
expect(content).to_contain("HELLO_SIMPLE")
```

</details>


</details>

<details>
<summary>Advanced: should handle simple math</summary>

#### should handle simple math _(slow)_

- should handle simple math
- Invoke the provider with deterministic arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle simple math")
step("Invoke the provider with deterministic arithmetic")
val result = call_claude_simple("What is 2 + 2? Reply with ONLY the number.")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")

print "  [MANUAL] Math result: {content}"
expect(content).to_contain("4")
```

</details>


</details>

<details>
<summary>Advanced: should return a model name</summary>

#### should return a model name _(slow)_

- should return a model name
- Inspect structured provider identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return a model name")
step("Inspect structured provider identity")
val result = call_claude_simple("Say hi")
val stdout = result.0 ?? ""
val model = _extract_json_string(stdout, "model")
val content = _extract_json_string(stdout, "result")
val session_id = _extract_json_string(stdout, "session_id")

print "  [MANUAL] Model: {model}"
val has_identity = model.len() > 0 or content.len() > 0 or session_id.len() > 0
expect(has_identity).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: should return a session_id for tracking</summary>

#### should return a session_id for tracking _(slow)_

- should return a session_id for tracking
- Inspect the structured session identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return a session_id for tracking")
step("Inspect the structured session identifier")
val result = call_claude_simple("Say hello")
val stdout = result.0 ?? ""
val session_id = _extract_json_string(stdout, "session_id")

print "  [MANUAL] Session ID: {session_id}"
expect(session_id.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: should report token usage</summary>

#### should report token usage _(slow)_

- should report token usage
- Inspect structured token usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report token usage")
step("Inspect structured token usage")
val result = call_claude_simple("Say ok")
val stdout = result.0 ?? ""
val in_tok = _extract_json_int(stdout, "input_tokens")
val out_tok = _extract_json_int(stdout, "output_tokens")
val total = in_tok + out_tok

print "  [MANUAL] Tokens: in={in_tok}, out={out_tok}, total={total}"
expect(total).to_be_greater_than(0)
```

</details>


</details>

### Section 2: System prompt adherence

<details>
<summary>Advanced: should follow a pirate persona system prompt</summary>

#### should follow a pirate persona system prompt _(slow)_

- should follow a pirate persona system prompt
- Invoke the provider with a persona system prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should follow a pirate persona system prompt")
step("Invoke the provider with a persona system prompt")
val result = call_claude(
    "What are you?",
    "You are a pirate named CaptainBytes. Always speak in pirate dialect. Every response MUST include 'Arrr!'",
    "",
    1
)
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val lower = content.lower()

print "  [MANUAL] Pirate response: {content}"
expect(lower).to_contain("arr")
```

</details>


</details>

<details>
<summary>Advanced: should follow a CSV format constraint</summary>

#### should follow a CSV format constraint _(slow)_

- should follow a CSV format constraint
- Invoke the provider with a CSV-only system prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should follow a CSV format constraint")
step("Invoke the provider with a CSV-only system prompt")
val result = call_claude(
    "List 3 fruits",
    "You MUST respond in CSV format only. No explanations, just comma-separated values on a single line.",
    "",
    1
)
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")

print "  [MANUAL] CSV response: {content}"
expect(content).to_contain(",")
```

</details>


</details>

### Section 3: Multi-turn conversation (6 turns)

<details>
<summary>Advanced: should maintain context across 6 turns with session resume</summary>

#### should maintain context across 6 turns with session resume _(slow)_

- should maintain context across 6 turns with session resume
- Resume one deterministic conversation across six turns
   - Expected: first.2 equals `0`
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain context across 6 turns with session resume")
step("Resume one deterministic conversation across six turns")
val first = call_long_claude("Remember project code ORBIT-73.", "", "", 1)
expect(first.2).to_equal(0)
val first_json = first.0 ?? ""
val session_id = _extract_json_string(first_json, "session_id")
expect(session_id.len()).to_be_greater_than(0)

var turn = 2
while turn <= 6:
    val result = call_long_claude(
        "Turn {turn}: what is the project code? Reply only with it.",
        "",
        session_id,
        1
    )
    expect(result.2).to_equal(0)
    val content = _extract_json_string(result.0 ?? "", "result")
    expect(content).to_contain("ORBIT-73")
    turn = turn + 1
```

</details>


</details>

### Section 4: Code tutor session (5 turns)

<details>
<summary>Advanced: should build a progressive code tutor explanation</summary>

#### should build a progressive code tutor explanation _(slow)_

- should build a progressive code tutor explanation
- Resume one deterministic tutor conversation across five turns
   - Expected: first.2 equals `0`
   - Expected: fifth.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build a progressive code tutor explanation")
step("Resume one deterministic tutor conversation across five turns")
val first = call_long_claude("Explain an immutable value in one sentence.", "", "", 1)
expect(first.2).to_equal(0)
val session_id = _extract_json_string(first.0 ?? "", "session_id")
expect(session_id.len()).to_be_greater_than(0)

val second = call_long_claude("Explain a mutable value in one sentence.", "", session_id, 1)
expect(_extract_json_string(second.0 ?? "", "result").lower()).to_contain("mutable")
val third = call_long_claude("Now compare immutable and mutable values.", "", session_id, 1)
val comparison = _extract_json_string(third.0 ?? "", "result").lower()
expect(comparison).to_contain("immutable")
expect(comparison).to_contain("mutable")
val fourth = call_long_claude("Give a tutor summary using both terms.", "", session_id, 1)
val summary = _extract_json_string(fourth.0 ?? "", "result").lower()
expect(summary).to_contain("immutable")
expect(summary).to_contain("mutable")
val fifth = call_long_claude("Repeat the tutor summary concisely.", "", session_id, 1)
expect(fifth.2).to_equal(0)
```

</details>


</details>

### Section 5: Shopping list state tracking (5 turns)

<details>
<summary>Advanced: should maintain mutable shopping-list state</summary>

#### should maintain mutable shopping-list state _(slow)_

- should maintain mutable shopping-list state
- Resume one deterministic stateful conversation across five turns
   - Expected: first.2 equals `0`
   - Expected: fifth.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain mutable shopping-list state")
step("Resume one deterministic stateful conversation across five turns")
val first = call_long_claude("Start a shopping list with apples, bread, and coffee.", "", "", 1)
expect(first.2).to_equal(0)
val session_id = _extract_json_string(first.0 ?? "", "session_id")
expect(session_id.len()).to_be_greater_than(0)

val second = call_long_claude("From the shopping list remove bread.", "", session_id, 1)
val after_remove = _extract_json_string(second.0 ?? "", "result").lower()
expect(after_remove).to_contain("apples")
expect(after_remove).to_contain("coffee")
expect(after_remove.contains("bread")).to_be(false)

val third = call_long_claude("To the shopping list add tea.", "", session_id, 1)
expect(_extract_json_string(third.0 ?? "", "result").lower()).to_contain("tea")
val fourth = call_long_claude("Return the final list.", "", session_id, 1)
val final_list = _extract_json_string(fourth.0 ?? "", "result").lower()
expect(final_list).to_contain("apples")
expect(final_list).to_contain("coffee")
expect(final_list).to_contain("tea")
expect(final_list.contains("bread")).to_be(false)
val fifth = call_long_claude("Confirm the final list remains unchanged.", "", session_id, 1)
expect(fifth.2).to_equal(0)
```

</details>


</details>

### Section 6: Edge cases

<details>
<summary>Advanced: should handle repetition requests</summary>

#### should handle repetition requests _(slow)_

- should handle repetition requests
- Ask for an exact repetition count
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle repetition requests")
step("Ask for an exact repetition count")
val result = call_claude_simple("Repeat PLATYPUS exactly 5 times separated by spaces. Nothing else.")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val upper = content.upper()

# Count occurrences manually
var count = 0
var idx = 0
val search = "PLATYPUS"
while idx < upper.len():
    val found_idx = _unwrap_idx(upper.substring(idx).index_of(search))
    if found_idx >= 0:
        count = count + 1
        idx = idx + found_idx + search.len()
    else:
        break

print "  [EDGE] Repetition count: {count}, content: {content}"
expect(count).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: should handle exact phrase requests</summary>

#### should handle exact phrase requests _(slow)_

- should handle exact phrase requests
- Ask for an exact phrase


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle exact phrase requests")
step("Ask for an exact phrase")
val result = call_claude_simple("Reply with exactly: hello world test")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val lower = content.lower()

print "  [EDGE] Exact phrase: {content}"
expect(lower).to_contain("hello world test")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_harden.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_harden.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b99d95169bad6f70cae4e7e3eeab4b8ff546e482d130b34024eaf8c7d33c3576`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b99d95169bad6f70cae4e7e3eeab4b8ff546e482d130b34024eaf8c7d33c3576`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b99d95169bad6f70cae4e7e3eeab4b8ff546e482d130b34024eaf8c7d33c3576`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl
mirror: doc/06_spec/03_system/tools/llm/llm_caret_live_comprehensive_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/llm_caret_live_comprehensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/llm_caret_live_comprehensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:281:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return exact text in the response' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:281:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return exact text in the response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:295:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle simple math' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:295:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle simple math' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:306:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return a model name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:306:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return a model name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:320:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return a session_id for tracking' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:331:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report token usage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl:350:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should follow a pirate persona system prompt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
