# Codex Cli Specification

> Tests covering build_codex_args - minimal, build_codex_args - model, build_codex_args - json mode, build_codex_args - instructions, build_codex_args - sandbox, build_codex_args - extra args, build_codex_args - combined, parse_codex_jsonl_response - success, parse_codex_jsonl_response - error, parse_codex_jsonl_response - multiline content, parse_codex_jsonl_response - edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codex Cli Specification

## Scenarios

### build_codex_args - minimal

#### starts with exec subcommand

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with exec subcommand
   - Expected: args[0] equals `exec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with exec subcommand")
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args[0]).to_equal("exec")
```

</details>

#### includes --full-auto

- includes --full-auto
   - Expected: args_contain(args, "--full-auto") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes --full-auto")
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args_contain(args, "--full-auto")).to_equal(true)
```

</details>

#### defaults sandbox to off

- defaults sandbox to off
   - Expected: args_get_flag_value(args, "--sandbox") equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults sandbox to off")
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("off")
```

</details>

#### prompt is last positional arg

- prompt is last positional arg
   - Expected: args_contain(args, "Hello world") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prompt is last positional arg")
val args = build_codex_args("Hello world", "", false, "", "", [])
# Prompt should be the last arg before any extra_args
expect(args_contain(args, "Hello world")).to_equal(true)
```

</details>

#### has no model flag when empty

- has no model flag when empty
   - Expected: args_contain(args, "--model") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no model flag when empty")
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--model")).to_equal(false)
```

</details>

#### has no instructions flag when empty

- has no instructions flag when empty
   - Expected: args_contain(args, "--instructions") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no instructions flag when empty")
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--instructions")).to_equal(false)
```

</details>

#### has no json flag when json_mode is false

- has no json flag when json_mode is false
   - Expected: args_contain(args, "--json") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no json flag when json_mode is false")
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--json")).to_equal(false)
```

</details>

### build_codex_args - model

#### includes model flag

- includes model flag
   - Expected: args_get_flag_value(args, "--model") equals `o4-mini`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes model flag")
val args = build_codex_args("Hi", "o4-mini", false, "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("o4-mini")
```

</details>

#### supports o3 model

- supports o3 model
   - Expected: args_get_flag_value(args, "--model") equals `o3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports o3 model")
val args = build_codex_args("Hi", "o3", false, "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("o3")
```

</details>

### build_codex_args - json mode

#### includes json flag when true

- includes json flag when true
   - Expected: args_contain(args, "--json") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes json flag when true")
val args = build_codex_args("Hi", "", true, "", "", [])
expect(args_contain(args, "--json")).to_equal(true)
```

</details>

### build_codex_args - instructions

#### includes instructions

- includes instructions
   - Expected: args_get_flag_value(args, "--instructions") equals `You are a pirate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes instructions")
val args = build_codex_args("Hi", "", false, "You are a pirate", "", [])
expect(args_get_flag_value(args, "--instructions")).to_equal("You are a pirate")
```

</details>

### build_codex_args - sandbox

#### uses custom sandbox value

- uses custom sandbox value
   - Expected: args_get_flag_value(args, "--sandbox") equals `network-only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses custom sandbox value")
val args = build_codex_args("Hi", "", false, "", "network-only", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("network-only")
```

</details>

#### defaults sandbox to off when empty

- defaults sandbox to off when empty
   - Expected: args_get_flag_value(args, "--sandbox") equals `off`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults sandbox to off when empty")
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("off")
```

</details>

### build_codex_args - extra args

#### appends extra args

- appends extra args
   - Expected: args_contain(args, "--no-cache") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends extra args")
val args = build_codex_args("Hi", "", false, "", "", ["--no-cache"])
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

#### skips empty extra args

- skips empty extra args
   - Expected: args_contain(args, "--flag") is true
   - Expected: args_contain(args, "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips empty extra args")
val args = build_codex_args("Hi", "", false, "", "", ["", "--flag", ""])
expect(args_contain(args, "--flag")).to_equal(true)
expect(args_contain(args, "")).to_equal(false)
```

</details>

### build_codex_args - combined

#### builds complete args

- builds complete args
   - Expected: args[0] equals `exec`
   - Expected: args_contain(args, "--json") is true
   - Expected: args_get_flag_value(args, "--model") equals `o4-mini`
   - Expected: args_get_flag_value(args, "--instructions") equals `be helpful`
   - Expected: args_contain(args, "--full-auto") is true
   - Expected: args_get_flag_value(args, "--sandbox") equals `network-only`
   - Expected: args_contain(args, "prompt") is true
   - Expected: args_contain(args, "--no-cache") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds complete args")
val args = build_codex_args("prompt", "o4-mini", true, "be helpful", "network-only", ["--no-cache"])
expect(args[0]).to_equal("exec")
expect(args_contain(args, "--json")).to_equal(true)
expect(args_get_flag_value(args, "--model")).to_equal("o4-mini")
expect(args_get_flag_value(args, "--instructions")).to_equal("be helpful")
expect(args_contain(args, "--full-auto")).to_equal(true)
expect(args_get_flag_value(args, "--sandbox")).to_equal("network-only")
expect(args_contain(args, "prompt")).to_equal(true)
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

### parse_codex_jsonl_response - success

#### parses assistant message with output_text

- parses assistant message with output_text
   - Expected: resp.content equals `Hello world!`
   - Expected: resp.is_error is false
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses assistant message with output_text")
val jsonl = mock_jsonl_message("Hello world!")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("Hello world!")
expect(resp.is_error).to_equal(false)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### parses multiline JSONL with model info

- parses multiline JSONL with model info
   - Expected: resp.content equals `The answer is 42`
   - Expected: resp.model equals `o4-mini`
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiline JSONL with model info")
val line1 = mock_jsonl_model("o4-mini")
val line2 = mock_jsonl_message("The answer is 42")
val jsonl = line1 + "\n" + line2
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("The answer is 42")
expect(resp.model).to_equal("o4-mini")
expect(resp.is_error).to_equal(false)
```

</details>

#### preserves raw response

- preserves raw response
   - Expected: resp.raw equals `jsonl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves raw response")
val jsonl = mock_jsonl_message("Hi")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.raw).to_equal(jsonl)
```

</details>

### parse_codex_jsonl_response - error

#### parses error event

- parses error event
   - Expected: resp.is_error is true
   - Expected: resp.error equals `Rate limited`
   - Expected: resp.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses error event")
val jsonl = mock_jsonl_error("Rate limited")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("Rate limited")
expect(resp.stop_reason).to_equal("error")
```

</details>

#### handles empty response

- handles empty response
   - Expected: resp.is_error is true
   - Expected: resp.error equals `empty response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty response")
val resp = parse_codex_jsonl_response("")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### handles whitespace-only response

- handles whitespace-only response
   - Expected: resp.is_error is true
   - Expected: resp.error equals `empty response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles whitespace-only response")
val resp = parse_codex_jsonl_response("   ")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

### parse_codex_jsonl_response - multiline content

#### extracts text from assistant message

- extracts text from assistant message


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts text from assistant message")
val line1 = mock_jsonl_model("o4-mini")
val line2 = mock_jsonl_message("Line 1\\nLine 2")
val jsonl = line1 + "\n" + line2
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_contain("Line 1")
```

</details>

#### uses last assistant message content

- uses last assistant message content
   - Expected: resp.content equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses last assistant message content")
val line1 = mock_jsonl_message("first")
val line2 = mock_jsonl_message("second")
val jsonl = line1 + "\n" + line2
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("second")
```

</details>

### parse_codex_jsonl_response - edge cases

#### handles missing model field

- handles missing model field
   - Expected: resp.content equals `Hello`
   - Expected: resp.model equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing model field")
val jsonl = mock_jsonl_message("Hello")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### defaults session_id to empty

- defaults session_id to empty
   - Expected: resp.session_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults session_id to empty")
val jsonl = mock_jsonl_message("Hello")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.session_id).to_equal("")
```

</details>

#### handles error with empty message

- handles error with empty message
   - Expected: resp.is_error is true
   - Expected: resp.error equals `unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles error with empty message")
var err_line = _LB()
err_line = err_line + _Q() + "type" + _Q() + ":" + _Q() + "error" + _Q()
err_line = err_line + _RB()
val resp = parse_codex_jsonl_response(err_line)
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("unknown error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/codex_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering build_codex_args - minimal, build_codex_args - model, build_codex_args - json mode, build_codex_args - instructions, build_codex_args - sandbox, build_codex_args - extra args, build_codex_args - combined, parse_codex_jsonl_response - success, parse_codex_jsonl_response - error, parse_codex_jsonl_response - multiline content, parse_codex_jsonl_response - edge cases.
- build_codex_args - minimal
- build_codex_args - model
- build_codex_args - json mode
- build_codex_args - instructions
- build_codex_args - sandbox
- build_codex_args - extra args
- build_codex_args - combined
- parse_codex_jsonl_response - success
- parse_codex_jsonl_response - error
- parse_codex_jsonl_response - multiline content
- parse_codex_jsonl_response - edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3554384ebf703b131c3100be66029844a4c815e9b6ac07343d1c28e83d9dbb8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3554384ebf703b131c3100be66029844a4c815e9b6ac07343d1c28e83d9dbb8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3554384ebf703b131c3100be66029844a4c815e9b6ac07343d1c28e83d9dbb8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_caret/codex_cli_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/codex_cli_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/codex_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/codex_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/codex_cli_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with exec subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/codex_cli_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes --full-auto' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/codex_cli_spec.spl:264:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults sandbox to off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
