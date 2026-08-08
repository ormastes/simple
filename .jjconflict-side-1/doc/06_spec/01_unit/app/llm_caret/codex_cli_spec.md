# Codex Cli Specification

> <details>

<!-- sdn-diagram:id=codex_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=codex_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codex_cli_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=codex_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codex Cli Specification

## Scenarios

### build_codex_args - minimal

#### starts with exec subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args[0]).to_equal("exec")
```

</details>

#### includes --full-auto

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args_contain(args, "--full-auto")).to_equal(true)
```

</details>

#### defaults sandbox to off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hello", "", false, "", "", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("off")
```

</details>

#### prompt is last positional arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hello world", "", false, "", "", [])
# Prompt should be the last arg before any extra_args
expect(args_contain(args, "Hello world")).to_equal(true)
```

</details>

#### has no model flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--model")).to_equal(false)
```

</details>

#### has no instructions flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--instructions")).to_equal(false)
```

</details>

#### has no json flag when json_mode is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_contain(args, "--json")).to_equal(false)
```

</details>

### build_codex_args - model

#### includes model flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "o4-mini", false, "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("o4-mini")
```

</details>

#### supports o3 model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "o3", false, "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("o3")
```

</details>

### build_codex_args - json mode

#### includes json flag when true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", true, "", "", [])
expect(args_contain(args, "--json")).to_equal(true)
```

</details>

### build_codex_args - instructions

#### includes instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "You are a pirate", "", [])
expect(args_get_flag_value(args, "--instructions")).to_equal("You are a pirate")
```

</details>

### build_codex_args - sandbox

#### uses custom sandbox value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "network-only", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("network-only")
```

</details>

#### defaults sandbox to off when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", [])
expect(args_get_flag_value(args, "--sandbox")).to_equal("off")
```

</details>

### build_codex_args - extra args

#### appends extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", ["--no-cache"])
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

#### skips empty extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_codex_args("Hi", "", false, "", "", ["", "--flag", ""])
expect(args_contain(args, "--flag")).to_equal(true)
expect(args_contain(args, "")).to_equal(false)
```

</details>

### build_codex_args - combined

#### builds complete args

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = mock_jsonl_message("Hello world!")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("Hello world!")
expect(resp.is_error).to_equal(false)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### parses multiline JSONL with model info

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = mock_jsonl_message("Hi")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.raw).to_equal(jsonl)
```

</details>

### parse_codex_jsonl_response - error

#### parses error event

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = mock_jsonl_error("Rate limited")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("Rate limited")
expect(resp.stop_reason).to_equal("error")
```

</details>

#### handles empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_codex_jsonl_response("")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### handles whitespace-only response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_codex_jsonl_response("   ")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

### parse_codex_jsonl_response - multiline content

#### extracts text from assistant message

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line1 = mock_jsonl_model("o4-mini")
val line2 = mock_jsonl_message("Line 1\\nLine 2")
val jsonl = line1 + "\n" + line2
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_contain("Line 1")
```

</details>

#### uses last assistant message content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line1 = mock_jsonl_message("first")
val line2 = mock_jsonl_message("second")
val jsonl = line1 + "\n" + line2
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("second")
```

</details>

### parse_codex_jsonl_response - edge cases

#### handles missing model field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = mock_jsonl_message("Hello")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### defaults session_id to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jsonl = mock_jsonl_message("Hello")
val resp = parse_codex_jsonl_response(jsonl)
expect(resp.session_id).to_equal("")
```

</details>

#### handles error with empty message

1. var err line =  LB
2. err line = err line +  Q
3. err line = err line +  RB
   - Expected: resp.is_error is true
   - Expected: resp.error equals `unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/llm_caret/codex_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
