# Minimal Arg Building

> Tests that build_gemini_args produces correct args with minimal input.

<!-- sdn-diagram:id=gemini_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gemini_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gemini_cli_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gemini_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Minimal Arg Building

Tests that build_gemini_args produces correct args with minimal input.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/gemini_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that build_gemini_args produces correct args with minimal input.

## Scenarios

### build_gemini_args - minimal

#### includes prompt with -p flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hello", "", "", "", [])
expect(args_contain(args, "-p")).to_equal(true)
expect(args_get_flag_value(args, "-p")).to_equal("Hello")
```

</details>

#### defaults to json output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
```

</details>

#### has no model flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_contain(args, "--model")).to_equal(false)
```

</details>

#### has no resume flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_contain(args, "--resume")).to_equal(false)
```

</details>

### build_gemini_args - model

#### includes model flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "gemini-2.5-pro", "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("gemini-2.5-pro")
```

</details>

#### supports flash model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "gemini-2.5-flash", "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("gemini-2.5-flash")
```

</details>

### build_gemini_args - output format

#### uses custom output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "text", "", [])
expect(args_get_flag_value(args, "--output-format")).to_equal("text")
```

</details>

### build_gemini_args - session

#### includes session resume

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "abc-123", [])
expect(args_get_flag_value(args, "--resume")).to_equal("abc-123")
```

</details>

### build_gemini_args - extra args

#### appends extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "", ["--no-cache"])
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

#### skips empty extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("Hi", "", "", "", ["", "--flag", ""])
expect(args_contain(args, "--flag")).to_equal(true)
expect(args_contain(args, "")).to_equal(false)
```

</details>

### build_gemini_args - combined

#### builds complete args

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_gemini_args("prompt", "gemini-2.5-pro", "json", "sess-1", ["--sandbox"])
expect(args_get_flag_value(args, "-p")).to_equal("prompt")
expect(args_get_flag_value(args, "--model")).to_equal("gemini-2.5-pro")
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
expect(args_get_flag_value(args, "--resume")).to_equal("sess-1")
expect(args_contain(args, "--sandbox")).to_equal(true)
```

</details>

### parse_gemini_json_response - success

#### parses successful response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hello world!", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.is_error).to_equal(false)
```

</details>

#### parses model field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "gemini-2.5-flash")
val resp = parse_gemini_json_response(json)
expect(resp.model).to_equal("gemini-2.5-flash")
```

</details>

#### parses stop reason as end_turn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### preserves raw json

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.raw).to_equal(json)
```

</details>

#### session_id is always empty for gemini

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.session_id).to_equal("")
```

</details>

### parse_gemini_json_response - tokens

#### parses token counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json_with_tokens("Hi", 300, 75)
val resp = parse_gemini_json_response(json)
expect(resp.input_tokens).to_equal(300)
expect(resp.output_tokens).to_equal(75)
```

</details>

### parse_gemini_json_response - error

#### parses error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_error_json("Rate limited")
val resp = parse_gemini_json_response(json)
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
val resp = parse_gemini_json_response("")
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
val resp = parse_gemini_json_response("   ")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

### parse_gemini_json_response - edge cases

#### handles missing model field

1. var json =  LB
2. json = json +  Q
3. json = json +  RB
   - Expected: resp.content equals `Hello`
   - Expected: resp.model equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var json = _LB()
json = json + _Q() + "response" + _Q() + ":" + _Q() + "Hello" + _Q()
json = json + _RB()
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### handles response with no content and no error

1. var json =  LB
2. json = json +  Q
3. json = json +  RB
   - Expected: resp.content equals ``
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var json = _LB()
json = json + _Q() + "model" + _Q() + ":" + _Q() + "gemini-2.5-pro" + _Q()
json = json + _RB()
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("")
expect(resp.is_error).to_equal(false)
```

</details>

#### handles multiline response content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Line 1\\nLine 2", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.content).to_contain("Line 1")
```

</details>

#### defaults stop reason to end_turn for non-error

1. var json =  LB
2. json = json +  Q
3. json = json +  RB
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var json = _LB()
json = json + _Q() + "response" + _Q() + ":" + _Q() + "Done" + _Q()
json = json + _RB()
val resp = parse_gemini_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
