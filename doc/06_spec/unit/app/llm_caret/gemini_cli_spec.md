# Minimal Arg Building

> Tests that build_gemini_args produces correct args with minimal input.

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
| Source | `test/unit/app/llm_caret/gemini_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that build_gemini_args produces correct args with minimal input.

## Scenarios

### build_gemini_args - minimal

#### includes prompt with -p flag

- includes prompt with -p flag
   - Expected: args_contain(args, "-p") is true
   - Expected: args_get_flag_value(args, "-p") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes prompt with -p flag")
val args = build_gemini_args("Hello", "", "", "", [])
expect(args_contain(args, "-p")).to_equal(true)
expect(args_get_flag_value(args, "-p")).to_equal("Hello")
```

</details>

#### defaults to json output format

- defaults to json output format
   - Expected: args_get_flag_value(args, "--output-format") equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to json output format")
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
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
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_contain(args, "--model")).to_equal(false)
```

</details>

#### has no resume flag when empty

- has no resume flag when empty
   - Expected: args_contain(args, "--resume") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no resume flag when empty")
val args = build_gemini_args("Hi", "", "", "", [])
expect(args_contain(args, "--resume")).to_equal(false)
```

</details>

### build_gemini_args - model

#### includes model flag

- includes model flag
   - Expected: args_get_flag_value(args, "--model") equals `gemini-2.5-pro`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes model flag")
val args = build_gemini_args("Hi", "gemini-2.5-pro", "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("gemini-2.5-pro")
```

</details>

#### supports flash model

- supports flash model
   - Expected: args_get_flag_value(args, "--model") equals `gemini-2.5-flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports flash model")
val args = build_gemini_args("Hi", "gemini-2.5-flash", "", "", [])
expect(args_get_flag_value(args, "--model")).to_equal("gemini-2.5-flash")
```

</details>

### build_gemini_args - output format

#### uses custom output format

- uses custom output format
   - Expected: args_get_flag_value(args, "--output-format") equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses custom output format")
val args = build_gemini_args("Hi", "", "text", "", [])
expect(args_get_flag_value(args, "--output-format")).to_equal("text")
```

</details>

### build_gemini_args - session

#### includes session resume

- includes session resume
   - Expected: args_get_flag_value(args, "--resume") equals `abc-123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes session resume")
val args = build_gemini_args("Hi", "", "", "abc-123", [])
expect(args_get_flag_value(args, "--resume")).to_equal("abc-123")
```

</details>

### build_gemini_args - extra args

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
val args = build_gemini_args("Hi", "", "", "", ["--no-cache"])
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
val args = build_gemini_args("Hi", "", "", "", ["", "--flag", ""])
expect(args_contain(args, "--flag")).to_equal(true)
expect(args_contain(args, "")).to_equal(false)
```

</details>

### build_gemini_args - combined

#### builds complete args

- builds complete args
   - Expected: args_get_flag_value(args, "-p") equals `prompt`
   - Expected: args_get_flag_value(args, "--model") equals `gemini-2.5-pro`
   - Expected: args_get_flag_value(args, "--output-format") equals `json`
   - Expected: args_get_flag_value(args, "--resume") equals `sess-1`
   - Expected: args_contain(args, "--sandbox") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds complete args")
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

- parses successful response
   - Expected: resp.content equals `Hello world!`
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses successful response")
val json = mock_json("Hello world!", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.is_error).to_equal(false)
```

</details>

#### parses model field

- parses model field
   - Expected: resp.model equals `gemini-2.5-flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses model field")
val json = mock_json("Hi", "gemini-2.5-flash")
val resp = parse_gemini_json_response(json)
expect(resp.model).to_equal("gemini-2.5-flash")
```

</details>

#### parses stop reason as end_turn

- parses stop reason as end_turn
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses stop reason as end_turn")
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### preserves raw json

- preserves raw json
   - Expected: resp.raw equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves raw json")
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.raw).to_equal(json)
```

</details>

#### session_id is always empty for gemini

- session_id is always empty for gemini
   - Expected: resp.session_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_id is always empty for gemini")
val json = mock_json("Hi", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.session_id).to_equal("")
```

</details>

### parse_gemini_json_response - tokens

#### parses token counts

- parses token counts
   - Expected: resp.input_tokens equals `300`
   - Expected: resp.output_tokens equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses token counts")
val json = mock_json_with_tokens("Hi", 300, 75)
val resp = parse_gemini_json_response(json)
expect(resp.input_tokens).to_equal(300)
expect(resp.output_tokens).to_equal(75)
```

</details>

### parse_gemini_json_response - error

#### parses error response

- parses error response
   - Expected: resp.is_error is true
   - Expected: resp.error equals `Rate limited`
   - Expected: resp.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses error response")
val json = mock_error_json("Rate limited")
val resp = parse_gemini_json_response(json)
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
val resp = parse_gemini_json_response("")
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
val resp = parse_gemini_json_response("   ")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

### parse_gemini_json_response - edge cases

#### handles missing model field

- handles missing model field
   - Expected: resp.content equals `Hello`
   - Expected: resp.model equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing model field")
var json = _LB()
json = json + _Q() + "response" + _Q() + ":" + _Q() + "Hello" + _Q()
json = json + _RB()
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### handles response with no content and no error

- handles response with no content and no error
   - Expected: resp.content equals ``
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles response with no content and no error")
var json = _LB()
json = json + _Q() + "model" + _Q() + ":" + _Q() + "gemini-2.5-pro" + _Q()
json = json + _RB()
val resp = parse_gemini_json_response(json)
expect(resp.content).to_equal("")
expect(resp.is_error).to_equal(false)
```

</details>

#### handles multiline response content

- handles multiline response content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline response content")
val json = mock_json("Line 1\\nLine 2", "gemini-2.5-pro")
val resp = parse_gemini_json_response(json)
expect(resp.content).to_contain("Line 1")
```

</details>

#### defaults stop reason to end_turn for non-error

- defaults stop reason to end_turn for non-error
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults stop reason to end_turn for non-error")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e6f53c79f92d80838dd9407c3718e5fae0a112a14d54facfdf8a037ef4fdada`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e6f53c79f92d80838dd9407c3718e5fae0a112a14d54facfdf8a037ef4fdada`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e6f53c79f92d80838dd9407c3718e5fae0a112a14d54facfdf8a037ef4fdada`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/llm_caret/gemini_cli_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/gemini_cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/gemini_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/gemini_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/gemini_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_caret/gemini_cli_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes prompt with -p flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/gemini_cli_spec.spl:237:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to json output format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/gemini_cli_spec.spl:243:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no model flag when empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
