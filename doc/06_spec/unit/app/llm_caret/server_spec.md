# Server Specification

> Tests covering Health Endpoint, Models Endpoint, Chat Completion Response, Anthropic Response, Error Response, Route Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Specification

## Scenarios

### Health Endpoint

#### returns ok status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns ok status


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ok status")
val resp = build_health_response()
expect(resp).to_contain("\"ok\"")
```

</details>

#### returns service name

- returns service name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns service name")
val resp = build_health_response()
expect(resp).to_contain("llm_caret")
```

</details>

#### returns version

- returns version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns version")
val resp = build_health_response()
expect(resp).to_contain("0.1.0")
```

</details>

### Models Endpoint

#### returns list object

- returns list object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns list object")
val resp = build_models_response()
expect(resp).to_contain("\"list\"")
```

</details>

#### includes claude sonnet

- includes claude sonnet


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes claude sonnet")
val resp = build_models_response()
expect(resp).to_contain("claude-sonnet-4-20250514")
```

</details>

#### includes claude opus

- includes claude opus


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes claude opus")
val resp = build_models_response()
expect(resp).to_contain("claude-opus-4-20250514")
```

</details>

#### includes gpt-4o

- includes gpt-4o


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes gpt-4o")
val resp = build_models_response()
expect(resp).to_contain("gpt-4o")
```

</details>

### Chat Completion Response

#### includes content

- includes content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes content")
val resp = build_chat_completion_response("Hello!", "gpt-4o", "stop")
expect(resp).to_contain("Hello!")
```

</details>

#### includes model

- includes model


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes model")
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("gpt-4o")
```

</details>

#### includes finish reason

- includes finish reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes finish reason")
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("stop")
```

</details>

#### has chat.completion object type

- has chat.completion object type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has chat.completion object type")
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("chat.completion")
```

</details>

#### has assistant role

- has assistant role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has assistant role")
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("assistant")
```

</details>

### Anthropic Response

#### includes text content

- includes text content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes text content")
val resp = build_anthropic_response("Hello!", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("Hello!")
```

</details>

#### has message type

- has message type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has message type")
val resp = build_anthropic_response("Hi", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("\"message\"")
```

</details>

#### includes stop reason

- includes stop reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes stop reason")
val resp = build_anthropic_response("Hi", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("end_turn")
```

</details>

### Error Response

#### includes error message

- includes error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes error message")
val resp = build_error_response("not found", 404)
expect(resp).to_contain("not found")
```

</details>

#### includes status code

- includes status code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes status code")
val resp = build_error_response("bad request", 400)
expect(resp).to_contain("400")
```

</details>

### Route Handling

#### handles health check

- handles health check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles health check")
val resp = handle_route("GET", "/v1/health", "")
expect(resp).to_contain("ok")
```

</details>

#### handles models list

- handles models list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles models list")
val resp = handle_route("GET", "/v1/models", "")
expect(resp).to_contain("list")
```

</details>

#### returns 404 for unknown path

- returns 404 for unknown path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 404 for unknown path")
val resp = handle_route("GET", "/unknown", "")
expect(resp).to_contain("not found")
```

</details>

#### returns error for empty chat completion

- returns error for empty chat completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for empty chat completion")
val resp = handle_route("POST", "/v1/chat/completions", "")
expect(resp).to_contain("messages required")
```

</details>

#### returns 501 for valid chat request

- returns 501 for valid chat request


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 501 for valid chat request")
var body = _LB()
body = body + _Q() + "content" + _Q() + ":" + _Q() + "Hello" + _Q()
body = body + _RB()
val resp = handle_route("POST", "/v1/chat/completions", body)
expect(resp).to_contain("501")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Health Endpoint, Models Endpoint, Chat Completion Response, Anthropic Response, Error Response, Route Handling.
- Health Endpoint
- Models Endpoint
- Chat Completion Response
- Anthropic Response
- Error Response
- Route Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `aa4fa347588f4d093373049975f0bdec122099b4dec1fabe701ba9a1a7827a01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa4fa347588f4d093373049975f0bdec122099b4dec1fabe701ba9a1a7827a01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa4fa347588f4d093373049975f0bdec122099b4dec1fabe701ba9a1a7827a01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_caret/server_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/server_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/server_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ok status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/server_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns service name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/server_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
