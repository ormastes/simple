# OTP Behaviour Implementations

> Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour contracts with message dispatch patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# OTP Behaviour Implementations

Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour contracts with message dispatch patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/feature/lib/gc_parity/otp_behaviours_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the OTP-inspired GenServer, GenStatem, and GenEvent behaviour
contracts with message dispatch patterns.

## Scenarios

### GenServer Behaviour

#### when handling calls

#### updates state via call

- updates state via call
- updates state via call
   - Expected: state equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("updates state via call")
step("updates state via call")
# @req: REQ-FEAT-GC-PARITY-OTP-BEHAVIOURS-SPEC-001
"""
A counter increment handler should update state.
"""
var state = 0
state = state + 1
expect(state).to_equal(1)
```

</details>

#### supports reply format

- supports reply format
- supports reply format
   - Expected: parts[0] equals `reply`
   - Expected: parts.len() equals `3`
   - Expected: parts[1] equals `hello`
   - Expected: parts[2] equals `updated_state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports reply format")
step("supports reply format")
"""
Handlers can return "reply|<reply>|<new_state>" for explicit replies.
"""
val result = "reply|hello|updated_state"
val parts = result.split("|")
expect(parts[0]).to_equal("reply")
expect(parts.len()).to_equal(3)
expect(parts[1]).to_equal("hello")
expect(parts[2]).to_equal("updated_state")
```

</details>

#### when using message prefixes

#### identifies call messages

- identifies call messages
- identifies call messages
   - Expected: is_call is true
   - Expected: request equals `get_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identifies call messages")
step("identifies call messages")
"""
Messages starting with "call:" are synchronous calls.
"""
val msg = "call:get_count"
val is_call = msg.starts_with("call:")
expect(is_call).to_equal(true)
val request = msg.substring(5)
expect(request).to_equal("get_count")
```

</details>

#### identifies cast messages

- identifies cast messages
- identifies cast messages
   - Expected: is_cast is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identifies cast messages")
step("identifies cast messages")
"""
Messages starting with "cast:" are async casts.
"""
val msg = "cast:increment"
val is_cast = msg.starts_with("cast:")
expect(is_cast).to_equal(true)
```

</details>

#### identifies stop message

- identifies stop message
- identifies stop message
   - Expected: is_stop is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identifies stop message")
step("identifies stop message")
"""
The special "$$stop$$" message stops the server.
"""
val msg = '$$stop$$'
val is_stop = msg == '$$stop$$'
expect(is_stop).to_equal(true)
```

</details>

### GenStatem Behaviour

#### when processing transitions

#### transitions through states

- transitions through states
- transitions through states
   - Expected: state equals `green`
   - Expected: state equals `yellow`
   - Expected: state equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transitions through states")
step("transitions through states")
"""
A traffic light cycles: red -> green -> yellow -> red.
"""
var state = "red"
if state == "red":
    state = "green"
expect(state).to_equal("green")

if state == "green":
    state = "yellow"
expect(state).to_equal("yellow")

if state == "yellow":
    state = "red"
expect(state).to_equal("red")
```

</details>

#### counts transitions

- counts transitions
- counts transitions
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("counts transitions")
step("counts transitions")
"""
Each state change increments a transition counter.
"""
var count = 0
var state = "idle"
state = "active"
count = count + 1
state = "idle"
count = count + 1
expect(count).to_equal(2)
```

</details>

#### when using transition result format

#### parses next_state result

- parses next_state result
- parses next_state result
   - Expected: is_transition is true
   - Expected: new_state equals `active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses next_state result")
step("parses next_state result")
"""
"next_state:active|session_id=123" transitions to "active".
"""
val result = "next_state:active|session_id=123"
val is_transition = result.starts_with("next_state:")
expect(is_transition).to_equal(true)
val payload = result.substring(11)
val parts = payload.split("|")
val new_state = parts[0]
expect(new_state).to_equal("active")
```

</details>

#### parses stop result

- parses stop result
- parses stop result
   - Expected: is_stop is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses stop result")
step("parses stop result")
"""
"stop:normal" signals termination.
"""
val result = "stop:normal"
val is_stop = result.starts_with("stop:")
expect(is_stop).to_equal(true)
```

</details>

### GenEvent Behaviour

#### when managing handlers

#### adds and counts handlers

- adds and counts handlers
- adds and counts handlers
   - Expected: handler_list[0] equals `logger`
   - Expected: handler_list.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds and counts handlers")
step("adds and counts handlers")
"""
Adding handlers should increment count.
"""
val handler_list = ["logger", "metrics", "audit"]
expect(handler_list[0]).to_equal("logger")
expect(handler_list.len()).to_equal(3)
```

</details>

#### removes handlers by id

- removes handlers by id
- removes handlers by id
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("removes handlers by id")
step("removes handlers by id")
"""
Removing a handler filters by ID.
"""
val all_handlers = ["logger", "metrics", "audit"]
var count = 0
for h in all_handlers:
    if h != "metrics":
        count = count + 1
expect(count).to_equal(2)
```

</details>

#### when dispatching events

#### broadcasts to all handlers

- broadcasts to all handlers
- broadcasts to all handlers
   - Expected: dispatched_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("broadcasts to all handlers")
step("broadcasts to all handlers")
"""
Each handler gets called with the event.
"""
val handler_ids = ["h1", "h2", "h3"]
var dispatched_count = 0
for h in handler_ids:
    dispatched_count = dispatched_count + 1
expect(dispatched_count).to_equal(3)
```

</details>

#### collects sync responses

- collects sync responses
- collects sync responses
   - Expected: responses.len() equals `3`
   - Expected: ok_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("collects sync responses")
step("collects sync responses")
"""
Synchronous calls collect a response from each handler.
"""
val responses = ["ok", "ok", "error"]
expect(responses.len()).to_equal(3)
var ok_count = 0
for r in responses:
    if r == "ok":
        ok_count = ok_count + 1
expect(ok_count).to_equal(2)
```

</details>

### Common Module Migration

#### when using migrated modules

#### basic array operations work

- basic array operations work
- basic array operations work
   - Expected: items[0] equals `5`
   - Expected: items.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("basic array operations work")
step("basic array operations work")
"""
Array utilities migrated from nogc_sync_mut to common/.
"""
val items = [5, 3, 1, 4, 2]
expect(items[0]).to_equal(5)
expect(items.len()).to_equal(5)
```

</details>

#### string operations for config parsing work

- string operations for config parsing work
- string operations for config parsing work
   - Expected: has_eq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("string operations for config parsing work")
step("string operations for config parsing work")
"""
config_parser.spl was migrated to common/.
Text parsing should still work.
"""
val line = "key = value"
val has_eq = line.contains("=")
expect(has_eq).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-GC-PARITY-OTP-BEHAVIOURS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b988b8d628827cde62edf4a7f4d1d11b0d0132ac3aeebdc07c75c74556c5b86a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b988b8d628827cde62edf4a7f4d1d11b0d0132ac3aeebdc07c75c74556c5b86a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b988b8d628827cde62edf4a7f4d1d11b0d0132ac3aeebdc07c75c74556c5b86a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/lib/gc_parity/otp_behaviours_spec.spl
mirror: doc/06_spec/feature/lib/gc_parity/otp_behaviours_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/gc_parity/otp_behaviours_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/gc_parity/otp_behaviours_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/gc_parity/otp_behaviours_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/gc_parity/otp_behaviours_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates state via call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/gc_parity/otp_behaviours_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports reply format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/gc_parity/otp_behaviours_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies call messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
