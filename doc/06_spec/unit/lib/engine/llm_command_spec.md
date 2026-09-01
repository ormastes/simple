# llm_command_spec

> LLM Command Dispatch Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_command_spec

LLM Command Dispatch Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/llm_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

LLM Command Dispatch Tests

Tests LLMRequest parsing, LLMResponse creation, LLMCommandDispatcher
registration and dispatch, and ContextPacker packing.

## Scenarios

### LLMRequest

### new

#### creates a request with command and prompt

- creates a request with command and prompt
   - Expected: req.command equals `create`
   - Expected: req.prompt equals `a forest scene`
   - Expected: req.context_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a request with command and prompt")
val req = LLMRequest.new("create", "a forest scene")
expect(req.command).to_equal("create")
expect(req.prompt).to_equal("a forest scene")
expect(req.context_data).to_equal("")
```

</details>

### parse

#### splits command from prompt on first space

- splits command from prompt on first space
   - Expected: req.command equals `create`
   - Expected: req.prompt equals `a forest scene`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits command from prompt on first space")
val req = LLMRequest.parse("create a forest scene")
expect(req.command).to_equal("create")
expect(req.prompt).to_equal("a forest scene")
```

</details>

#### handles input with no space as command only

- handles input with no space as command only
   - Expected: req.command equals `nospace`
   - Expected: req.prompt equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles input with no space as command only")
val req = LLMRequest.parse("nospace")
expect(req.command).to_equal("nospace")
expect(req.prompt).to_equal("")
```

</details>

#### handles single word with trailing content

- handles single word with trailing content
   - Expected: req.command equals `debug`
   - Expected: req.prompt equals `why is FPS low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single word with trailing content")
val req = LLMRequest.parse("debug why is FPS low")
expect(req.command).to_equal("debug")
expect(req.prompt).to_equal("why is FPS low")
```

</details>

### LLMResponse

### ok

#### creates a successful response

- creates a successful response
   - Expected: resp.success is true
   - Expected: resp.output equals `scene created`
   - Expected: resp.response_type equals `create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a successful response")
val resp = LLMResponse.ok("scene created", "create")
expect(resp.success).to_equal(true)
expect(resp.output).to_equal("scene created")
expect(resp.response_type).to_equal("create")
```

</details>

### error

#### creates an error response

- creates an error response
   - Expected: resp.success is false
   - Expected: resp.output equals `something went wrong`
   - Expected: resp.response_type equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an error response")
val resp = LLMResponse.error("something went wrong")
expect(resp.success).to_equal(false)
expect(resp.output).to_equal("something went wrong")
expect(resp.response_type).to_equal("error")
```

</details>

### LLMCommandDispatcher

### new

#### starts with default commands registered

- starts with default commands registered
   - Expected: disp.command_count() equals `5.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with default commands registered")
val disp = LLMCommandDispatcher.new()
expect(disp.command_count()).to_equal(5.to_i32())
```

</details>

### has_command

#### returns true for a default command

- returns true for a default command
   - Expected: disp.has_command("create") is true
   - Expected: disp.has_command("debug") is true
   - Expected: disp.has_command("generate") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for a default command")
val disp = LLMCommandDispatcher.new()
expect(disp.has_command("create")).to_equal(true)
expect(disp.has_command("debug")).to_equal(true)
expect(disp.has_command("generate")).to_equal(true)
```

</details>

#### returns false for an unknown command

- returns false for an unknown command
   - Expected: disp.has_command("explode") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for an unknown command")
val disp = LLMCommandDispatcher.new()
expect(disp.has_command("explode")).to_equal(false)
```

</details>

### register_command

#### adds a new command

- adds a new command
   - Expected: disp.has_command("optimize") is true
   - Expected: disp.command_count() equals `6.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds a new command")
var disp = LLMCommandDispatcher.new()
disp.register_command("optimize")
expect(disp.has_command("optimize")).to_equal(true)
expect(disp.command_count()).to_equal(6.to_i32())
```

</details>

### dispatch

#### dispatches a known command successfully

- dispatches a known command successfully
   - Expected: resp.success is true
   - Expected: resp.response_type equals `create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches a known command successfully")
val disp = LLMCommandDispatcher.new()
val req = LLMRequest.new("create", "a tree")
val resp = disp.dispatch(req)
expect(resp.success).to_equal(true)
expect(resp.response_type).to_equal("create")
expect(resp.output).to_contain("create")
expect(resp.output).to_contain("a tree")
```

</details>

#### returns error for an unknown command

- returns error for an unknown command
   - Expected: resp.success is false
   - Expected: resp.response_type equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for an unknown command")
val disp = LLMCommandDispatcher.new()
val req = LLMRequest.new("explode", "everything")
val resp = disp.dispatch(req)
expect(resp.success).to_equal(false)
expect(resp.response_type).to_equal("error")
expect(resp.output).to_contain("Unknown command")
```

</details>

### ContextPacker

### new

#### starts with zero entries

- starts with zero entries
   - Expected: pkr.entry_count() equals `0.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero entries")
val pkr = ContextPacker.new(10)
expect(pkr.entry_count()).to_equal(0.to_i64())
```

</details>

### add_entry

#### adds a single entry

- adds a single entry
   - Expected: pkr.entry_count() equals `1.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds a single entry")
var pkr = ContextPacker.new(10)
pkr.add_entry("scene", "name", "Forest")
expect(pkr.entry_count()).to_equal(1.to_i64())
```

</details>

#### respects max_entries limit

- respects max_entries limit
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects max_entries limit")
var pkr = ContextPacker.new(2)
pkr.add_entry("a", "k1", "v1")
pkr.add_entry("a", "k2", "v2")
pkr.add_entry("a", "k3", "v3")
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### add_scene_info

#### adds two entries for scene info

- adds two entries for scene info
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two entries for scene info")
var pkr = ContextPacker.new(10)
pkr.add_scene_info("Level1", 42)
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### add_physics_info

#### adds two entries for physics info

- adds two entries for physics info
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two entries for physics info")
var pkr = ContextPacker.new(10)
pkr.add_physics_info(10, -9.8)
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### pack

#### returns empty string when no entries

- returns empty string when no entries
   - Expected: pkr.pack() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string when no entries")
val pkr = ContextPacker.new(10)
expect(pkr.pack()).to_equal("")
```

</details>

#### formats entries with category headers

- formats entries with category headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats entries with category headers")
var pkr = ContextPacker.new(10)
pkr.add_scene_info("Forest", 5)
val packed = pkr.pack()
expect(packed).to_contain("## scene")
expect(packed).to_contain("- name: Forest")
expect(packed).to_contain("- node_count: 5")
```

</details>

#### separates different categories

- separates different categories


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates different categories")
var pkr = ContextPacker.new(10)
pkr.add_scene_info("Level1", 42)
pkr.add_physics_info(10, -9.8)
val packed = pkr.pack()
expect(packed).to_contain("## scene")
expect(packed).to_contain("## physics")
```

</details>

### clear

#### removes all entries

- removes all entries
   - Expected: pkr.entry_count() equals `0.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes all entries")
var pkr = ContextPacker.new(10)
pkr.add_entry("cat", "key", "val")
pkr.add_entry("cat", "key2", "val2")
pkr.clear()
expect(pkr.entry_count()).to_equal(0.to_i64())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `d9c2afa8693fea3a8d339055e2dac7dfeaf00e5f0b115cf4981d30044e10b5e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d9c2afa8693fea3a8d339055e2dac7dfeaf00e5f0b115cf4981d30044e10b5e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d9c2afa8693fea3a8d339055e2dac7dfeaf00e5f0b115cf4981d30044e10b5e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/engine/llm_command_spec.spl
mirror: doc/06_spec/unit/lib/engine/llm_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/llm_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/llm_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/llm_command_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a request with command and prompt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/llm_command_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits command from prompt on first space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/llm_command_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles input with no space as command only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
