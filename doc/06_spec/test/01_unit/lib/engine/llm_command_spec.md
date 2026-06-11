# llm_command_spec

> LLM Command Dispatch Tests

<!-- sdn-diagram:id=llm_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_command_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/engine/llm_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

LLM Command Dispatch Tests

Tests LLMRequest parsing, LLMResponse creation, LLMCommandDispatcher
registration and dispatch, and ContextPacker packing.

## Scenarios

### LLMRequest

### new

#### creates a request with command and prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = LLMRequest.new("create", "a forest scene")
expect(req.command).to_equal("create")
expect(req.prompt).to_equal("a forest scene")
expect(req.context_data).to_equal("")
```

</details>

### parse

#### splits command from prompt on first space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = LLMRequest.parse("create a forest scene")
expect(req.command).to_equal("create")
expect(req.prompt).to_equal("a forest scene")
```

</details>

#### handles input with no space as command only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = LLMRequest.parse("nospace")
expect(req.command).to_equal("nospace")
expect(req.prompt).to_equal("")
```

</details>

#### handles single word with trailing content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = LLMRequest.parse("debug why is FPS low")
expect(req.command).to_equal("debug")
expect(req.prompt).to_equal("why is FPS low")
```

</details>

### LLMResponse

### ok

#### creates a successful response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = LLMResponse.ok("scene created", "create")
expect(resp.success).to_equal(true)
expect(resp.output).to_equal("scene created")
expect(resp.response_type).to_equal("create")
```

</details>

### error

#### creates an error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = LLMResponse.error("something went wrong")
expect(resp.success).to_equal(false)
expect(resp.output).to_equal("something went wrong")
expect(resp.response_type).to_equal("error")
```

</details>

### LLMCommandDispatcher

### new

#### starts with default commands registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disp = LLMCommandDispatcher.new()
expect(disp.command_count()).to_equal(5.to_i32())
```

</details>

### has_command

#### returns true for a default command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disp = LLMCommandDispatcher.new()
expect(disp.has_command("create")).to_equal(true)
expect(disp.has_command("debug")).to_equal(true)
expect(disp.has_command("generate")).to_equal(true)
```

</details>

#### returns false for an unknown command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disp = LLMCommandDispatcher.new()
expect(disp.has_command("explode")).to_equal(false)
```

</details>

### register_command

#### adds a new command

1. var disp = LLMCommandDispatcher new
2. disp register command
   - Expected: disp.has_command("optimize") is true
   - Expected: disp.command_count() equals `6.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var disp = LLMCommandDispatcher.new()
disp.register_command("optimize")
expect(disp.has_command("optimize")).to_equal(true)
expect(disp.command_count()).to_equal(6.to_i32())
```

</details>

### dispatch

#### dispatches a known command successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkr = ContextPacker.new(10)
expect(pkr.entry_count()).to_equal(0.to_i64())
```

</details>

### add_entry

#### adds a single entry

1. var pkr = ContextPacker new
2. pkr add entry
   - Expected: pkr.entry_count() equals `1.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pkr = ContextPacker.new(10)
pkr.add_entry("scene", "name", "Forest")
expect(pkr.entry_count()).to_equal(1.to_i64())
```

</details>

#### respects max_entries limit

1. var pkr = ContextPacker new
2. pkr add entry
3. pkr add entry
4. pkr add entry
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pkr = ContextPacker.new(2)
pkr.add_entry("a", "k1", "v1")
pkr.add_entry("a", "k2", "v2")
pkr.add_entry("a", "k3", "v3")
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### add_scene_info

#### adds two entries for scene info

1. var pkr = ContextPacker new
2. pkr add scene info
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pkr = ContextPacker.new(10)
pkr.add_scene_info("Level1", 42)
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### add_physics_info

#### adds two entries for physics info

1. var pkr = ContextPacker new
2. pkr add physics info
   - Expected: pkr.entry_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pkr = ContextPacker.new(10)
pkr.add_physics_info(10, -9.8)
expect(pkr.entry_count()).to_equal(2.to_i64())
```

</details>

### pack

#### returns empty string when no entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkr = ContextPacker.new(10)
expect(pkr.pack()).to_equal("")
```

</details>

#### formats entries with category headers

1. var pkr = ContextPacker new
2. pkr add scene info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pkr = ContextPacker.new(10)
pkr.add_scene_info("Forest", 5)
val packed = pkr.pack()
expect(packed).to_contain("## scene")
expect(packed).to_contain("- name: Forest")
expect(packed).to_contain("- node_count: 5")
```

</details>

#### separates different categories

1. var pkr = ContextPacker new
2. pkr add scene info
3. pkr add physics info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var pkr = ContextPacker new
2. pkr add entry
3. pkr add entry
4. pkr clear
   - Expected: pkr.entry_count() equals `0.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
