# Console API Spec

> Unit tests for the Simple browser engine Console API.

<!-- sdn-diagram:id=console_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=console_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

console_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=console_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Console API Spec

Unit tests for the Simple browser engine Console API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/console_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Console API.

## Scenarios

### Console API - Logging

#### logs a message

1. var buf = ConsoleBuffer new
2. buf = console log
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_log(buf, "hello")
val entries = buf.entries()
expect(entries.len()).to_equal(1)
```

</details>

#### log entry has correct level

1. var buf = ConsoleBuffer new
2. buf = console log
   - Expected: entries[0].level equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_log(buf, "test")
val entries = buf.entries()
expect(entries[0].level).to_equal("log")
```

</details>

#### log entry has correct message

1. var buf = ConsoleBuffer new
2. buf = console log
   - Expected: entries[0].message equals `test msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_log(buf, "test msg")
val entries = buf.entries()
expect(entries[0].message).to_equal("test msg")
```

</details>

#### warns a message

1. var buf = ConsoleBuffer new
2. buf = console warn
   - Expected: entries[0].level equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_warn(buf, "warning")
val entries = buf.entries()
expect(entries[0].level).to_equal("warn")
```

</details>

#### errors a message

1. var buf = ConsoleBuffer new
2. buf = console error
   - Expected: entries[0].level equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_error(buf, "err")
val entries = buf.entries()
expect(entries[0].level).to_equal("error")
```

</details>

#### info message

1. var buf = ConsoleBuffer new
2. buf = console info
   - Expected: entries[0].level equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_info(buf, "info msg")
val entries = buf.entries()
expect(entries[0].level).to_equal("info")
```

</details>

#### debug message

1. var buf = ConsoleBuffer new
2. buf = console debug
   - Expected: entries[0].level equals `debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_debug(buf, "dbg")
val entries = buf.entries()
expect(entries[0].level).to_equal("debug")
```

</details>

#### logs WebGPU shader diagnostics for DevTools

1. var buf = ConsoleBuffer new
2. buf = console webgpu shader diagnostic
   - Expected: entries.len() equals `1`
   - Expected: entries[0].level equals `error`
   - Expected: entries[0].message equals `error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @locat... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
val diagnostic = webgpu_diagnose_wgsl("// prelude\n@fragment fn main() -> vec4f { return vec4f(1.0); }")
buf = console_webgpu_shader_diagnostic(buf, diagnostic)
val entries = buf.entries()
expect(entries.len()).to_equal(1)
expect(entries[0].level).to_equal("error")
expect(entries[0].message).to_equal("error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @location(0) output")
```

</details>

### Console API - Clear

#### clears all entries

1. var buf = ConsoleBuffer new
2. buf = console log
3. buf = console log
4. buf = console clear
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_log(buf, "a")
buf = console_log(buf, "b")
buf = console_clear(buf)
val entries = buf.entries()
expect(entries.len()).to_equal(0)
```

</details>

### Console API - Timers

#### starts a timer

1. var buf = ConsoleBuffer new
2. buf = console time
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_time(buf, "op-start")
# Timer started — no entry yet
val entries = buf.entries()
expect(entries.len()).to_equal(0)
```

</details>

#### ends a timer and logs

1. var buf = ConsoleBuffer new
2. buf = console time
3. buf = console time end
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_time(buf, "op-end")
buf = console_time_end(buf, "op-end")
val entries = buf.entries()
expect(entries.len()).to_equal(1)
```

</details>

#### warns on duplicate timer

1. var buf = ConsoleBuffer new
2. buf = console time
3. buf = console time
   - Expected: entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_time(buf, "op-duplicate")
buf = console_time(buf, "op-duplicate")
val entries = buf.entries()
expect(entries.len()).to_equal(1)
```

</details>

#### warns on unknown timer end

1. var buf = ConsoleBuffer new
2. buf = console time end
   - Expected: entries[0].level equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ConsoleBuffer.new()
buf = console_time_end(buf, "unknown")
val entries = buf.entries()
expect(entries[0].level).to_equal("warn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
