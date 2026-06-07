# AOP Debug Log Specification

> Tests the AOP debug logger's DebugLogEntry struct construction, field naming, and query function contracts. The logger is activated by env var SIMPLE_AOP_DEBUG and stores structured call traces in a ring buffer.

<!-- sdn-diagram:id=aop_debug_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_debug_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_debug_log_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_debug_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AOP Debug Log Specification

Tests the AOP debug logger's DebugLogEntry struct construction, field naming, and query function contracts. The logger is activated by env var SIMPLE_AOP_DEBUG and stores structured call traces in a ring buffer.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Compiler |
| Status | Implemented |
| Source | `test/01_unit/compiler/frontend/aop_debug_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the AOP debug logger's DebugLogEntry struct construction,
field naming, and query function contracts. The logger is activated
by env var SIMPLE_AOP_DEBUG and stores structured call traces in a
ring buffer.

## Key Concepts

| Concept        | Description                                         |
|----------------|-----------------------------------------------------|
| DebugLogEntry  | Struct capturing enter/exit metadata for a call     |
| Ring buffer    | Capped at g_log_max_entries, trims oldest on overflow |
| Filter pattern | Glob matching on function name or module path       |

## Scenarios

### DebugLogEntry struct

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = DebugLogEntry(
    entry_id: 1,
    group_id: 10,
    parent_group_id: 0,
    depth: 2,
    entry_type: "enter",
    package_path: "compiler.parser",
    class_name: "Parser",
    function_name: "parse",
    line_number: 42,
    timestamp_ms: 1000,
    duration_ms: 0,
    params_text: "source=\"hello\"",
    message: "",
)
expect(entry.entry_id).to_equal(1)
expect(entry.group_id).to_equal(10)
expect(entry.parent_group_id).to_equal(0)
expect(entry.depth).to_equal(2)
expect(entry.entry_type).to_equal("enter")
expect(entry.package_path).to_equal("compiler.parser")
expect(entry.class_name).to_equal("Parser")
expect(entry.function_name).to_equal("parse")
expect(entry.line_number).to_equal(42)
expect(entry.timestamp_ms).to_equal(1000)
expect(entry.duration_ms).to_equal(0)
expect(entry.params_text).to_equal("source=\"hello\"")
expect(entry.message).to_equal("")
```

</details>

#### entry_type is either enter or exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enter = DebugLogEntry(
    entry_id: 1, group_id: 1, parent_group_id: 0, depth: 0,
    entry_type: "enter", package_path: "", class_name: "",
    function_name: "f", line_number: 1, timestamp_ms: 0,
    duration_ms: 0, params_text: "", message: "",
)
val exit = DebugLogEntry(
    entry_id: 2, group_id: 1, parent_group_id: 0, depth: 0,
    entry_type: "exit", package_path: "", class_name: "",
    function_name: "f", line_number: 0, timestamp_ms: 10,
    duration_ms: 10, params_text: "", message: "",
)
expect(enter.entry_type).to_equal("enter")
expect(exit.entry_type).to_equal("exit")
expect(exit.duration_ms).to_equal(10)
```

</details>

### AOP Debug Log enable/disable

#### starts disabled by default when SIMPLE_AOP_DEBUG is unset

1. debug log clear
   - Expected: status.2 equals `0`
   - Expected: status.3 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
val status = debug_log_get_status()
expect(status.2).to_equal(0)
expect(status.3).to_equal(0)
```

</details>

#### enable sets enabled flag

1. debug log clear
2. debug log enable
   - Expected: debug_log_is_enabled() is true
   - Expected: status.0 is true
   - Expected: status.1 equals `*`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
expect(debug_log_is_enabled()).to_equal(true)
val status = debug_log_get_status()
expect(status.0).to_equal(true)
expect(status.1).to_equal("*")
debug_log_disable()
```

</details>

#### disable clears enabled flag

1. debug log enable
2. debug log disable
   - Expected: debug_log_is_enabled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_enable("*")
debug_log_disable()
expect(debug_log_is_enabled()).to_equal(false)
```

</details>

#### enable with pattern sets filter

1. debug log clear
2. debug log enable
   - Expected: status.0 is true
   - Expected: status.1 equals `parse_*`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("parse_*")
val status = debug_log_get_status()
expect(status.0).to_equal(true)
expect(status.1).to_equal("parse_*")
debug_log_disable()
```

</details>

#### enable with empty pattern defaults to wildcard

1. debug log clear
2. debug log enable
   - Expected: status.1 equals `*`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("")
val status = debug_log_get_status()
expect(status.1).to_equal("*")
debug_log_disable()
```

</details>

### AOP Debug Log entry recording

#### records enter and exit entries

1. debug log clear
2. debug log enable
3. debug log exit
   - Expected: entries.len() equals `2`
   - Expected: entries[0].entry_type equals `enter`
   - Expected: entries[0].function_name equals `my_func`
   - Expected: entries[0].package_path equals `mod.path`
   - Expected: entries[0].class_name equals `MyClass`
   - Expected: entries[0].line_number equals `10`
   - Expected: entries[0].params_text equals `x=1`
   - Expected: entries[1].entry_type equals `exit`
   - Expected: entries[1].function_name equals `my_func`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid = debug_log_enter("my_func", "mod.path", "MyClass", 10, "x=1")
expect(gid).to_be_greater_than(0)
debug_log_exit("my_func", "mod.path", gid, 0)
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(2)
expect(entries[0].entry_type).to_equal("enter")
expect(entries[0].function_name).to_equal("my_func")
expect(entries[0].package_path).to_equal("mod.path")
expect(entries[0].class_name).to_equal("MyClass")
expect(entries[0].line_number).to_equal(10)
expect(entries[0].params_text).to_equal("x=1")
expect(entries[1].entry_type).to_equal("exit")
expect(entries[1].function_name).to_equal("my_func")
debug_log_disable()
```

</details>

#### does not record when disabled

1. debug log clear
2. debug log disable
   - Expected: gid equals `-1`
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_disable()
val gid = debug_log_enter("f", "m", "", 1, "")
expect(gid).to_equal(-1)
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(0)
```

</details>

#### tracks depth for nested calls

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log exit
   - Expected: entries.len() equals `4`
   - Expected: entries[0].depth equals `0`
   - Expected: entries[1].depth equals `1`
   - Expected: entries[2].depth equals `1`
   - Expected: entries[3].depth equals `0`
5. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid1 = debug_log_enter("outer", "m", "", 1, "")
val gid2 = debug_log_enter("inner", "m", "", 2, "")
debug_log_exit("inner", "m", gid2, 0)
debug_log_exit("outer", "m", gid1, 0)
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(4)
expect(entries[0].depth).to_equal(0)
expect(entries[1].depth).to_equal(1)
expect(entries[2].depth).to_equal(1)
expect(entries[3].depth).to_equal(0)
debug_log_disable()
```

</details>

#### get_entries_since filters by entry_id

1. debug log clear
2. debug log enable
3. debug log exit
   - Expected: since_entries.len() equals `1`
   - Expected: since_entries[0].entry_id equals `2`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid1 = debug_log_enter("a", "m", "", 1, "")
debug_log_exit("a", "m", gid1, 0)
val since_entries = debug_log_get_entries_since(1)
expect(since_entries.len()).to_equal(1)
expect(since_entries[0].entry_id).to_equal(2)
debug_log_disable()
```

</details>

#### clear resets all state

1. debug log enable
2. debug log exit
3. debug log clear
   - Expected: entries.len() equals `0`
   - Expected: status.2 equals `0`
   - Expected: status.3 equals `0`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_enable("*")
val gid = debug_log_enter("f", "m", "", 1, "")
debug_log_exit("f", "m", gid, 0)
debug_log_clear()
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(0)
val status = debug_log_get_status()
expect(status.2).to_equal(0)
expect(status.3).to_equal(0)
debug_log_disable()
```

</details>

### AOP Debug Log filter

#### prefix pattern filters by function name

1. debug log clear
2. debug log enable
   - Expected: gid2 equals `-1`
3. debug log exit
   - Expected: entries.len() equals `2`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("parse_*")
val gid1 = debug_log_enter("parse_expr", "m", "", 1, "")
val gid2 = debug_log_enter("compile_expr", "m", "", 2, "")
expect(gid1).to_be_greater_than(0)
expect(gid2).to_equal(-1)
debug_log_exit("parse_expr", "m", gid1, 0)
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(2)
debug_log_disable()
```

</details>

#### wildcard pattern matches everything

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid = debug_log_enter("anything", "anywhere", "", 1, "")
expect(gid).to_be_greater_than(0)
debug_log_exit("anything", "anywhere", gid, 0)
debug_log_disable()
```

</details>

### AOP Debug Log ring buffer

#### set_max_entries changes limit

1. debug log clear
2. debug log set max entries
   - Expected: status.2 equals `0`
3. debug log set max entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_set_max_entries(50)
val status = debug_log_get_status()
expect(status.2).to_equal(0)
debug_log_set_max_entries(10000)
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
