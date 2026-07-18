# aop_debug_log_spec

> Validates the AOP debug logging subsystem including enable/disable toggling, entry creation with depth tracking, group pairing of enter/exit calls, wildcard and prefix-based filter patterns, incremental entry querying, and ring buffer trimming when the entry limit is exceeded.

<!-- sdn-diagram:id=aop_debug_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_debug_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_debug_log_spec
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
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# aop_debug_log_spec

Validates the AOP debug logging subsystem including enable/disable toggling, entry creation with depth tracking, group pairing of enter/exit calls, wildcard and prefix-based filter patterns, incremental entry querying, and ring buffer trimming when the entry limit is exceeded.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/aop_debug_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the AOP debug logging subsystem including enable/disable toggling,
entry creation with depth tracking, group pairing of enter/exit calls,
wildcard and prefix-based filter patterns, incremental entry querying,
and ring buffer trimming when the entry limit is exceeded.

## Syntax

```simple
debug_log_enable("parse_*")
val gid = debug_log_enter("my_func", "app.mcp.main", "Server", 42, "path=\"/src\"")
debug_log_exit("my_func", "app.mcp.main", gid, 0)
val entries = debug_log_get_entries()
```
AOP Debug Logger Specification

Self-contained implementation of AOP debug logging with depth tracking,
group pairing, and ring buffer. No compiler imports needed.
Uses array concat (items = items + [x]) instead of .push() because
.push() does not persist on module-level arrays in the runtime.

## Scenarios

### AOP Debug Logger

#### enable and disable

#### starts disabled by default

1. debug log clear
2. debug log disable
   - Expected: enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_disable()
val enabled = debug_log_is_enabled()
expect(enabled).to_equal(false)
```

</details>

#### enables with wildcard pattern

1. debug log clear
2. debug log enable
   - Expected: debug_log_is_enabled() is true
   - Expected: en is true
   - Expected: pat equals `*`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
expect(debug_log_is_enabled()).to_equal(true)
val (en, pat, cnt, dep) = debug_log_get_status()
expect(en).to_equal(true)
expect(pat).to_equal("*")
debug_log_disable()
```

</details>

#### enables with specific pattern

1. debug log clear
2. debug log enable
   - Expected: en is true
   - Expected: pat equals `parse_*`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("parse_*")
val (en, pat, cnt, dep) = debug_log_get_status()
expect(en).to_equal(true)
expect(pat).to_equal("parse_*")
debug_log_disable()
```

</details>

#### disables logging

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

#### entry creation

#### creates enter entry with correct fields

1. debug log clear
2. debug log enable
   - Expected: entries.len() equals `1`
   - Expected: e.entry_type equals `enter`
   - Expected: e.function_name equals `my_func`
   - Expected: e.package_path equals `app.mcp.main`
   - Expected: e.class_name equals `Server`
   - Expected: e.line_number equals `42`
   - Expected: e.params_text equals `path="/src"`
   - Expected: e.depth equals `0`
   - Expected: e.group_id equals `gid`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid = debug_log_enter("my_func", "app.mcp.main", "Server", 42, "path=\"/src\"")
val entries = debug_log_get_entries()
val e = entries[0]
expect(entries.len()).to_equal(1)
expect(e.entry_type).to_equal("enter")
expect(e.function_name).to_equal("my_func")
expect(e.package_path).to_equal("app.mcp.main")
expect(e.class_name).to_equal("Server")
expect(e.line_number).to_equal(42)
expect(e.params_text).to_equal("path=\"/src\"")
expect(e.depth).to_equal(0)
expect(e.group_id).to_equal(gid)
debug_log_disable()
```

</details>

#### creates exit entry paired with enter

1. debug log clear
2. debug log enable
3. debug log exit
   - Expected: entries[0].entry_type equals `enter`
   - Expected: entries.len() equals `2`
   - Expected: entries[1].entry_type equals `exit`
   - Expected: entries[0].group_id equals `entries[1].group_id`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val gid = debug_log_enter("my_func", "app.mcp.main", "", 10, "")
debug_log_exit("my_func", "app.mcp.main", gid, 0)
val entries = debug_log_get_entries()
expect(entries[0].entry_type).to_equal("enter")
expect(entries.len()).to_equal(2)
expect(entries[1].entry_type).to_equal("exit")
expect(entries[0].group_id).to_equal(entries[1].group_id)
debug_log_disable()
```

</details>

#### skips entries when disabled

1. debug log clear
2. debug log disable
   - Expected: gid equals `-1`
   - Expected: debug_log_get_entries().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_disable()
val gid = debug_log_enter("my_func", "mod", "", 1, "")
expect(gid).to_equal(-1)
expect(debug_log_get_entries().len()).to_equal(0)
```

</details>

#### depth tracking

#### tracks nested call depth

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log exit
5. debug log exit
   - Expected: entries.len() equals `6`
   - Expected: entries[0].depth equals `0`
   - Expected: entries[1].depth equals `1`
   - Expected: entries[2].depth equals `2`
   - Expected: entries[3].depth equals `2`
   - Expected: entries[4].depth equals `1`
   - Expected: entries[5].depth equals `0`
6. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val g1 = debug_log_enter("outer", "mod", "", 1, "")
val g2 = debug_log_enter("inner", "mod", "", 2, "")
val g3 = debug_log_enter("deep", "mod", "", 3, "")
debug_log_exit("deep", "mod", g3, 0)
debug_log_exit("inner", "mod", g2, 0)
debug_log_exit("outer", "mod", g1, 0)
val entries = debug_log_get_entries()
expect(entries.len()).to_equal(6)
# Enter depths: 0, 1, 2
expect(entries[0].depth).to_equal(0)
expect(entries[1].depth).to_equal(1)
expect(entries[2].depth).to_equal(2)
# Exit depths: 2, 1, 0
expect(entries[3].depth).to_equal(2)
expect(entries[4].depth).to_equal(1)
expect(entries[5].depth).to_equal(0)
debug_log_disable()
```

</details>

#### group pairing

#### assigns unique group IDs

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log exit
5. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val g1 = debug_log_enter("func_a", "mod", "", 1, "")
debug_log_exit("func_a", "mod", g1, 0)
val g2 = debug_log_enter("func_b", "mod", "", 2, "")
debug_log_exit("func_b", "mod", g2, 0)
expect(g1).to_be_greater_than(0)
expect(g2).to_be_greater_than(g1)
debug_log_disable()
```

</details>

#### tracks parent group IDs

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log exit
   - Expected: entries[1].parent_group_id equals `g_outer`
   - Expected: entries[0].parent_group_id equals `0`
5. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val g_outer = debug_log_enter("outer", "mod", "", 1, "")
val g_inner = debug_log_enter("inner", "mod", "", 2, "")
debug_log_exit("inner", "mod", g_inner, 0)
debug_log_exit("outer", "mod", g_outer, 0)
val entries = debug_log_get_entries()
# Inner enter should have outer as parent
expect(entries[1].parent_group_id).to_equal(g_outer)
# Outer enter should have 0 (no parent)
expect(entries[0].parent_group_id).to_equal(0)
debug_log_disable()
```

</details>

#### filter pattern

#### filters by prefix pattern

1. debug log clear
2. debug log enable
   - Expected: g2 equals `-1`
   - Expected: debug_log_get_entries().len() equals `1`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("parse_*")
val g1 = debug_log_enter("parse_expr", "mod", "", 1, "")
val g2 = debug_log_enter("eval_expr", "mod", "", 2, "")
expect(g1).to_be_greater_than(0)
expect(g2).to_equal(-1)
expect(debug_log_get_entries().len()).to_equal(1)
debug_log_disable()
```

</details>

#### filters by module path

1. debug log clear
2. debug log enable
   - Expected: g2 equals `-1`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("app.mcp*")
val g1 = debug_log_enter("handle", "app.mcp.main", "", 1, "")
val g2 = debug_log_enter("handle", "app.cli.main", "", 2, "")
expect(g1).to_be_greater_than(0)
expect(g2).to_equal(-1)
debug_log_disable()
```

</details>

#### matches exact function name

1. debug log clear
2. debug log enable
   - Expected: g2 equals `-1`
3. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("my_exact_func")
val g1 = debug_log_enter("my_exact_func", "mod", "", 1, "")
val g2 = debug_log_enter("other_func", "mod", "", 2, "")
expect(g1).to_be_greater_than(0)
expect(g2).to_equal(-1)
debug_log_disable()
```

</details>

#### query entries

#### returns entries since a given ID

1. debug log clear
2. debug log enable
3. debug log exit
4. debug log exit
   - Expected: new_entries[0].function_name equals `b`
   - Expected: new_entries.len() equals `2`
5. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
val g1 = debug_log_enter("a", "mod", "", 1, "")
debug_log_exit("a", "mod", g1, 0)
val entries_before = debug_log_get_entries()
val last_id = entries_before[entries_before.len() - 1].entry_id
val g2 = debug_log_enter("b", "mod", "", 2, "")
debug_log_exit("b", "mod", g2, 0)
val new_entries = debug_log_get_entries_since(last_id)
expect(new_entries[0].function_name).to_equal("b")
expect(new_entries.len()).to_equal(2)
debug_log_disable()
```

</details>

#### ring buffer

#### trims entries when exceeding max

1. debug log clear
2. debug log enable
3. debug log set max entries
4. debug log enter
5. debug log set max entries
6. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_clear()
debug_log_enable("*")
debug_log_set_max_entries(20)
# Add 25 enter entries
for i in range(0, 25):
    debug_log_enter("func", "mod", "", i, "")
val entries = debug_log_get_entries()
# Should have trimmed: 25 > 20, so oldest entries removed
expect(entries.len()).to_be_less_than(26)
# Reset max for other tests
debug_log_set_max_entries(10000)
debug_log_disable()
```

</details>

#### clear

#### resets all state

1. debug log enable
2. debug log enter
3. debug log clear
   - Expected: cnt equals `0`
   - Expected: dep equals `0`
4. debug log disable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_enable("*")
debug_log_enter("func", "mod", "", 1, "")
debug_log_clear()
val (en, pat, cnt, dep) = debug_log_get_status()
expect(cnt).to_equal(0)
expect(dep).to_equal(0)
debug_log_disable()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
