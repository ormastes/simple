# Deps Tool Specification

> <details>

<!-- sdn-diagram:id=deps_tool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deps_tool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deps_tool_spec -> std
deps_tool_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deps_tool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deps Tool Specification

## Scenarios

### deps tool

### _parse_use_line

#### parses plain use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line1 = "use std.string." + "{" + "split" + "}"
val mods = _parse_use_line(line1)
expect(mods.len()).to_equal(1)
expect(mods[0]).to_equal("std.string")
```

</details>

#### parses export use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line2 = "export use std.io." + "{" + "print" + "}"
val mods = _parse_use_line(line2)
expect(mods.len()).to_equal(1)
expect(mods[0]).to_equal("std.io")
```

</details>

#### parses wildcard use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mods = _parse_use_line("use std.spec.*")
expect(mods.len()).to_equal(1)
expect(mods[0]).to_equal("std.spec")
```

</details>

#### parses relative use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line3 = "use .cycle_b." + "{" + "cycle_b_fn" + "}"
val mods = _parse_use_line(line3)
expect(mods.len()).to_equal(1)
expect(mods[0]).to_equal(".cycle_b")
```

</details>

#### returns empty list for non-use line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mods = _parse_use_line("fn foo() -> text:")
expect(mods.len()).to_equal(0)
```

</details>

### direct imports from entry fixture

#### entry.spl has exactly 2 direct imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directs = _direct_imports(ENTRY_FILE)
expect(directs.len()).to_equal(2)
```

</details>

#### entry.spl imports module_a.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directs = _direct_imports(ENTRY_FILE)
var found = false
for d in directs:
    if d.contains("module_a"):
        found = true
expect(found).to_equal(true)
```

</details>

#### entry.spl imports module_b.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directs = _direct_imports(ENTRY_FILE)
var found = false
for d in directs:
    if d.contains("module_b"):
        found = true
expect(found).to_equal(true)
```

</details>

### transitive scanning

#### module_a transitive set includes common.spl

- visited =  scan file recursive
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_a = FIXTURE_DIR + "/module_a.spl"
var visited: {text: bool} = {}
visited = _scan_file_recursive(module_a, visited)
var found = false
for f in visited.keys():
    if f.contains("common"):
        found = true
expect(found).to_equal(true)
```

</details>

#### module_a transitive set includes cycle files

- visited =  scan file recursive
   - Expected: found_a is true
   - Expected: found_b is true
   - Expected: found_c is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_a = FIXTURE_DIR + "/module_a.spl"
var visited: {text: bool} = {}
visited = _scan_file_recursive(module_a, visited)
var found_a = false
var found_b = false
var found_c = false
for f in visited.keys():
    if f.contains("cycle_a"):
        found_a = true
    if f.contains("cycle_b"):
        found_b = true
    if f.contains("cycle_c"):
        found_c = true
expect(found_a).to_equal(true)
expect(found_b).to_equal(true)
expect(found_c).to_equal(true)
```

</details>

#### module_b transitive set includes common.spl

- visited =  scan file recursive
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_b = FIXTURE_DIR + "/module_b.spl"
var visited: {text: bool} = {}
visited = _scan_file_recursive(module_b, visited)
var found = false
for f in visited.keys():
    if f.contains("common"):
        found = true
expect(found).to_equal(true)
```

</details>

#### module_b transitive set does NOT include cycle files

- visited =  scan file recursive
   - Expected: found_cycle is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_b = FIXTURE_DIR + "/module_b.spl"
var visited: {text: bool} = {}
visited = _scan_file_recursive(module_b, visited)
var found_cycle = false
for f in visited.keys():
    if f.contains("cycle_"):
        found_cycle = true
expect(found_cycle).to_equal(false)
```

</details>

### cycle detection

#### finds at least one cycle in entry fixture graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cycles = find_cycles_in_file(ENTRY_FILE)
expect(cycles.len() > 0).to_equal(true)
```

</details>

#### cycle involves cycle_a, cycle_b, and cycle_c

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cycles = find_cycles_in_file(ENTRY_FILE)
var found_cycle = false
for cyc_path in cycles:
    var has_a = false
    var has_b = false
    var has_c = false
    for node in cyc_path:
        if node.contains("cycle_a"):
            has_a = true
        if node.contains("cycle_b"):
            has_b = true
        if node.contains("cycle_c"):
            has_c = true
    if has_a and has_b and has_c:
        found_cycle = true
expect(found_cycle).to_equal(true)
```

</details>

### shared module detection (normal mode)

#### common.spl is reachable from both module_a and module_b

- visited a =  scan file recursive
- visited b =  scan file recursive
   - Expected: shared_count >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_a = FIXTURE_DIR + "/module_a.spl"
val module_b = FIXTURE_DIR + "/module_b.spl"
var visited_a: {text: bool} = {}
visited_a = _scan_file_recursive(module_a, visited_a)
var visited_b: {text: bool} = {}
visited_b = _scan_file_recursive(module_b, visited_b)
# Count files shared between a and b
var shared_count = 0
for f in visited_a.keys():
    if visited_b.has(f):
        shared_count = shared_count + 1
# common.spl is at minimum shared
expect(shared_count >= 1).to_equal(true)
```

</details>

#### common.spl specifically is in both sets

- visited a =  scan file recursive
- visited b =  scan file recursive
   - Expected: common_in_a is true
   - Expected: common_in_b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_a = FIXTURE_DIR + "/module_a.spl"
val module_b = FIXTURE_DIR + "/module_b.spl"
var visited_a: {text: bool} = {}
visited_a = _scan_file_recursive(module_a, visited_a)
var visited_b: {text: bool} = {}
visited_b = _scan_file_recursive(module_b, visited_b)
var common_in_a = false
var common_in_b = false
for f in visited_a.keys():
    if f.contains("common"):
        common_in_a = true
for f in visited_b.keys():
    if f.contains("common"):
        common_in_b = true
expect(common_in_a).to_equal(true)
expect(common_in_b).to_equal(true)
```

</details>

### smoke: mcp main.spl has large dependency set

#### mcp/main.spl transitive file count > 30

- visited =  scan file recursive
   - Expected: count > 30 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var visited: {text: bool} = {}
visited = _scan_file_recursive(MCP_ENTRY, visited)
val all_keys = visited.keys()
val count = all_keys.len()
expect(count > 30).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/deps/deps_tool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- deps tool
- _parse_use_line
- direct imports from entry fixture
- transitive scanning
- cycle detection
- shared module detection (normal mode)
- smoke: mcp main.spl has large dependency set

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
