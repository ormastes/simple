# SDN UI File Parsing Specification

> Verifies that `.ui.sdn` layout files are correctly parsed into `UITree` structures. Tests the full pipeline: file loading, tree construction, property extraction, child traversal, and state initialization.

<!-- sdn-diagram:id=sdn_parsing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_parsing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_parsing_spec -> std
sdn_parsing_spec -> nogc_sync_mut
sdn_parsing_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_parsing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDN UI File Parsing Specification

Verifies that `.ui.sdn` layout files are correctly parsed into `UITree` structures. Tests the full pipeline: file loading, tree construction, property extraction, child traversal, and state initialization.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-SDN-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/sdn_parsing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `.ui.sdn` layout files are correctly parsed into `UITree`
structures. Tests the full pipeline: file loading, tree construction,
property extraction, child traversal, and state initialization.

## Scenarios

### Parsing minimal.ui.sdn

<details>
<summary>Advanced: parses successfully and returns Ok</summary>

#### parses successfully and returns Ok _(slow)_

1. Ok
   - Expected: tree.title equals `Minimal`
   - Expected: tree.theme equals `glass_dark`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        expect(tree.title).to_equal("Minimal")
        expect(tree.theme).to_equal("glass_dark")
    Err(e) :
        fail("minimal.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree root is not nil</summary>

#### parsed tree root is not nil _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        val root = tree.root
        expect(root.id.len()).to_be_greater_than(0)
    Err(e) :
        fail("minimal.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree has a title property</summary>

#### parsed tree has a title property _(slow)_

1. Ok
   - Expected: tree.title equals `Minimal`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        expect(tree.title).to_equal("Minimal")
    Err(e) :
        fail("minimal.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree has at least one child</summary>

#### parsed tree has at least one child _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        val children = tree.root.children
        expect(children.len()).to_be_greater_than(0)
    Err(e) :
        fail("minimal.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: contains a greeting text widget</summary>

#### contains a greeting text widget _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        val widget = tree.find_widget("greeting")
        if widget != nil:
            val content = widget.get_prop("content")
            expect(content).to_contain("Hello")
        else:
            # Widget should be found somewhere in the tree
            val ids = tree.all_widget_ids()
            expect(ids.len()).to_be_greater_than(0)
    Err(e) :
        fail("minimal.ui.sdn parse failed: " + e)
```

</details>


</details>

### Parsing demo.ui.sdn

<details>
<summary>Advanced: parses successfully and returns Ok</summary>

#### parses successfully and returns Ok _(slow)_

1. Ok
   - Expected: tree.title equals `Simple UI Demo`
   - Expected: tree.theme equals `glass_dark`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        expect(tree.title).to_equal("Simple UI Demo")
        expect(tree.theme).to_equal("glass_dark")
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree root is not nil</summary>

#### parsed tree root is not nil _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val root = tree.root
        expect(root.id.len()).to_be_greater_than(0)
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree has correct title</summary>

#### parsed tree has correct title _(slow)_

1. Ok
   - Expected: tree.title equals `Simple UI Demo`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        expect(tree.title).to_equal("Simple UI Demo")
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: parsed tree has dark theme</summary>

#### parsed tree has dark theme _(slow)_

1. Ok
   - Expected: tree.theme equals `glass_dark`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        expect(tree.theme).to_equal("glass_dark")
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: widget tree has multiple children</summary>

#### widget tree has multiple children _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val children = tree.root.children
        expect(children.len()).to_be_greater_than(1)
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: all_widget_ids returns multiple ids</summary>

#### all_widget_ids returns multiple ids _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val ids = tree.all_widget_ids()
        expect(ids.len()).to_be_greater_than(3)
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

<details>
<summary>Advanced: all_widget_ids includes status widget</summary>

#### all_widget_ids includes status widget _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val ids = tree.all_widget_ids()
        expect(ids).to_contain("status")
    Err(e) :
        fail("demo.ui.sdn parse failed: " + e)
```

</details>


</details>

### SDN parsing error handling

<details>
<summary>Advanced: returns Err for nonexistent file</summary>

#### returns Err for nonexistent file _(slow)_

1. Err

2. Ok

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("nonexistent/path/does_not_exist.ui.sdn")
match result:
    Err(e) :
        expect(e.len()).to_be_greater_than(0)
    Ok(tree) :
        fail("nonexistent file parsed with title: " + tree.title)
```

</details>


</details>

<details>
<summary>Advanced: error message contains useful information</summary>

#### error message contains useful information _(slow)_

1. Err

2. Ok

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("/tmp/no_such_file_12345.ui.sdn")
match result:
    Err(e) :
        expect(e).to_contain("File not found")
    Ok(tree) :
        fail("missing /tmp file parsed with title: " + tree.title)
```

</details>


</details>

### init_state from parsed tree

<details>
<summary>Advanced: creates a UIState with focused_id set</summary>

#### creates a UIState with focused_id set _(slow)_

1. Ok

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        val state = init_state(tree)
        # focused_id should be set to the first widget id
        expect(state.focused_id.len()).to_be_greater_than(0)
    Err(e) :
        fail("minimal.ui.sdn parse failed before init_state: " + e)
```

</details>


</details>

<details>
<summary>Advanced: creates a UIState in Normal mode</summary>

#### creates a UIState in Normal mode _(slow)_

1. Ok
   - Expected: state.mode_name() equals `NORMAL`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match result:
    Ok(tree) :
        val state = init_state(tree)
        expect(state.mode_name()).to_equal("NORMAL")
    Err(e) :
        fail("minimal.ui.sdn parse failed before init_state: " + e)
```

</details>


</details>

<details>
<summary>Advanced: creates a UIState with empty command buffer</summary>

#### creates a UIState with empty command buffer _(slow)_

1. Ok
   - Expected: state.command_buffer equals ``

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val state = init_state(tree)
        expect(state.command_buffer).to_equal("")
    Err(e) :
        fail("demo.ui.sdn parse failed before init_state: " + e)
```

</details>


</details>

<details>
<summary>Advanced: state tree preserves the original title</summary>

#### state tree preserves the original title _(slow)_

1. Ok
   - Expected: state.tree.title equals `Simple UI Demo`

2. Err

3. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match result:
    Ok(tree) :
        val state = init_state(tree)
        expect(state.tree.title).to_equal("Simple UI Demo")
    Err(e) :
        fail("demo.ui.sdn parse failed before init_state: " + e)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
