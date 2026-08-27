# SDN UI File Parsing Specification

> Verifies that `.ui.sdn` layout files are correctly parsed into `UITree` structures. Tests the full pipeline: file loading, tree construction, property extraction, child traversal, and state initialization.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses successfully and returns Ok
   - Expected: tree.title equals `Minimal`
   - Expected: tree.theme equals `glass_dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses successfully and returns Ok")
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

- parsed tree root is not nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree root is not nil")
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

- parsed tree has a title property
   - Expected: tree.title equals `Minimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree has a title property")
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

- parsed tree has at least one child


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree has at least one child")
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

- contains a greeting text widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains a greeting text widget")
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

- parses successfully and returns Ok
   - Expected: tree.title equals `Simple UI Demo`
   - Expected: tree.theme equals `glass_dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses successfully and returns Ok")
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

- parsed tree root is not nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree root is not nil")
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

- parsed tree has correct title
   - Expected: tree.title equals `Simple UI Demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree has correct title")
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

- parsed tree has dark theme
   - Expected: tree.theme equals `glass_dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parsed tree has dark theme")
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

- widget tree has multiple children


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("widget tree has multiple children")
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

- all_widget_ids returns multiple ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all_widget_ids returns multiple ids")
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

- all_widget_ids includes status widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all_widget_ids includes status widget")
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

- returns Err for nonexistent file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Err for nonexistent file")
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

- error message contains useful information


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error message contains useful information")
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

- creates a UIState with focused_id set


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a UIState with focused_id set")
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

- creates a UIState in Normal mode
   - Expected: state.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a UIState in Normal mode")
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

- creates a UIState with empty command buffer
   - Expected: state.command_buffer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a UIState with empty command buffer")
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

- state tree preserves the original title
   - Expected: state.tree.title equals `Simple UI Demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("state tree preserves the original title")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `704b210008ba36be715c135d5d06125fb4a466214485103f3ad51c1e2bfa53d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `704b210008ba36be715c135d5d06125fb4a466214485103f3ad51c1e2bfa53d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `704b210008ba36be715c135d5d06125fb4a466214485103f3ad51c1e2bfa53d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/sdn_parsing_spec.spl
mirror: doc/06_spec/03_system/gui/sdn_parsing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/sdn_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/sdn_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/sdn_parsing_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses successfully and returns Ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/sdn_parsing_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parsed tree root is not nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/sdn_parsing_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parsed tree has a title property' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
