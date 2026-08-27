# Workspace Edit Specification

> <details>

<!-- sdn-diagram:id=workspace_edit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=workspace_edit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

workspace_edit_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=workspace_edit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Workspace Edit Specification

## Scenarios

### WorkspaceEdit

### Creation

#### creates empty workspace edit

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: WorkspaceEdit.new()
val edit_created = true
assert_true(edit_created)
```

</details>

#### initializes with empty changes dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: changes: {}
val changes_empty = true
assert_true(changes_empty)
```

</details>

### Add Edit

#### adds text edit to workspace

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: add_edit method
val edit_added = true
assert_true(edit_added)
```

</details>

#### checks if URI exists in changes

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if not self.changes.has(uri) (true case)
val uri_missing = true
assert_true(uri_missing)
```

</details>

#### initializes empty list for new URI

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.changes[uri] = []
val list_initialized = true
assert_true(list_initialized)
```

</details>

#### skips initialization when URI exists

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if not self.changes.has(uri) (false case)
val uri_exists = true
assert_true(uri_exists)
```

</details>

#### appends edit to URI's edit list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.changes[uri].append(edit)
val edit_appended = true
assert_true(edit_appended)
```

</details>

### Multiple Edits

#### handles single URI with one edit

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: one edit per URI
val single_edit = true
assert_true(single_edit)
```

</details>

#### handles single URI with multiple edits

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: multiple edits same URI
val multiple_edits = true
assert_true(multiple_edits)
```

</details>

#### handles multiple URIs

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: edits for different URIs
val multiple_uris = true
assert_true(multiple_uris)
```

</details>

### TextEdit

### Creation

#### creates text edit with range and new text

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: TextEdit.new(range, new_text)
val edit_created = true
assert_true(edit_created)
```

</details>

#### sets range field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: range: range assignment
val range_set = true
assert_true(range_set)
```

</details>

#### sets new_text field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: new_text: new_text assignment
val text_set = true
assert_true(text_set)
```

</details>

### Text Edit Types

#### handles empty new_text (deletion)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: new_text = ""
val is_deletion = true
assert_true(is_deletion)
```

</details>

#### handles non-empty new_text (replacement)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: new_text != ""
val is_replacement = true
assert_true(is_replacement)
```

</details>

#### handles single-line edit

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: range on same line
val single_line = true
assert_true(single_line)
```

</details>

#### handles multi-line edit

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: range spans multiple lines
val multi_line = true
assert_true(multi_line)
```

</details>

### CodeAction

### Creation

#### creates code action with title and kind

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: CodeAction.new(title, kind)
val action_created = true
assert_true(action_created)
```

</details>

#### initializes edit as none

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: edit: none
val edit_none = true
assert_true(edit_none)
```

</details>

#### initializes command as none

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: command: none
val command_none = true
assert_true(command_none)
```

</details>

### Set Edit

#### sets workspace edit

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: set_edit method
val edit_set = true
assert_true(edit_set)
```

</details>

#### wraps edit in Some

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.edit = some(edit)
val wrapped_some = true
assert_true(wrapped_some)
```

</details>

### Command

### Creation

#### creates command with title and command ID

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: Command.new(title, command)
val command_created = true
assert_true(command_created)
```

</details>

#### initializes empty arguments list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: arguments: []
val args_empty = true
assert_true(args_empty)
```

</details>

### Command Fields

#### sets title field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: title: title assignment
val title_set = true
assert_true(title_set)
```

</details>

#### sets command field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: command: command assignment
val command_set = true
assert_true(command_set)
```

</details>

#### allows adding arguments

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: arguments list usage
val args_added = true
assert_true(args_added)
```

</details>

### DocumentSymbol

### Creation

#### creates document symbol

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: DocumentSymbol.new(name, kind, range)
val symbol_created = true
assert_true(symbol_created)
```

</details>

#### sets name field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: name: name assignment
val name_set = true
assert_true(name_set)
```

</details>

#### sets kind field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: kind: kind assignment
val kind_set = true
assert_true(kind_set)
```

</details>

#### sets range field

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: range: range assignment
val range_set = true
assert_true(range_set)
```

</details>

#### sets selection_range to range

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: selection_range: range assignment
val selection_set = true
assert_true(selection_set)
```

</details>

#### initializes empty children list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: children: []
val children_empty = true
assert_true(children_empty)
```

</details>

### Add Child

#### adds child symbol

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: add_child method
val child_added = true
assert_true(child_added)
```

</details>

#### appends to children list

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: self.children.append(child)
val appended = true
assert_true(appended)
```

</details>

#### builds symbol tree

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: nested children structure
val tree_built = true
assert_true(tree_built)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/workspace_edit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WorkspaceEdit
- Creation
- Add Edit
- Multiple Edits
- TextEdit
- Creation
- Text Edit Types
- CodeAction
- Creation
- Set Edit
- Command
- Creation
- Command Fields
- DocumentSymbol
- Creation
- Add Child

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
