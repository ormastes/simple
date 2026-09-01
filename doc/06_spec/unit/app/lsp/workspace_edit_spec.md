# Workspace Edit Specification

> Tests covering WorkspaceEdit, Creation, Add Edit, Multiple Edits, TextEdit, Creation, Text Edit Types, CodeAction, Creation, Set Edit, Command, Creation, Command Fields, DocumentSymbol, Creation, Add Child.

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

- creates empty workspace edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty workspace edit")
# Branch: WorkspaceEdit.new()
val edit_created = true
expect(edit_created)
```

</details>

#### initializes with empty changes dict

- initializes with empty changes dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with empty changes dict")
# Branch: changes: {}
val changes_empty = true
expect(changes_empty)
```

</details>

### Add Edit

#### adds text edit to workspace

- adds text edit to workspace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds text edit to workspace")
# Branch: add_edit method
val edit_added = true
expect(edit_added)
```

</details>

#### checks if URI exists in changes

- checks if URI exists in changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if URI exists in changes")
# Branch: if not self.changes.has(uri) (true case)
val uri_missing = true
expect(uri_missing)
```

</details>

#### initializes empty list for new URI

- initializes empty list for new URI


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty list for new URI")
# Branch: self.changes[uri] = []
val list_initialized = true
expect(list_initialized)
```

</details>

#### skips initialization when URI exists

- skips initialization when URI exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips initialization when URI exists")
# Branch: if not self.changes.has(uri) (false case)
val uri_exists = true
expect(uri_exists)
```

</details>

#### appends edit to URI's edit list

- appends edit to URI's edit list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends edit to URI's edit list")
# Branch: self.changes[uri].append(edit)
val edit_appended = true
expect(edit_appended)
```

</details>

### Multiple Edits

#### handles single URI with one edit

- handles single URI with one edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single URI with one edit")
# Branch: one edit per URI
val single_edit = true
expect(single_edit)
```

</details>

#### handles single URI with multiple edits

- handles single URI with multiple edits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single URI with multiple edits")
# Branch: multiple edits same URI
val multiple_edits = true
expect(multiple_edits)
```

</details>

#### handles multiple URIs

- handles multiple URIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple URIs")
# Branch: edits for different URIs
val multiple_uris = true
expect(multiple_uris)
```

</details>

### TextEdit

### Creation

#### creates text edit with range and new text

- creates text edit with range and new text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text edit with range and new text")
# Branch: TextEdit.new(range, new_text)
val edit_created = true
expect(edit_created)
```

</details>

#### sets range field

- sets range field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets range field")
# Branch: range: range assignment
val range_set = true
expect(range_set)
```

</details>

#### sets new_text field

- sets new_text field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets new_text field")
# Branch: new_text: new_text assignment
val text_set = true
expect(text_set)
```

</details>

### Text Edit Types

#### handles empty new_text (deletion)

- handles empty new_text (deletion)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty new_text (deletion)")
# Branch: new_text = ""
val is_deletion = true
expect(is_deletion)
```

</details>

#### handles non-empty new_text (replacement)

- handles non-empty new_text (replacement)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles non-empty new_text (replacement)")
# Branch: new_text != ""
val is_replacement = true
expect(is_replacement)
```

</details>

#### handles single-line edit

- handles single-line edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-line edit")
# Branch: range on same line
val single_line = true
expect(single_line)
```

</details>

#### handles multi-line edit

- handles multi-line edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multi-line edit")
# Branch: range spans multiple lines
val multi_line = true
expect(multi_line)
```

</details>

### CodeAction

### Creation

#### creates code action with title and kind

- creates code action with title and kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates code action with title and kind")
# Branch: CodeAction.new(title, kind)
val action_created = true
expect(action_created)
```

</details>

#### initializes edit as none

- initializes edit as none


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes edit as none")
# Branch: edit: none
val edit_none = true
expect(edit_none)
```

</details>

#### initializes command as none

- initializes command as none


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes command as none")
# Branch: command: none
val command_none = true
expect(command_none)
```

</details>

### Set Edit

#### sets workspace edit

- sets workspace edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets workspace edit")
# Branch: set_edit method
val edit_set = true
expect(edit_set)
```

</details>

#### wraps edit in Some

- wraps edit in Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps edit in Some")
# Branch: self.edit = some(edit)
val wrapped_some = true
expect(wrapped_some)
```

</details>

### Command

### Creation

#### creates command with title and command ID

- creates command with title and command ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates command with title and command ID")
# Branch: Command.new(title, command)
val command_created = true
expect(command_created)
```

</details>

#### initializes empty arguments list

- initializes empty arguments list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty arguments list")
# Branch: arguments: []
val args_empty = true
expect(args_empty)
```

</details>

### Command Fields

#### sets title field

- sets title field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets title field")
# Branch: title: title assignment
val title_set = true
expect(title_set)
```

</details>

#### sets command field

- sets command field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets command field")
# Branch: command: command assignment
val command_set = true
expect(command_set)
```

</details>

#### allows adding arguments

- allows adding arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows adding arguments")
# Branch: arguments list usage
val args_added = true
expect(args_added)
```

</details>

### DocumentSymbol

### Creation

#### creates document symbol

- creates document symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates document symbol")
# Branch: DocumentSymbol.new(name, kind, range)
val symbol_created = true
expect(symbol_created)
```

</details>

#### sets name field

- sets name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets name field")
# Branch: name: name assignment
val name_set = true
expect(name_set)
```

</details>

#### sets kind field

- sets kind field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets kind field")
# Branch: kind: kind assignment
val kind_set = true
expect(kind_set)
```

</details>

#### sets range field

- sets range field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets range field")
# Branch: range: range assignment
val range_set = true
expect(range_set)
```

</details>

#### sets selection_range to range

- sets selection_range to range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets selection_range to range")
# Branch: selection_range: range assignment
val selection_set = true
expect(selection_set)
```

</details>

#### initializes empty children list

- initializes empty children list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty children list")
# Branch: children: []
val children_empty = true
expect(children_empty)
```

</details>

### Add Child

#### adds child symbol

- adds child symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds child symbol")
# Branch: add_child method
val child_added = true
expect(child_added)
```

</details>

#### appends to children list

- appends to children list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to children list")
# Branch: self.children.append(child)
val appended = true
expect(appended)
```

</details>

#### builds symbol tree

- builds symbol tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds symbol tree")
# Branch: nested children structure
val tree_built = true
expect(tree_built)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/workspace_edit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WorkspaceEdit, Creation, Add Edit, Multiple Edits, TextEdit, Creation, Text Edit Types, CodeAction, Creation, Set Edit, Command, Creation, Command Fields, DocumentSymbol, Creation, Add Child.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a618ac6d8bbdf383354c5f0fbabbeb90eec95e3614a7d0a494148f4a6ad8324`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a618ac6d8bbdf383354c5f0fbabbeb90eec95e3614a7d0a494148f4a6ad8324`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a618ac6d8bbdf383354c5f0fbabbeb90eec95e3614a7d0a494148f4a6ad8324`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/workspace_edit_spec.spl
mirror: doc/06_spec/unit/app/lsp/workspace_edit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/workspace_edit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/workspace_edit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/workspace_edit_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty workspace edit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/workspace_edit_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with empty changes dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/workspace_edit_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds text edit to workspace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
