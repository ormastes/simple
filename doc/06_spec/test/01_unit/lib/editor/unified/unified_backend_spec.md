# Unified Backend Specification

> <details>

<!-- sdn-diagram:id=unified_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Backend Specification

## Scenarios

### unified backend — backend_trait

#### constructs CursorPos with line and col

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = CursorPos(line: 5, col: 10)
expect(pos.line).to_equal(5)
expect(pos.col).to_equal(10)
```

</details>

#### editor_ok creates a successful result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = editor_ok("done")
expect(r.ok).to_equal(true)
expect(r.message).to_equal("done")
expect(r.changed).to_equal(true)
```

</details>

#### editor_err creates a failure result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = editor_err("fail")
expect(r.ok).to_equal(false)
expect(r.message).to_equal("fail")
expect(r.changed).to_equal(false)
```

</details>

### unified backend — edit_operation

#### creates an insert operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = op_insert(0, 0, "hello", 0, 0)
expect(op.kind == OperationKind.Insert).to_equal(true)
expect(op.content).to_equal("hello")
expect(op.cursor_after_col).to_equal(5)
```

</details>

#### creates a delete operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = op_delete(1, 3, "abc", 1, 6)
expect(op.kind == OperationKind.Delete).to_equal(true)
expect(op.replaced).to_equal("abc")
expect(op.cursor_after_col).to_equal(3)
```

</details>

#### creates a replace operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = op_replace(0, 0, "old", "new", 0, 0)
expect(op.kind == OperationKind.Replace).to_equal(true)
expect(op.content).to_equal("new")
expect(op.replaced).to_equal("old")
```

</details>

#### inverts an insert to a delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = op_insert(0, 0, "x", 0, 0)
val inv = invert_operation(op)
expect(inv.kind == OperationKind.Delete).to_equal(true)
expect(inv.replaced).to_equal("x")
```

</details>

#### inverts a delete to an insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = op_delete(0, 0, "y", 0, 0)
val inv = invert_operation(op)
expect(inv.kind == OperationKind.Insert).to_equal(true)
expect(inv.content).to_equal("y")
```

</details>

#### OperationHistory records and undoes

1. var hist = OperationHistory with defaults
   - Expected: hist.can_undo() is false
2. hist record
   - Expected: hist.can_undo() is true
   - Expected: hist.undo_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var hist = OperationHistory.with_defaults()
expect(hist.can_undo()).to_equal(false)
val op = op_insert(0, 0, "test", 0, 0)
hist.record(op)
expect(hist.can_undo()).to_equal(true)
expect(hist.undo_count()).to_equal(1)
```

</details>

#### OperationHistory redo after undo

1. var hist = OperationHistory with defaults
2. hist record
3. hist undo
   - Expected: hist.can_redo() is true
   - Expected: hist.redo_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var hist = OperationHistory.with_defaults()
val op = op_insert(0, 0, "z", 0, 0)
hist.record(op)
hist.undo()
expect(hist.can_redo()).to_equal(true)
expect(hist.redo_count()).to_equal(1)
```

</details>

### unified backend — syntax_facade

#### creates SyntaxTreeFacade

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facade = SyntaxTreeFacade.new("fn main():\n    0", "simple")
expect(facade.language_id).to_equal("simple")
```

</details>

#### parses function definitions

1. var facade = SyntaxTreeFacade new
2. facade parse
   - Expected: nodes.len() equals `2`
   - Expected: nodes[0].kind equals `function`
   - Expected: nodes[0].label equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var facade = SyntaxTreeFacade.new("fn hello():\n    0\nfn world():\n    0", "simple")
facade.parse()
val nodes = facade.outline()
expect(nodes.len()).to_equal(2)
expect(nodes[0].kind).to_equal("function")
expect(nodes[0].label).to_equal("hello")
```

</details>

#### parses class and struct definitions

1. var facade = SyntaxTreeFacade new
2. facade parse
   - Expected: nodes.len() equals `2`
   - Expected: nodes[0].kind equals `class`
   - Expected: nodes[1].kind equals `struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var facade = SyntaxTreeFacade.new("class Foo:\n    x: i64\nstruct Bar:\n    y: text", "simple")
facade.parse()
val nodes = facade.outline()
expect(nodes.len()).to_equal(2)
expect(nodes[0].kind).to_equal("class")
expect(nodes[1].kind).to_equal("struct")
```

</details>

#### skips non-simple languages

1. var facade = SyntaxTreeFacade new
2. facade parse
   - Expected: facade.outline().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var facade = SyntaxTreeFacade.new("function foo() {}", "javascript")
facade.parse()
expect(facade.outline().len()).to_equal(0)
```

</details>

### unified backend — project_navigator

#### creates ProjectNavigator with empty root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = ProjectNavigator.new("")
expect(nav.entry_count()).to_equal(0)
expect(nav.total_count()).to_equal(0)
```

</details>

#### selected_path returns empty for no entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nav = ProjectNavigator.new("")
expect(nav.selected_path()).to_equal("")
```

</details>

### unified backend — unified_backend

#### creates UnifiedEditorBackend with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = UnifiedEditorBackend.new()
expect(be.get_config("theme")).to_equal("")
```

</details>

#### sets and gets config

1. var be = UnifiedEditorBackend new
2. be set config
   - Expected: be.get_config("theme") equals `dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var be = UnifiedEditorBackend.new()
be.set_config("theme", "dark")
expect(be.get_config("theme")).to_equal("dark")
```

</details>

#### sets config and overwrites existing key

1. var be = UnifiedEditorBackend new
2. be set config
   - Expected: be.get_config("indent") equals `4`
3. be set config
   - Expected: be.get_config("indent") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var be = UnifiedEditorBackend.new()
be.set_config("indent", "4")
expect(be.get_config("indent")).to_equal("4")
be.set_config("indent", "2")
expect(be.get_config("indent")).to_equal("2")
```

</details>

### unified backend — tui_adapter

#### TuiEditorAdapter wraps backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = UnifiedEditorBackend.new()
val tui = TuiEditorAdapter.new(be)
expect(tui.terminal_rows).to_equal(24)
expect(tui.terminal_cols).to_equal(80)
```

</details>

#### TuiEditorAdapter handles quit key

1. var tui = TuiEditorAdapter new
   - Expected: result.ok is true
   - Expected: result.message equals `quit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = UnifiedEditorBackend.new()
var tui = TuiEditorAdapter.new(be)
val result = tui.handle_key("q")
expect(result.ok).to_equal(true)
expect(result.message).to_equal("quit")
```

</details>

### unified backend — vscode_adapter

#### VscodeEditorAdapter wraps backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = UnifiedEditorBackend.new()
val vsc = VscodeEditorAdapter.new(be)
val req = VscodeRequest(method: "unknown_method", path: "", content: "", line: 0, col: 0, count: 0, query: "")
val resp = vsc.dispatch(req)
expect(resp.ok).to_equal(false)
expect(resp.message).to_contain("Unknown method")
```

</details>

#### VscodeAdapter config round-trip

1. var vsc = VscodeEditorAdapter new
   - Expected: set_resp.ok is true
   - Expected: get_resp.ok is true
   - Expected: get_resp.data equals `dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = UnifiedEditorBackend.new()
var vsc = VscodeEditorAdapter.new(be)
val set_req = VscodeRequest(method: "config_set", path: "", content: "dark", line: 0, col: 0, count: 0, query: "theme")
val set_resp = vsc.dispatch(set_req)
expect(set_resp.ok).to_equal(true)
val get_req = VscodeRequest(method: "config_get", path: "", content: "", line: 0, col: 0, count: 0, query: "theme")
val get_resp = vsc.dispatch(get_req)
expect(get_resp.ok).to_equal(true)
expect(get_resp.data).to_equal("dark")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/unified/unified_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- unified backend — backend_trait
- unified backend — edit_operation
- unified backend — syntax_facade
- unified backend — project_navigator
- unified backend — unified_backend
- unified backend — tui_adapter
- unified backend — vscode_adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
