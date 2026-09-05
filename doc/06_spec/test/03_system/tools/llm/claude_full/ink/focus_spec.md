# Claude Full Focus Manager

> Mirrors the Ink root-owned focus manager and focus stack behavior.

<!-- sdn-diagram:id=focus_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=focus_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

focus_spec -> std
focus_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=focus_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Focus Manager

Mirrors the Ink root-owned focus manager and focus stack behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/focus_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the Ink root-owned focus manager and focus stack behavior.

## Scenarios

### Claude full focus manager

#### should dispatch blur and focus when active element changes

- Focus two nodes in order
- manager focus
- manager focus
   - Expected: manager.activeElement equals `second`
   - Expected: manager.focusStack.len() equals `1`
   - Expected: manager.focusStack[0] equals `first`
   - Expected: manager.dispatchLog[0] equals `first:focus:`
   - Expected: manager.dispatchLog[1] equals `first:blur:second`
   - Expected: manager.dispatchLog[2] equals `second:focus:first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Focus two nodes in order")
val manager = demoFocusTree()
manager.focus("first")
manager.focus("second")
expect(manager.activeElement).to_equal("second")
expect(manager.focusStack.len()).to_equal(1)
expect(manager.focusStack[0]).to_equal("first")
expect(manager.dispatchLog[0]).to_equal("first:focus:")
expect(manager.dispatchLog[1]).to_equal("first:blur:second")
expect(manager.dispatchLog[2]).to_equal("second:focus:first")
```

</details>

#### should ignore focus requests while disabled and blur active focus

- Disable the manager before a focus request
- manager disable
- manager focus
   - Expected: manager.activeElement equals ``
- manager enable
- manager focus
- manager blur
   - Expected: manager.activeElement equals ``
   - Expected: manager.dispatchLog[1] equals `first:blur:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Disable the manager before a focus request")
val manager = demoFocusTree()
manager.disable()
manager.focus("first")
expect(manager.activeElement).to_equal("")
manager.enable()
manager.focus("first")
manager.blur()
expect(manager.activeElement).to_equal("")
expect(manager.dispatchLog[1]).to_equal("first:blur:")
```

</details>

#### should focus only click targets with numeric tab index

- Click a non-tabbable node and then a tabbable node
- manager handleClickFocus
   - Expected: manager.activeElement equals ``
- manager handleClickFocus
   - Expected: manager.activeElement equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Click a non-tabbable node and then a tabbable node")
val manager = demoFocusTree()
manager.handleClickFocus("plain")
expect(manager.activeElement).to_equal("")
manager.handleClickFocus("first")
expect(manager.activeElement).to_equal("first")
```

</details>

#### should move focus through tabbable nodes in tree order

- Cycle forward and backward through tabbable nodes
- manager focusNext
   - Expected: manager.activeElement equals `first`
- manager focusNext
   - Expected: manager.activeElement equals `second`
- manager focusPrevious
   - Expected: manager.activeElement equals `first`
   - Expected: manager.collectTabbable("root").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cycle forward and backward through tabbable nodes")
val manager = demoFocusTree()
manager.focusNext("root")
expect(manager.activeElement).to_equal("first")
manager.focusNext("root")
expect(manager.activeElement).to_equal("second")
manager.focusPrevious("root")
expect(manager.activeElement).to_equal("first")
expect(manager.collectTabbable("root").len()).to_equal(3)
```

</details>

#### should restore the most recent mounted focus when the active node is removed

- Remove the active node and restore from the focus stack
- manager focus
- manager focus
- manager handleNodeRemoved
   - Expected: manager.activeElement equals `first`
   - Expected: manager.dispatchLog[3] equals `nested:blur:`
   - Expected: manager.dispatchLog[4] equals `first:focus:nested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the active node and restore from the focus stack")
val manager = demoFocusTree()
manager.focus("first")
manager.focus("nested")
manager.handleNodeRemoved("nested", "root")
expect(manager.activeElement).to_equal("first")
expect(manager.dispatchLog[3]).to_equal("nested:blur:")
expect(manager.dispatchLog[4]).to_equal("first:focus:nested")
```

</details>

#### should find the root node that owns the focus manager

- Walk from a descendant to the focus-manager root
   - Expected: manager.isInTree("nested", "root") is true
   - Expected: manager.getRootNode("nested") equals `root`
   - Expected: manager.getFocusManagerRoot("nested") equals `root`
   - Expected: maxFocusStack() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Walk from a descendant to the focus-manager root")
val manager = demoFocusTree()
expect(manager.isInTree("nested", "root")).to_equal(true)
expect(manager.getRootNode("nested")).to_equal("root")
expect(manager.getFocusManagerRoot("nested")).to_equal("root")
expect(maxFocusStack()).to_equal(32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
