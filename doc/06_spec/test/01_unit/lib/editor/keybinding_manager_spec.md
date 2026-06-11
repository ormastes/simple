# Editor Keybinding Manager Tests

> @cover src/lib/editor/core/keybinding_manager.spl 80%

<!-- sdn-diagram:id=keybinding_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=keybinding_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

keybinding_manager_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=keybinding_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Keybinding Manager Tests

@cover src/lib/editor/core/keybinding_manager.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EDITOR-KB-001 |
| Category | Editor \| Core |
| Status | Implemented |
| Source | `test/01_unit/lib/editor/keybinding_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/editor/core/keybinding_manager.spl 80%
@cover src/lib/editor/common/keybindings.spl 40%

## Scenarios

### keybinding manager defaults

#### creates manager with default bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "h", "normal")
expect(cmd).to_equal("move-left")
```

</details>

#### resolves vim movement keys in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "j", "normal")).to_equal("move-down")
expect(keybinding_manager_resolve(mgr, "k", "normal")).to_equal("move-up")
expect(keybinding_manager_resolve(mgr, "l", "normal")).to_equal("move-right")
```

</details>

#### resolves line-start and line-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "0", "normal")).to_equal("move-line-start")
expect(keybinding_manager_resolve(mgr, "$", "normal")).to_equal("move-line-end")
```

</details>

#### resolves editing keys in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "i", "normal")).to_equal("enter-insert")
expect(keybinding_manager_resolve(mgr, "x", "normal")).to_equal("delete")
expect(keybinding_manager_resolve(mgr, "u", "normal")).to_equal("undo")
```

</details>

#### resolves insert mode keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "\x1b", "insert")).to_equal("exit-insert")
expect(keybinding_manager_resolve(mgr, "\x7f", "insert")).to_equal("backspace")
expect(keybinding_manager_resolve(mgr, "\r", "insert")).to_equal("newline")
```

</details>

#### resolves command mode keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "\x1b", "command")).to_equal("cancel")
expect(keybinding_manager_resolve(mgr, "\r", "command")).to_equal("execute")
```

</details>

### keybinding manager resolution

#### returns empty for unbound key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "Z", "normal")
expect(cmd).to_equal("")
```

</details>

#### returns empty for wrong mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "h", "insert")
expect(cmd).to_equal("")
```

</details>

#### returns empty for empty key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "", "normal")
expect(cmd).to_equal("")
```

</details>

### keybinding manager overrides

#### override takes precedence over default

1. var mgr = keybinding manager new
2. mgr = keybinding manager add override
   - Expected: cmd equals `custom-left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "h", command: "custom-left", mode: "normal", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
val cmd = keybinding_manager_resolve(mgr, "h", "normal")
expect(cmd).to_equal("custom-left")
```

</details>

#### non-overridden keys still resolve from defaults

1. var mgr = keybinding manager new
2. mgr = keybinding manager add override
   - Expected: cmd equals `move-down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "h", command: "custom-left", mode: "normal", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
val cmd = keybinding_manager_resolve(mgr, "j", "normal")
expect(cmd).to_equal("move-down")
```

</details>

#### mode-specific override does not affect other modes

1. var mgr = keybinding manager new
2. mgr = keybinding manager add override
   - Expected: keybinding_manager_resolve(mgr, "\r", "insert") equals `custom-enter`
   - Expected: keybinding_manager_resolve(mgr, "\r", "command") equals `execute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "\r", command: "custom-enter", mode: "insert", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
expect(keybinding_manager_resolve(mgr, "\r", "insert")).to_equal("custom-enter")
expect(keybinding_manager_resolve(mgr, "\r", "command")).to_equal("execute")
```

</details>

#### global override applies to any mode

1. var mgr = keybinding manager from config
2. mgr = keybinding manager add override
   - Expected: keybinding_manager_resolve(mgr, "F1", "normal") equals `help`
   - Expected: keybinding_manager_resolve(mgr, "F1", "insert") equals `help`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = KeybindingConfig(bindings: [])
var mgr = keybinding_manager_from_config(config)
val binding = KeyBinding(key: "F1", command: "help", mode: "", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
expect(keybinding_manager_resolve(mgr, "F1", "normal")).to_equal("help")
expect(keybinding_manager_resolve(mgr, "F1", "insert")).to_equal("help")
```

</details>

### keybinding manager mode listing

#### lists bindings for normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val normal_bindings = keybinding_manager_all_for_mode(mgr, "normal")
expect(normal_bindings.len() > 0).to_equal(true)
```

</details>

#### lists bindings for insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = keybinding_manager_new()
val insert_bindings = keybinding_manager_all_for_mode(mgr, "insert")
expect(insert_bindings.len() > 0).to_equal(true)
```

</details>

#### returns empty for unknown mode

1. KeyBinding
   - Expected: unknown.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = KeybindingConfig(bindings: [
    KeyBinding(key: "a", command: "cmd-a", mode: "normal", args: "")
])
val mgr = keybinding_manager_from_config(config)
val unknown = keybinding_manager_all_for_mode(mgr, "visual")
expect(unknown.len()).to_equal(0)
```

</details>

#### includes overrides in mode listing

1. var mgr = keybinding manager new
2. mgr = keybinding manager add override
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "F2", command: "rename", mode: "normal", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
val all_normal = keybinding_manager_all_for_mode(mgr, "normal")
var found = false
for b in all_normal:
    if b.key == "F2":
        found = true
expect(found).to_equal(true)
```

</details>

### keybinding config from scratch

#### empty config resolves nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = KeybindingConfig(bindings: [])
val mgr = keybinding_manager_from_config(config)
expect(keybinding_manager_resolve(mgr, "h", "normal")).to_equal("")
```

</details>

#### custom config resolves custom bindings

1. KeyBinding
2. KeyBinding
   - Expected: keybinding_manager_resolve(mgr, "a", "edit") equals `alpha`
   - Expected: keybinding_manager_resolve(mgr, "b", "edit") equals `beta`
   - Expected: keybinding_manager_resolve(mgr, "c", "edit") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = KeybindingConfig(bindings: [
    KeyBinding(key: "a", command: "alpha", mode: "edit", args: ""),
    KeyBinding(key: "b", command: "beta", mode: "edit", args: "")
])
val mgr = keybinding_manager_from_config(config)
expect(keybinding_manager_resolve(mgr, "a", "edit")).to_equal("alpha")
expect(keybinding_manager_resolve(mgr, "b", "edit")).to_equal("beta")
expect(keybinding_manager_resolve(mgr, "c", "edit")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
