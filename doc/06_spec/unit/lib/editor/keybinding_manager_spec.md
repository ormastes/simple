# Keybinding Manager Specification

> Tests covering keybinding manager defaults, keybinding manager resolution, keybinding manager overrides, keybinding manager mode listing, keybinding config from scratch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keybinding Manager Specification

## Scenarios

### keybinding manager defaults

#### creates manager with default bindings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates manager with default bindings
   - Expected: cmd equals `move-left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates manager with default bindings")
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "h", "normal")
expect(cmd).to_equal("move-left")
```

</details>

#### resolves vim movement keys in normal mode

- resolves vim movement keys in normal mode
   - Expected: keybinding_manager_resolve(mgr, "j", "normal") equals `move-down`
   - Expected: keybinding_manager_resolve(mgr, "k", "normal") equals `move-up`
   - Expected: keybinding_manager_resolve(mgr, "l", "normal") equals `move-right`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves vim movement keys in normal mode")
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "j", "normal")).to_equal("move-down")
expect(keybinding_manager_resolve(mgr, "k", "normal")).to_equal("move-up")
expect(keybinding_manager_resolve(mgr, "l", "normal")).to_equal("move-right")
```

</details>

#### resolves line-start and line-end

- resolves line-start and line-end
   - Expected: keybinding_manager_resolve(mgr, "0", "normal") equals `move-line-start`
   - Expected: keybinding_manager_resolve(mgr, "$", "normal") equals `move-line-end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves line-start and line-end")
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "0", "normal")).to_equal("move-line-start")
expect(keybinding_manager_resolve(mgr, "$", "normal")).to_equal("move-line-end")
```

</details>

#### resolves editing keys in normal mode

- resolves editing keys in normal mode
   - Expected: keybinding_manager_resolve(mgr, "i", "normal") equals `enter-insert`
   - Expected: keybinding_manager_resolve(mgr, "x", "normal") equals `delete`
   - Expected: keybinding_manager_resolve(mgr, "u", "normal") equals `undo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves editing keys in normal mode")
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "i", "normal")).to_equal("enter-insert")
expect(keybinding_manager_resolve(mgr, "x", "normal")).to_equal("delete")
expect(keybinding_manager_resolve(mgr, "u", "normal")).to_equal("undo")
```

</details>

#### resolves insert mode keys

- resolves insert mode keys
   - Expected: keybinding_manager_resolve(mgr, "\x1b", "insert") equals `exit-insert`
   - Expected: keybinding_manager_resolve(mgr, "\x7f", "insert") equals `backspace`
   - Expected: keybinding_manager_resolve(mgr, "\r", "insert") equals `newline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves insert mode keys")
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "\x1b", "insert")).to_equal("exit-insert")
expect(keybinding_manager_resolve(mgr, "\x7f", "insert")).to_equal("backspace")
expect(keybinding_manager_resolve(mgr, "\r", "insert")).to_equal("newline")
```

</details>

#### resolves command mode keys

- resolves command mode keys
   - Expected: keybinding_manager_resolve(mgr, "\x1b", "command") equals `cancel`
   - Expected: keybinding_manager_resolve(mgr, "\r", "command") equals `execute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves command mode keys")
val mgr = keybinding_manager_new()
expect(keybinding_manager_resolve(mgr, "\x1b", "command")).to_equal("cancel")
expect(keybinding_manager_resolve(mgr, "\r", "command")).to_equal("execute")
```

</details>

### keybinding manager resolution

#### returns empty for unbound key

- returns empty for unbound key
   - Expected: cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unbound key")
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "Z", "normal")
expect(cmd).to_equal("")
```

</details>

#### returns empty for wrong mode

- returns empty for wrong mode
   - Expected: cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for wrong mode")
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "h", "insert")
expect(cmd).to_equal("")
```

</details>

#### returns empty for empty key

- returns empty for empty key
   - Expected: cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty key")
val mgr = keybinding_manager_new()
val cmd = keybinding_manager_resolve(mgr, "", "normal")
expect(cmd).to_equal("")
```

</details>

### keybinding manager overrides

#### override takes precedence over default

- override takes precedence over default
   - Expected: cmd equals `custom-left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("override takes precedence over default")
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "h", command: "custom-left", mode: "normal", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
val cmd = keybinding_manager_resolve(mgr, "h", "normal")
expect(cmd).to_equal("custom-left")
```

</details>

#### non-overridden keys still resolve from defaults

- non-overridden keys still resolve from defaults
   - Expected: cmd equals `move-down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-overridden keys still resolve from defaults")
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "h", command: "custom-left", mode: "normal", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
val cmd = keybinding_manager_resolve(mgr, "j", "normal")
expect(cmd).to_equal("move-down")
```

</details>

#### mode-specific override does not affect other modes

- mode-specific override does not affect other modes
   - Expected: keybinding_manager_resolve(mgr, "\r", "insert") equals `custom-enter`
   - Expected: keybinding_manager_resolve(mgr, "\r", "command") equals `execute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mode-specific override does not affect other modes")
var mgr = keybinding_manager_new()
val binding = KeyBinding(key: "\r", command: "custom-enter", mode: "insert", args: "")
mgr = keybinding_manager_add_override(mgr, binding)
expect(keybinding_manager_resolve(mgr, "\r", "insert")).to_equal("custom-enter")
expect(keybinding_manager_resolve(mgr, "\r", "command")).to_equal("execute")
```

</details>

#### global override applies to any mode

- global override applies to any mode
   - Expected: keybinding_manager_resolve(mgr, "F1", "normal") equals `help`
   - Expected: keybinding_manager_resolve(mgr, "F1", "insert") equals `help`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("global override applies to any mode")
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

- lists bindings for normal mode
   - Expected: normal_bindings.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists bindings for normal mode")
val mgr = keybinding_manager_new()
val normal_bindings = keybinding_manager_all_for_mode(mgr, "normal")
expect(normal_bindings.len() > 0).to_equal(true)
```

</details>

#### lists bindings for insert mode

- lists bindings for insert mode
   - Expected: insert_bindings.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists bindings for insert mode")
val mgr = keybinding_manager_new()
val insert_bindings = keybinding_manager_all_for_mode(mgr, "insert")
expect(insert_bindings.len() > 0).to_equal(true)
```

</details>

#### returns empty for unknown mode

- returns empty for unknown mode
   - Expected: unknown.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown mode")
val config = KeybindingConfig(bindings: [
    KeyBinding(key: "a", command: "cmd-a", mode: "normal", args: "")
])
val mgr = keybinding_manager_from_config(config)
val unknown = keybinding_manager_all_for_mode(mgr, "visual")
expect(unknown.len()).to_equal(0)
```

</details>

#### includes overrides in mode listing

- includes overrides in mode listing
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes overrides in mode listing")
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

- empty config resolves nothing
   - Expected: keybinding_manager_resolve(mgr, "h", "normal") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty config resolves nothing")
val config = KeybindingConfig(bindings: [])
val mgr = keybinding_manager_from_config(config)
expect(keybinding_manager_resolve(mgr, "h", "normal")).to_equal("")
```

</details>

#### custom config resolves custom bindings

- custom config resolves custom bindings
   - Expected: keybinding_manager_resolve(mgr, "a", "edit") equals `alpha`
   - Expected: keybinding_manager_resolve(mgr, "b", "edit") equals `beta`
   - Expected: keybinding_manager_resolve(mgr, "c", "edit") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom config resolves custom bindings")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/editor/keybinding_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering keybinding manager defaults, keybinding manager resolution, keybinding manager overrides, keybinding manager mode listing, keybinding config from scratch.
- keybinding manager defaults
- keybinding manager resolution
- keybinding manager overrides
- keybinding manager mode listing
- keybinding config from scratch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `dd1a482481f334f346e762c5c3b82619426d00baed49168d1074c80e1c2e7c56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd1a482481f334f346e762c5c3b82619426d00baed49168d1074c80e1c2e7c56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd1a482481f334f346e762c5c3b82619426d00baed49168d1074c80e1c2e7c56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/editor/keybinding_manager_spec.spl
mirror: doc/06_spec/unit/lib/editor/keybinding_manager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/editor/keybinding_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/editor/keybinding_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/editor/keybinding_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/editor/keybinding_manager_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates manager with default bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/keybinding_manager_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves vim movement keys in normal mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/keybinding_manager_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves line-start and line-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
