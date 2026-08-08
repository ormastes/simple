# custom_block_plugin_spec

> Custom Block Plugin — AC-2 Spec

<!-- sdn-diagram:id=custom_block_plugin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_block_plugin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_block_plugin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_block_plugin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# custom_block_plugin_spec

Custom Block Plugin — AC-2 Spec

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC2-BLOCK-PLUGIN |
| Category | Plugin / BlockRegistry |
| Status | Planned (Phase 5 implements; Phase 4 specifies) |
| Source | `test/03_system/feature/plugin/custom_block_plugin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Custom Block Plugin — AC-2 Spec

Validates the BlockRegistry-driven plugin path using local doubles.
Phase 5 swaps doubles for real imports from
src/compiler/15.blocks/blocks/registry.spl and easy.spl.

## Scenarios

### AC-2: Custom Block Plugin — add and replace

#### new block registers and is visible

1.  reset registry
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
val _ok = register_block(csv_def)
check(is_block("csv"))
val all = list_blocks()
check(all.contains("csv"))
```

</details>

#### block parser-fn is invoked on use

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In-process path: call the parser-fn directly (end-to-end source
# compilation is not testable in interpreter mode).
val payload = "1,2,3"
val result = parse_csv(payload)
check(result == "1,2,3")
```

</details>

#### unregister_block removes the entry

1.  reset registry
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
val _ok = register_block(csv_def)
check(is_block("csv"))
val removed = unregister_block("csv")
check(removed)
check(not is_block("csv"))
```

</details>

#### with_block scope-registers and auto-cleans

1.  reset registry
2. fn body
3. is block
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
fn body() -> bool:
    is_block("csv")
val inside = with_block(csv_def, body)
check(inside)
check(not is_block("csv"))
```

</details>

#### replacing a built-in is rejected — built-in stays intact

1.  reset registry
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# register_block now returns false when keyword is already taken.
# Attempt to register a fake 'm' def; registry must reject it and
# the original built-in definition must be unchanged.
_reset_registry()
val original = get_block("m")
val fake_m = BlockDef(kind: "m", mode: "math_fake", description: "fake")
val rejected = register_block(fake_m)
# Must return false — keyword was already taken
check(not rejected)
val after = get_block("m")
# Built-in must still be present and its mode must not have changed
check(is_block("m"))
check(after.mode == original.mode)
```

</details>

#### replace flow: unregister then register succeeds with new def

1.  reset registry
2. check
3. unregister block
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_reset_registry()
val csv_v1 = BlockDef.create("csv", "raw")
val _ok1 = register_block(csv_v1)
check(is_block("csv"))
unregister_block("csv")
val csv_v2 = BlockDef(kind: "csv", mode: "normal", description: "csv v2")
val _ok2 = register_block(csv_v2)
check(is_block("csv"))
val current = get_block("csv")
check(current.mode == "normal")
check(current.description == "csv v2")
```

</details>

#### use_plugin semantics: blocks register only after explicit activate_plugin call

1.  reset registry
2.  reset plugin hooks
3. fn csv register
4. register simple plugin
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Validates the two-phase contract from plugin_startup.spl:
#   Phase 1 (index): plugin hook is registered but blocks NOT yet active
#   Phase 2 (activate): activate_plugin("csv_plugin") fires the hook,
#                       which calls register_block; is_block returns true.
#
# This scenario uses local doubles (same API shape as real module) so it
# runs in interpreter mode without importing compiler.blocks.plugin_startup.
# The companion spec plugin_startup_block_spec.spl imports the real module.
_reset_registry()
_reset_plugin_hooks()

# Phase 1: register the plugin hook (simulates module init of csv_plugin.spl)
fn csv_register() -> bool:
    val csv_def = BlockDef.create("csv", "raw")
    val _r = register_block(csv_def)
    true

register_simple_plugin("csv_plugin", csv_register)

# Before activate: block must NOT be in registry
check(not is_block("csv"))

# Phase 2: activate the plugin
val ok = activate_plugin("csv_plugin")
check(ok)

# After activate: block IS in registry
check(is_block("csv"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
