# plugin_startup_block_spec

> Plugin Startup Block — AC-2 Real-Module Spec

<!-- sdn-diagram:id=plugin_startup_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_startup_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_startup_block_spec -> std
plugin_startup_block_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_startup_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# plugin_startup_block_spec

Plugin Startup Block — AC-2 Real-Module Spec

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC2-BLOCK-PLUGIN-REAL |
| Category | Plugin / BlockRegistry / plugin_startup |
| Status | Phase 5 — real module integration |
| Source | `test/03_system/feature/plugin/plugin_startup_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Plugin Startup Block — AC-2 Real-Module Spec

Imports the actual plugin_startup.spl and BlockRegistry to verify the
two-phase loading contract against the real implementation.
Complements custom_block_plugin_spec.spl (which uses local doubles).

## Scenarios

### AC-2: plugin_startup two-phase contract (real module)

#### activate_plugin fires hook and registers block via real registry

1. fn csv setup
2. register simple plugin
   - Expected: is_block("csv") is false
   - Expected: ok is true
   - Expected: is_block("csv") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensure clean state: csv may have been registered by a prior test run
val _pre = unregister_block("csv")

# Phase 1: register the pure-Simple plugin hook
fn csv_setup() -> bool:
    val block = define_block("csv", LexerMode.Raw, Ok(_1.trim()))
    # register_block returns true on success, false if already taken
    val registered = register_block(block)
    registered

register_simple_plugin("csv_plugin_real", csv_setup)

# Before activate: block must NOT be in registry
expect(is_block("csv")).to_equal(false)

# Phase 2: activate the plugin
val ok = activate_plugin("csv_plugin_real")
expect(ok).to_equal(true)

# After activate: block IS in registry
expect(is_block("csv")).to_equal(true)

# Cleanup: leave registry clean for other tests
val _post = unregister_block("csv")
```

</details>

#### activate_plugin returns false for unknown plugin name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = activate_plugin("__nonexistent_plugin_xyz__")
expect(result).to_equal(false)
```

</details>

#### register_block returns false for already-taken keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Register once
val _pre = unregister_block("csv_dup")
val block1 = define_block("csv_dup", LexerMode.Raw, Ok(_1.trim()))
val first = register_block(block1)
expect(first).to_equal(true)

# Register again — must be rejected
val block2 = define_block("csv_dup", LexerMode.Raw, Ok(_1.trim()))
val second = register_block(block2)
expect(second).to_equal(false)

# Cleanup
val _post = unregister_block("csv_dup")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
