# Surface Specification

> 1. expect sm surface count

<!-- sdn-diagram:id=surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

surface_spec -> std
surface_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Surface Specification

## Scenarios

### SurfaceManager creation

#### creates empty manager

1. expect sm surface count
2. expect sm active


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = new_surface_manager()
expect sm.surface_count() to_equal 0
expect sm.active() to_equal "main"
```

</details>

### SurfaceManager open

#### opens a surface and increments count

1. var sm = new surface manager
2. expect sm surface count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_open_root", "Hello")
val tree = UITree.new(root)
val handle = sm.open("window1", tree)
expect sm.surface_count() to_equal 1
expect handle.id to_equal "window1"
expect handle.generation to_equal 1
```

</details>

#### opens multiple surfaces

1. var sm = new surface manager
2. sm open
3. sm open
4. expect sm surface count
5. expect sm has
6. expect sm has


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root1 = text_widget("sm_multi_r1", "One")
val root2 = text_widget("sm_multi_r2", "Two")
val tree1 = UITree.new(root1)
val tree2 = UITree.new(root2)
sm.open("win_a", tree1)
sm.open("win_b", tree2)
expect sm.surface_count() to_equal 2
expect sm.has("win_a") to_equal true
expect sm.has("win_b") to_equal true
```

</details>

### SurfaceManager get

#### gets tree for an existing surface

1. var sm = new surface manager
2. sm open


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_get_root", "Content")
val tree = UITree.new(root)
sm.open("panel1", tree)
val found = sm.get("panel1")
expect found != nil to_equal true
```

</details>

#### returns nil for nonexistent surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = new_surface_manager()
val found = sm.get("sm_get_missing")
expect found to_be_nil
```

</details>

### SurfaceManager close

#### closes a surface and decrements count

1. var sm = new surface manager
2. expect sm surface count
3. expect sm surface count
4. expect sm has


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_close_root", "Bye")
val tree = UITree.new(root)
val handle = sm.open("temp_win", tree)
expect sm.surface_count() to_equal 1
val result = sm.close(handle)
expect result to_equal true
expect sm.surface_count() to_equal 0
expect sm.has("temp_win") to_equal false
```

</details>

#### resets active to main when closing active surface

1. var sm = new surface manager
2. sm set active
3. expect sm active
4. sm close
5. expect sm active


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_close_active_r", "Active")
val tree = UITree.new(root)
val handle = sm.open("popup", tree)
sm.set_active("popup")
expect sm.active() to_equal "popup"
sm.close(handle)
expect sm.active() to_equal "main"
```

</details>

### SurfaceManager handle validation

#### validates a fresh handle

1. var sm = new surface manager
2. expect sm validate handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_valid_root", "Test")
val tree = UITree.new(root)
val handle = sm.open("validated", tree)
expect sm.validate_handle(handle) to_equal true
```

</details>

#### invalidates handle after close

1. var sm = new surface manager
2. sm close
3. expect sm validate handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_stale_root", "Stale")
val tree = UITree.new(root)
val handle = sm.open("stale_win", tree)
sm.close(handle)
expect sm.validate_handle(handle) to_equal false
```

</details>

#### invalidates old handle when surface is re-opened

1. var sm = new surface manager
2. expect sm validate handle
3. expect sm validate handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root1 = text_widget("sm_reopen_r1", "V1")
val root2 = text_widget("sm_reopen_r2", "V2")
val tree1 = UITree.new(root1)
val tree2 = UITree.new(root2)
val old_handle = sm.open("reopen_win", tree1)
val new_handle = sm.open("reopen_win", tree2)
expect sm.validate_handle(old_handle) to_equal false
expect sm.validate_handle(new_handle) to_equal true
```

</details>

#### rejects close with stale handle

1. var sm = new surface manager
2. sm close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_reject_root", "Reject")
val tree = UITree.new(root)
val handle = sm.open("reject_win", tree)
sm.close(handle)
# Try to close again with stale handle
val result = sm.close(handle)
expect result to_equal false
```

</details>

### SurfaceManager active surface

#### defaults to main

1. expect sm active


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sm = new_surface_manager()
expect sm.active() to_equal "main"
```

</details>

#### switches active to existing surface

1. var sm = new surface manager
2. sm open
3. sm set active
4. expect sm active


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val root = text_widget("sm_active_root", "Active")
val tree = UITree.new(root)
sm.open("dialog", tree)
sm.set_active("dialog")
expect sm.active() to_equal "dialog"
```

</details>

#### does not switch to nonexistent surface

1. var sm = new surface manager
2. sm set active
3. expect sm active


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
sm.set_active("sm_active_ghost")
expect sm.active() to_equal "main"
```

</details>

### SurfaceManager surface_ids

#### returns all surface ids

1. var sm = new surface manager
2. sm open
3. sm open
4. sm open
5. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sm = new_surface_manager()
val r1 = text_widget("sm_ids_r1", "A")
val r2 = text_widget("sm_ids_r2", "B")
val r3 = text_widget("sm_ids_r3", "C")
sm.open("alpha", UITree.new(r1))
sm.open("beta", UITree.new(r2))
sm.open("gamma", UITree.new(r3))
val ids = sm.surface_ids()
expect ids.len() to_equal 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SurfaceManager creation
- SurfaceManager open
- SurfaceManager get
- SurfaceManager close
- SurfaceManager handle validation
- SurfaceManager active surface
- SurfaceManager surface_ids

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
