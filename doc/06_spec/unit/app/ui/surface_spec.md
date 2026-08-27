# Surface Specification

> Tests covering SurfaceManager creation, SurfaceManager open, SurfaceManager get, SurfaceManager close, SurfaceManager handle validation, SurfaceManager active surface, SurfaceManager surface_ids.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Surface Specification

## Scenarios

### SurfaceManager creation

#### creates empty manager

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty manager")
val sm = new_surface_manager()
expect sm.surface_count() to_equal 0
expect sm.active() to_equal "main"
```

</details>

### SurfaceManager open

#### opens a surface and increments count

- opens a surface and increments count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens a surface and increments count")
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

- opens multiple surfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens multiple surfaces")
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

- gets tree for an existing surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets tree for an existing surface")
var sm = new_surface_manager()
val root = text_widget("sm_get_root", "Content")
val tree = UITree.new(root)
sm.open("panel1", tree)
val found = sm.get("panel1")
expect found != nil to_equal true
```

</details>

#### returns nil for nonexistent surface

- returns nil for nonexistent surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for nonexistent surface")
val sm = new_surface_manager()
val found = sm.get("sm_get_missing")
expect found to_be_nil
```

</details>

### SurfaceManager close

#### closes a surface and decrements count

- closes a surface and decrements count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes a surface and decrements count")
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

- resets active to main when closing active surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets active to main when closing active surface")
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

- validates a fresh handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a fresh handle")
var sm = new_surface_manager()
val root = text_widget("sm_valid_root", "Test")
val tree = UITree.new(root)
val handle = sm.open("validated", tree)
expect sm.validate_handle(handle) to_equal true
```

</details>

#### invalidates handle after close

- invalidates handle after close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates handle after close")
var sm = new_surface_manager()
val root = text_widget("sm_stale_root", "Stale")
val tree = UITree.new(root)
val handle = sm.open("stale_win", tree)
sm.close(handle)
expect sm.validate_handle(handle) to_equal false
```

</details>

#### invalidates old handle when surface is re-opened

- invalidates old handle when surface is re-opened


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates old handle when surface is re-opened")
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

- rejects close with stale handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects close with stale handle")
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

- defaults to main


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to main")
val sm = new_surface_manager()
expect sm.active() to_equal "main"
```

</details>

#### switches active to existing surface

- switches active to existing surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches active to existing surface")
var sm = new_surface_manager()
val root = text_widget("sm_active_root", "Active")
val tree = UITree.new(root)
sm.open("dialog", tree)
sm.set_active("dialog")
expect sm.active() to_equal "dialog"
```

</details>

#### does not switch to nonexistent surface

- does not switch to nonexistent surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not switch to nonexistent surface")
var sm = new_surface_manager()
sm.set_active("sm_active_ghost")
expect sm.active() to_equal "main"
```

</details>

### SurfaceManager surface_ids

#### returns all surface ids

- returns all surface ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all surface ids")
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
| Source | `test/unit/app/ui/surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SurfaceManager creation, SurfaceManager open, SurfaceManager get, SurfaceManager close, SurfaceManager handle validation, SurfaceManager active surface, SurfaceManager surface_ids.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0cb083d1a2c1494a3f76729fda1608554daa9e66fab1fbd4fd9ed137badda688`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0cb083d1a2c1494a3f76729fda1608554daa9e66fab1fbd4fd9ed137badda688`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0cb083d1a2c1494a3f76729fda1608554daa9e66fab1fbd4fd9ed137badda688`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/surface_spec.spl
mirror: doc/06_spec/unit/app/ui/surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/surface_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/surface_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a surface and increments count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/surface_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens multiple surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
