# Gc Safety Specification

> <details>

<!-- sdn-diagram:id=gc_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_safety_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Safety Specification

## Scenarios

### EscapeState

#### identifies non-escaping state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# EscapeState.NoEscape.escapes() == false
# EscapeState.NoEscape.can_stack_allocate() == true
pass
```

</details>

#### identifies escaping states

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# EscapeState.ArgEscape.escapes() == true
# EscapeState.ReturnEscape.escapes() == true
# EscapeState.GlobalEscape.escapes() == true
# EscapeState.FieldEscape.escapes() == true
pass
```

</details>

#### merges escape states correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NoEscape + NoEscape = NoEscape
# NoEscape + ArgEscape = ArgEscape
# ArgEscape + GlobalEscape = GlobalEscape
# Any + Unknown = Unknown
pass
```

</details>

#### converts to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# EscapeState.NoEscape.to_text() == "no_escape"
# EscapeState.GlobalEscape.to_text() == "global_escape"
pass
```

</details>

### AllocationSite

#### creates allocation site

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AllocationSite.create(0, 10, 100)
# site.id == 0
# site.program_point == 10
# site.type_id == 100
pass
```

</details>

#### starts with unknown escape state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# site.escape_state == EscapeState.Unknown
pass
```

</details>

#### formats allocation site

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# site.to_text() contains id and program point
pass
```

</details>

### PointsToSet

#### creates empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PointsToSet.empty().is_empty() == true
pass
```

</details>

#### creates singleton set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PointsToSet.singleton(5).contains(5) == true
pass
```

</details>

#### adds allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pts.add(1); pts.add(2)
# pts.contains(1) and pts.contains(2)
pass
```

</details>

#### unions sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pts1 = {1, 2}, pts2 = {2, 3}
# union = {1, 2, 3}
pass
```

</details>

#### avoids duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pts.add(1); pts.add(1)
# pts.all().len() == 1
pass
```

</details>

### EscapeAnalysis

#### records allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_allocation(point, type_id, local)
# returns allocation id
pass
```

</details>

#### records copies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_copy(from, to)
# to now points to same allocations as from
pass
```

</details>

#### marks field stores as escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_field_store(base, field, value, type)
# value allocations marked as FieldEscape
pass
```

</details>

#### marks call args as escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_call_arg(local)
# allocations in local marked as ArgEscape
pass
```

</details>

#### marks returns as escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_return(local)
# allocations marked as ReturnEscape
pass
```

</details>

#### marks global stores as escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_global_store(local)
# allocations marked as GlobalEscape
pass
```

</details>

#### finalizes unknown as non-escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After finalize(), Unknown becomes NoEscape
pass
```

</details>

#### computes stack allocation ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With 3 total, 2 non-escaping
# ratio == 0.666...
pass
```

</details>

#### gets non-escaping allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.get_non_escaping() returns only NoEscape sites
pass
```

</details>

#### gets escaping allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.get_escaping() returns all escaping sites
pass
```

</details>

### RootKind

#### creates local root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootKind.Local(5).to_text() == "local_5"
pass
```

</details>

#### creates parameter root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootKind.Parameter(0).to_text() == "param_0"
pass
```

</details>

#### creates global root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootKind.Global("counter").to_text() == "global_counter"
pass
```

</details>

#### creates temporary root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootKind.Temporary(3).to_text() == "temp_3"
pass
```

</details>

#### creates return root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootKind.Return.to_text() == "return"
pass
```

</details>

### GcRoot

#### creates local root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcRoot.local(5, 100)
# root.kind == RootKind.Local(5)
pass
```

</details>

#### creates parameter root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcRoot.parameter(0, 100)
# root.live_range == (0, i64.max())
pass
```

</details>

#### checks liveness at point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# root with live_range = (10, 20)
# root.is_live_at(15) == true
# root.is_live_at(5) == false
pass
```

</details>

#### formats root description

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# root.to_text() includes kind and type
pass
```

</details>

### RootSet

#### creates empty root set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RootSet.create().count() == 0
pass
```

</details>

#### adds roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# set.add_root(root)
# set.count() == 1
pass
```

</details>

#### removes roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# set.add_root(root); set.remove_root(root.kind)
# set.count() == 0
pass
```

</details>

#### gets root by kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# set.add_root(local_root)
# set.get_root(RootKind.Local(5)).? == true
pass
```

</details>

#### gets live roots at point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# set.live_roots_at(15) returns only roots live at 15
pass
```

</details>

### GcPoint

#### creates call gc point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcPoint.call(10)
# gc_point.kind == GcPointKind.Call
pass
```

</details>

#### creates allocation gc point

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcPoint.allocation(15)
# gc_point.kind == GcPointKind.Allocation
pass
```

</details>

#### formats gc point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gc_point.to_text() contains kind and point
pass
```

</details>

### RootAnalysis

#### records roots at program points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_root(10, root)
# analysis.get_roots_at(10) contains root
pass
```

</details>

#### records gc points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_gc_point(gc_point)
# analysis.get_gc_points() contains gc_point
pass
```

</details>

#### propagates roots between points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.propagate_roots(from, to)
# Live roots flow from source to destination
pass
```

</details>

#### verifies gc points have required roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.verify_gc_points()
# Returns true if all required roots present
pass
```

</details>

#### reports missing roots as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gc_point with required_roots that are missing
# analysis.get_errors() contains RootError
pass
```

</details>

### BarrierKind

#### identifies barrier types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BarrierKind.PreWrite.to_text() == "pre_write"
# BarrierKind.PostWrite.to_text() == "post_write"
pass
```

</details>

#### checks old value requirement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BarrierKind.PreWrite.requires_old_value() == true
# BarrierKind.PostWrite.requires_old_value() == false
pass
```

</details>

#### checks new value requirement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BarrierKind.PostWrite.requires_new_value() == true
# BarrierKind.PreWrite.requires_new_value() == false
pass
```

</details>

### WriteSite

#### creates field write site

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# WriteSite.field_write(10, 100, 0, 200)
# site.program_point == 10
# site.field_index == Some(0)
pass
```

</details>

#### creates array write site

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# WriteSite.array_write(15, 100, 200)
# site.is_array_element == true
pass
```

</details>

#### formats write site

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# site.to_text() contains write type and point
pass
```

</details>

### BarrierAnalysis

#### records write sites

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.record_write(site)
pass
```

</details>

#### requires no barriers for stop-the-world GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With GcStrategy.StopTheWorld
# No barriers required for any writes
pass
```

</details>

#### requires post-write for incremental GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With GcStrategy.Incremental
# Reference writes need PostWrite barrier
pass
```

</details>

#### requires generational barrier for old->young

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With GcStrategy.Generational
# Cross-generation writes need Generational barrier
pass
```

</details>

#### requires pre-write for concurrent GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With GcStrategy.Concurrent
# Reference writes need PreWrite barrier
pass
```

</details>

#### verifies emitted barriers match requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analysis.verify_barriers(emitted)
# Returns true if all required barriers present
pass
```

</details>

#### reports missing barriers as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Required barrier not emitted
# analysis.get_errors() contains BarrierError
pass
```

</details>

### GcSafetyConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcSafetyConfig.default_config()
# All analyses enabled, Incremental mode
pass
```

</details>

#### creates minimal config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcSafetyConfig.minimal()
# Only root tracking enabled, StopTheWorld mode
pass
```

</details>

#### creates generational config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcSafetyConfig.generational()
# All analyses enabled, Generational mode
pass
```

</details>

### GcSafetyAnalyzer

#### creates analyzer with config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GcSafetyAnalyzer.create(config)
pass
```

</details>

#### registers GC types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analyzer.register_gc_type(type_id)
# analyzer.is_gc_type(type_id) == true
pass
```

</details>

#### analyzes MIR function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# analyzer.analyze_function(mir_func)
# Returns GcSafetyReport
pass
```

</details>

#### processes allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Alloc instruction creates GC root
# Records as GC point
pass
```

</details>

#### processes calls as GC points

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Call instruction is a potential GC point
pass
```

</details>

#### processes field operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SetField triggers escape and barrier analysis
# GetField tracks pointer flow
pass
```

</details>

### GcSafetyReport

#### reports safety status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.is_safe() == true when no errors
pass
```

</details>

#### counts errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.error_count() == root_errors + barrier_errors
pass
```

</details>

#### formats summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.format_summary() includes all statistics
pass
```

</details>

#### includes gc points

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.gc_points lists all safepoints
pass
```

</details>

#### includes barrier requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.barrier_requirements lists all needed barriers
pass
```

</details>

#### reports allocation statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# report.total_allocations
# report.stack_eligible_allocations
# report.escape_ratio
pass
```

</details>

### GC Safety Integration

#### analyzes function with no GC types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function with only primitives
# No GC points, no barriers needed
pass
```

</details>

#### analyzes function with allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function allocates GC-managed objects
# Tracks roots at GC points
pass
```

</details>

#### analyzes function with field stores

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function stores references in fields
# Generates appropriate barriers
pass
```

</details>

#### identifies stack-eligible allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Non-escaping allocations can be stack-allocated
pass
```

</details>

#### identifies heap-required allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Escaping allocations must be heap-allocated
pass
```

</details>

### real-world GC patterns

#### handles linked list construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Building linked list - all nodes escape
pass
```

</details>

#### handles temporary allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Local-only allocations can be stack-allocated
pass
```

</details>

#### handles closure captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Captured variables may escape
pass
```

</details>

#### handles collection operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Items added to collections escape
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gc_safety_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- EscapeState
- AllocationSite
- PointsToSet
- EscapeAnalysis
- RootKind
- GcRoot
- RootSet
- GcPoint
- RootAnalysis
- BarrierKind
- WriteSite
- BarrierAnalysis
- GcSafetyConfig
- GcSafetyAnalyzer
- GcSafetyReport
- GC Safety Integration
- real-world GC patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
