# Gc Safety Specification

> Tests covering EscapeState, AllocationSite, PointsToSet, EscapeAnalysis, EscapeState lattice, PointsToSet operations, EscapeAnalysis pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Safety Specification

## Scenarios

### EscapeState

#### distinguishes every escape variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.NoEscape == EscapeState.NoEscape).to_equal(true)
expect(EscapeState.NoEscape == EscapeState.ArgEscape).to_equal(false)
expect(EscapeState.ArgEscape == EscapeState.ReturnEscape).to_equal(false)
expect(EscapeState.ReturnEscape == EscapeState.GlobalEscape).to_equal(false)
expect(EscapeState.GlobalEscape == EscapeState.FieldEscape).to_equal(false)
expect(EscapeState.FieldEscape == EscapeState.Unknown).to_equal(false)
```

</details>

#### treats Unknown as distinct from every concrete state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.Unknown == EscapeState.NoEscape).to_equal(false)
expect(EscapeState.Unknown == EscapeState.ArgEscape).to_equal(false)
expect(EscapeState.Unknown == EscapeState.ReturnEscape).to_equal(false)
expect(EscapeState.Unknown == EscapeState.GlobalEscape).to_equal(false)
expect(EscapeState.Unknown == EscapeState.FieldEscape).to_equal(false)
expect(EscapeState.Unknown == EscapeState.Unknown).to_equal(true)
```

</details>

### AllocationSite

#### records the id, program point and type it was created with

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val site = allocationsite_create(7, 11, 13)
expect(site.id).to_equal(7)
expect(site.program_point).to_equal(11)
expect(site.type_id).to_equal(13)
```

</details>

#### starts in the Unknown escape state before analysis runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val site = allocationsite_create(1, 2, 3)
expect(site.escape_state == EscapeState.Unknown).to_equal(true)
expect(site.escape_state == EscapeState.NoEscape).to_equal(false)
```

</details>

#### keeps distinct ids for distinct allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = allocationsite_create(0, 100, 5)
val b = allocationsite_create(1, 100, 5)
expect(a.id == b.id).to_equal(false)
expect(a.program_point).to_equal(b.program_point)
expect(a.type_id).to_equal(b.type_id)
```

</details>

### PointsToSet

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = PointsToSet.empty()
expect(empty.allocations.len()).to_equal(0)
```

</details>

#### holds exactly the allocation it was seeded with

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one = PointsToSet.singleton(4)
expect(one.allocations.len()).to_equal(1)
expect(one.allocations[0]).to_equal(4)
```

</details>

#### keeps singletons independent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PointsToSet.singleton(4)
val b = PointsToSet.singleton(9)
expect(a.allocations[0]).to_equal(4)
expect(b.allocations[0]).to_equal(9)
expect(a.allocations[0] == b.allocations[0]).to_equal(false)
```

</details>

### EscapeAnalysis

#### starts with no allocations and no stack-eligible sites

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val analysis = EscapeAnalysis.create()
expect(analysis.next_alloc_id).to_equal(0)
expect(analysis.total_allocations).to_equal(0)
expect(analysis.stack_eligible).to_equal(0)
```

</details>

#### hands out allocation ids starting from zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val analysis = EscapeAnalysis.create()
expect(analysis.next_alloc_id).to_equal(0)
```

</details>

### EscapeState lattice

#### treats only NoEscape as non-escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.NoEscape.escapes()).to_equal(false)
expect(EscapeState.ArgEscape.escapes()).to_equal(true)
expect(EscapeState.ReturnEscape.escapes()).to_equal(true)
expect(EscapeState.GlobalEscape.escapes()).to_equal(true)
expect(EscapeState.FieldEscape.escapes()).to_equal(true)
```

</details>

#### treats Unknown as escaping, because it is unproven

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.Unknown.escapes()).to_equal(true)
expect(EscapeState.Unknown.can_stack_allocate()).to_equal(false)
```

</details>

#### allows stack allocation only for NoEscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.NoEscape.can_stack_allocate()).to_equal(true)
expect(EscapeState.ArgEscape.can_stack_allocate()).to_equal(false)
expect(EscapeState.GlobalEscape.can_stack_allocate()).to_equal(false)
```

</details>

#### joins Unknown with any concrete state to give that state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.Unknown.merge_with(EscapeState.NoEscape) == EscapeState.NoEscape).to_equal(true)
expect(EscapeState.Unknown.merge_with(EscapeState.ArgEscape) == EscapeState.ArgEscape).to_equal(true)
expect(EscapeState.Unknown.merge_with(EscapeState.GlobalEscape) == EscapeState.GlobalEscape).to_equal(true)
```

</details>

#### keeps the more escaping side when joining two concrete states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.NoEscape.merge_with(EscapeState.ArgEscape) == EscapeState.ArgEscape).to_equal(true)
expect(EscapeState.GlobalEscape.merge_with(EscapeState.ArgEscape) == EscapeState.GlobalEscape).to_equal(true)
expect(EscapeState.ArgEscape.merge_with(EscapeState.ReturnEscape) == EscapeState.ReturnEscape).to_equal(true)
```

</details>

#### is commutative and idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.ArgEscape.merge_with(EscapeState.FieldEscape) == EscapeState.FieldEscape.merge_with(EscapeState.ArgEscape)).to_equal(true)
expect(EscapeState.ArgEscape.merge_with(EscapeState.ArgEscape) == EscapeState.ArgEscape).to_equal(true)
```

</details>

#### names every state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EscapeState.NoEscape.to_text()).to_equal("NoEscape")
expect(EscapeState.ArgEscape.to_text()).to_equal("ArgEscape")
expect(EscapeState.ReturnEscape.to_text()).to_equal("ReturnEscape")
expect(EscapeState.GlobalEscape.to_text()).to_equal("GlobalEscape")
expect(EscapeState.FieldEscape.to_text()).to_equal("FieldEscape")
expect(EscapeState.Unknown.to_text()).to_equal("Unknown")
```

</details>

### PointsToSet operations

#### adds allocations without duplicating them

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pts = PointsToSet.empty()
pts.add(3)
pts.add(3)
pts.add(5)
expect(pts.allocations.len()).to_equal(2)
expect(pts.contains(3)).to_equal(true)
expect(pts.contains(5)).to_equal(true)
expect(pts.contains(9)).to_equal(false)
```

</details>

#### reports emptiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pts = PointsToSet.empty()
expect(pts.is_empty()).to_equal(true)
pts.add(1)
expect(pts.is_empty()).to_equal(false)
```

</details>

#### unions two sets without duplicating shared members

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = PointsToSet.empty()
a.add(1)
a.add(2)
var b = PointsToSet.empty()
b.add(2)
b.add(3)
val u = a.union(b)
expect(u.allocations.len()).to_equal(3)
expect(u.contains(1)).to_equal(true)
expect(u.contains(2)).to_equal(true)
expect(u.contains(3)).to_equal(true)
```

</details>

#### exposes all members

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = PointsToSet.empty()
a.add(8)
expect(a.all().len()).to_equal(1)
expect(a.all()[0]).to_equal(8)
```

</details>

### EscapeAnalysis pipeline

#### records allocations and hands out increasing ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 10)
val b = ea.record_allocation(2, 101, 10)
expect(a).to_equal(0)
expect(b).to_equal(1)
expect(ea.total_allocations).to_equal(2)
```

</details>

#### retains an untouched allocation as Unknown after finalize

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 10)
expect(ea.get_escape_state(a) == EscapeState.Unknown).to_equal(true)
ea.finalize()
expect(ea.get_escape_state(a) == EscapeState.Unknown).to_equal(true)
expect(ea.can_stack_allocate(a)).to_equal(false)
```

</details>

#### marks a returned local as ReturnEscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 20)
ea.record_return(20)
expect(ea.get_escape_state(a) == EscapeState.ReturnEscape).to_equal(true)
expect(ea.can_stack_allocate(a)).to_equal(false)
```

</details>

#### marks a local passed as a call argument as ArgEscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 21)
ea.record_call_arg(21)
expect(ea.get_escape_state(a) == EscapeState.ArgEscape).to_equal(true)
```

</details>

#### marks a local stored to a global as GlobalEscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 22)
ea.record_global_store(22)
expect(ea.get_escape_state(a) == EscapeState.GlobalEscape).to_equal(true)
```

</details>

#### propagates points-to through a copy so the copy escapes too

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 30)
ea.record_copy(30, 31)
ea.record_return(31)
expect(ea.get_escape_state(a) == EscapeState.ReturnEscape).to_equal(true)
```

</details>

#### marks a value stored into a field as FieldEscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 40)
ea.record_field_store(41, 0, 40, 7)
expect(ea.get_escape_state(a) == EscapeState.FieldEscape).to_equal(true)
```

</details>

#### recovers a field-stored allocation through a matching field load

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The store already pins the value at FieldEscape, so the load is proved
# to have propagated the points-to set by escalating to GlobalEscape,
# which strictly dominates FieldEscape in the lattice.
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 40)
ea.record_field_store(41, 0, 40, 7)
expect(ea.get_escape_state(a) == EscapeState.FieldEscape).to_equal(true)
ea.record_field_load(41, 0, 50, 7)
ea.record_global_store(50)
expect(ea.get_escape_state(a) == EscapeState.GlobalEscape).to_equal(true)
```

</details>

#### does not recover a field-stored allocation through a different field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 40)
ea.record_field_store(41, 0, 40, 7)
ea.record_field_load(41, 1, 50, 7)
ea.record_global_store(50)
expect(ea.get_escape_state(a) == EscapeState.FieldEscape).to_equal(true)
```

</details>

#### keeps the most escaping state when a local escapes twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 60)
ea.record_call_arg(60)
ea.record_global_store(60)
expect(ea.get_escape_state(a) == EscapeState.GlobalEscape).to_equal(true)
```

</details>

#### reports Unknown for an allocation id that was never recorded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ea = EscapeAnalysis.create()
expect(ea.get_escape_state(999) == EscapeState.Unknown).to_equal(true)
```

</details>

#### keeps unknown and returned allocations in the escaping partition

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 70)
val b = ea.record_allocation(2, 101, 71)
ea.record_return(71)
ea.finalize()
expect(ea.get_non_escaping().len()).to_equal(0)
val escaping = ea.get_escaping()
expect(escaping.len()).to_equal(2)
var found_unknown = false
var found_returned = false
for site in escaping:
    if site.id == a: found_unknown = true
    if site.id == b: found_returned = true
expect(found_unknown).to_equal(true)
expect(found_returned).to_equal(true)
```

</details>

#### does not count unproven locality as stack eligible

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
val a = ea.record_allocation(1, 100, 80)
val b = ea.record_allocation(2, 101, 81)
ea.record_return(81)
ea.finalize()
expect(ea.stack_eligible).to_equal(0)
expect(ea.total_allocations).to_equal(2)
expect(ea.stack_allocation_ratio()).to_equal(0.0)
```

</details>

#### reports a zero ratio when nothing was allocated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ea = EscapeAnalysis.create()
ea.finalize()
expect(ea.stack_allocation_ratio()).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gc_safety_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering EscapeState, AllocationSite, PointsToSet, EscapeAnalysis, EscapeState lattice, PointsToSet operations, EscapeAnalysis pipeline.
- EscapeState
- AllocationSite
- PointsToSet
- EscapeAnalysis
- EscapeState lattice
- PointsToSet operations
- EscapeAnalysis pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
