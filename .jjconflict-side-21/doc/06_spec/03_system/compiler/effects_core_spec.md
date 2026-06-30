# Effects Core Specification

> <details>

<!-- sdn-diagram:id=effects_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effects_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effects_core_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effects_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effects Core Specification

## Scenarios

### AsyncEffect - is_async predicate

#### Compute is async

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Compute
val result = e.is_async()
expect(result).to_equal(true)
```

</details>

#### Io is async

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Io
val result = e.is_async()
expect(result).to_equal(true)
```

</details>

#### Wait is not async

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Wait
val result = e.is_async()
expect(result).to_equal(false)
```

</details>

### AsyncEffect - pipeline_safe predicate

#### empty list is pipeline safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = []
val safe = pipeline_safe(effects)
expect(safe).to_equal(true)
```

</details>

#### list with only Compute is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Compute]
val safe = pipeline_safe(effects)
expect(safe).to_equal(true)
```

</details>

#### list with Compute and Io is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Io, AsyncEffect.Compute]
val safe = pipeline_safe(effects)
expect(safe).to_equal(true)
```

</details>

#### list with Wait is not safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Wait, AsyncEffect.Io]
val safe = pipeline_safe(effects)
expect(safe).to_equal(false)
```

</details>

#### singleton Wait list is not safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Wait]
val safe = pipeline_safe(effects)
expect(safe).to_equal(false)
```

</details>

### AsyncEffect - append_safe theorem

#### append two safe lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [AsyncEffect.Compute, AsyncEffect.Io]
val b = [AsyncEffect.Compute, AsyncEffect.Compute]
val result = append_safe(a, b)
expect(pipeline_safe(result)).to_equal(true)
expect(result.length()).to_equal(4)
```

</details>

#### append preserves order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [AsyncEffect.Compute]
val b = [AsyncEffect.Io]
val result = append_safe(a, b)
expect(result[0] == AsyncEffect.Compute).to_equal(true)
expect(result[1] == AsyncEffect.Io).to_equal(true)
```

</details>

#### append empty lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = []
val b = []
val result = append_safe(a, b)
expect(result.length()).to_equal(0)
expect(pipeline_safe(result)).to_equal(true)
```

</details>

### AsyncEffect - wait_detected theorem

#### wait detected in unsafe singleton

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Wait
val result = wait_detected(e)
expect(result).to_equal(true)
```

</details>

#### no wait in safe Compute singleton

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Compute
val result = wait_detected(e)
expect(result).to_equal(true)
```

</details>

#### no wait in safe Io singleton

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = AsyncEffect.Io
val result = wait_detected(e)
expect(result).to_equal(true)
```

</details>

### AsyncEffect - blocking detection

#### no blocking in pure compute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Compute]
val has_blocking = has_blocking_effects(effects)
expect(has_blocking).to_equal(false)
```

</details>

#### blocking detected with Wait

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Wait]
val has_blocking = has_blocking_effects(effects)
expect(has_blocking).to_equal(true)
```

</details>

#### count blocking effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Wait, AsyncEffect.Compute, AsyncEffect.Wait, AsyncEffect.Io]
val count = count_blocking(effects)
expect(count).to_equal(2)
```

</details>

#### filter async effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Wait, AsyncEffect.Compute, AsyncEffect.Wait, AsyncEffect.Io]
val filtered = filter_async(effects)
expect(filtered.length()).to_equal(2)
expect(pipeline_safe(filtered)).to_equal(true)
```

</details>

### NogcInstr - predicate methods

#### GcAlloc is GC allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.GcAlloc
val is_gc = instr.is_gc_alloc()
expect(is_gc).to_equal(true)
```

</details>

#### Const is not GC allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.Const(42)
val is_gc = instr.is_gc_alloc()
expect(is_gc).to_equal(false)
```

</details>

#### Add is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.Add
val is_nogc = instr.is_nogc()
expect(is_nogc).to_equal(true)
```

</details>

### NogcInstr - nogc predicate

#### empty list is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = []
val result = nogc(instrs)
expect(result).to_equal(true)
```

</details>

#### list with only Const and Add is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.Const(1), NogcInstr.Add, NogcInstr.Const(2)]
val result = nogc(instrs)
expect(result).to_equal(true)
```

</details>

#### list with GcAlloc is not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.Const(1), NogcInstr.GcAlloc, NogcInstr.Add]
val result = nogc(instrs)
expect(result).to_equal(false)
```

</details>

### NogcInstr - nogc_append theorem

#### append two nogc lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [NogcInstr.Const(1), NogcInstr.Add]
val b = [NogcInstr.Const(2), NogcInstr.Add]
val result = nogc_append(a, b)
expect(nogc(result)).to_equal(true)
expect(result.length()).to_equal(4)
```

</details>

#### append preserves instruction order

1. NogcInstr Const
   - Expected: first_const_value equals `1`
   - Expected: result[1] == NogcInstr.Add is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [NogcInstr.Const(1)]
val b = [NogcInstr.Add]
val result = nogc_append(a, b)
var first_const_value = -1
match result[0]:
    NogcInstr.Const(n):
        first_const_value = n
    _:
        first_const_value = -2
expect(first_const_value).to_equal(1)
expect(result[1] == NogcInstr.Add).to_equal(true)
```

</details>

### NogcInstr - nogc_singleton theorem

#### singleton Const is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.Const(42)
val result = nogc_singleton(instr)
expect(result).to_equal(true)
```

</details>

#### singleton Add is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.Add
val result = nogc_singleton(instr)
expect(result).to_equal(true)
```

</details>

#### singleton GcAlloc is not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = NogcInstr.GcAlloc
val result = nogc_singleton(instr)
expect(result).to_equal(false)
```

</details>

### NogcInstr - GC allocation tracking

#### count GC allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.GcAlloc, NogcInstr.Const(1), NogcInstr.GcAlloc, NogcInstr.Add]
val count = count_gc_allocs(instrs)
expect(count).to_equal(2)
```

</details>

#### filter nogc instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.GcAlloc, NogcInstr.Const(1), NogcInstr.GcAlloc, NogcInstr.Add]
val filtered = filter_nogc(instrs)
expect(filtered.length()).to_equal(2)
expect(nogc(filtered)).to_equal(true)
```

</details>

### Combined Effect Properties

#### create properties from async effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Compute, AsyncEffect.Io]
val props = EffectProperties.from_async(effects)
expect(props.is_pipeline_safe).to_equal(true)
expect(props.blocking_count).to_equal(0)
```

</details>

#### create properties from async with blocking

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effects = [AsyncEffect.Wait, AsyncEffect.Compute]
val props = EffectProperties.from_async(effects)
expect(props.is_pipeline_safe).to_equal(false)
expect(props.blocking_count).to_equal(1)
```

</details>

#### create properties from nogc instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.Const(1), NogcInstr.Add]
val props = EffectProperties.from_nogc(instrs)
expect(props.is_nogc).to_equal(true)
expect(props.gc_alloc_count).to_equal(0)
```

</details>

#### create properties from instructions with GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrs = [NogcInstr.GcAlloc, NogcInstr.Const(1)]
val props = EffectProperties.from_nogc(instrs)
expect(props.is_nogc).to_equal(false)
expect(props.gc_alloc_count).to_equal(1)
```

</details>

#### check optimizability

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = EffectProperties(
    is_pipeline_safe: true,
    is_nogc: true,
    blocking_count: 0,
    gc_alloc_count: 0
)
val opt = props.is_optimizable()
expect(opt).to_equal(true)
```

</details>

#### not optimizable with blocking

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = EffectProperties(
    is_pipeline_safe: false,
    is_nogc: true,
    blocking_count: 1,
    gc_alloc_count: 0
)
val opt = props.is_optimizable()
expect(opt).to_equal(false)
```

</details>

#### calculate effect severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = EffectProperties(
    is_pipeline_safe: false,
    is_nogc: false,
    blocking_count: 2,
    gc_alloc_count: 3
)
val sev = props.severity()
expect(sev).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/effects_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AsyncEffect - is_async predicate
- AsyncEffect - pipeline_safe predicate
- AsyncEffect - append_safe theorem
- AsyncEffect - wait_detected theorem
- AsyncEffect - blocking detection
- NogcInstr - predicate methods
- NogcInstr - nogc predicate
- NogcInstr - nogc_append theorem
- NogcInstr - nogc_singleton theorem
- NogcInstr - GC allocation tracking
- Combined Effect Properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
