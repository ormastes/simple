# Profiler Specification

> <details>

<!-- sdn-diagram:id=profiler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=profiler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

profiler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=profiler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Profiler Specification

## Scenarios

### ProfileSample

#### computes duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ProfileSample(name: "test", start_ms: 10.0, end_ms: 25.0, depth: 0)
expect(s.duration_ms()).to_equal(15.0)
```

</details>

### Profiler

#### starts enabled with zero samples

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Profiler.new(100)
expect(p.is_enabled()).to_equal(true)
expect(p.sample_count()).to_equal(0)
expect(p.get_frame_count()).to_equal(0)
```

</details>

#### records a scope

1. var p = Profiler new
2. p begin scope
3. p end scope
   - Expected: p.sample_count() equals `1`
   - Expected: samples[0].name equals `update`
   - Expected: samples[0].start_ms equals `0.0`
   - Expected: samples[0].end_ms equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.begin_scope("update", 0.0)
p.end_scope(16.0)
expect(p.sample_count()).to_equal(1)
val samples = p.get_samples()
expect(samples[0].name).to_equal("update")
expect(samples[0].start_ms).to_equal(0.0)
expect(samples[0].end_ms).to_equal(16.0)
```

</details>

#### tracks nesting depth

1. var p = Profiler new
2. p begin scope
3. p begin scope
4. p end scope
5. p end scope
   - Expected: samples[0].depth equals `0`
   - Expected: samples[1].depth equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.begin_scope("frame", 0.0)
p.begin_scope("physics", 1.0)
p.end_scope(5.0)
p.end_scope(16.0)
val samples = p.get_samples()
expect(samples[0].depth).to_equal(0)
expect(samples[1].depth).to_equal(1)
```

</details>

#### increments frame count

1. var p = Profiler new
2. p begin frame
3. p begin frame
4. p begin frame
   - Expected: p.get_frame_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.begin_frame()
p.begin_frame()
p.begin_frame()
expect(p.get_frame_count()).to_equal(3)
```

</details>

#### does not record when disabled

1. var p = Profiler new
2. p set enabled
   - Expected: p.is_enabled() is false
3. p begin scope
   - Expected: p.sample_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.set_enabled(false)
expect(p.is_enabled()).to_equal(false)
p.begin_scope("ignored", 0.0)
expect(p.sample_count()).to_equal(0)
```

</details>

#### trims to max_samples

1. var p = Profiler new
2. p begin scope
3. p end scope
4. p begin scope
5. p end scope
6. p begin scope
7. p end scope
   - Expected: p.sample_count() equals `2`
   - Expected: samples[0].name equals `b`
   - Expected: samples[1].name equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(2)
p.begin_scope("a", 0.0)
p.end_scope(1.0)
p.begin_scope("b", 1.0)
p.end_scope(2.0)
p.begin_scope("c", 2.0)
p.end_scope(3.0)
expect(p.sample_count()).to_equal(2)
val samples = p.get_samples()
expect(samples[0].name).to_equal("b")
expect(samples[1].name).to_equal("c")
```

</details>

#### finds samples by name

1. var p = Profiler new
2. p begin scope
3. p end scope
4. p begin scope
5. p end scope
6. p begin scope
7. p end scope
   - Expected: renders.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.begin_scope("render", 0.0)
p.end_scope(5.0)
p.begin_scope("physics", 5.0)
p.end_scope(8.0)
p.begin_scope("render", 8.0)
p.end_scope(14.0)
val renders = p.find_samples_by_name("render")
expect(renders.len()).to_equal(2)
```

</details>

#### clears all state

1. var p = Profiler new
2. p begin frame
3. p begin scope
4. p end scope
5. p clear
   - Expected: p.sample_count() equals `0`
   - Expected: p.get_frame_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Profiler.new(100)
p.begin_frame()
p.begin_scope("test", 0.0)
p.end_scope(1.0)
p.clear()
expect(p.sample_count()).to_equal(0)
expect(p.get_frame_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/profiler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ProfileSample
- Profiler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
